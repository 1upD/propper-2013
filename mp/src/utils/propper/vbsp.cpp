//========= Copyright Valve Corporation, All rights reserved. ============//
//
// Purpose: BSP Building tool
//
// $NoKeywords: $
//=============================================================================//

#include "vbsp.h"
#include "detail.h"
#include "physdll.h"
#include "utilmatlib.h"
#include "disp_vbsp.h"
#include "writebsp.h"
#include "tier0/icommandline.h"
#include "materialsystem/imaterialsystem.h"
#include "map.h"
#include "tools_minidump.h"
#include "materialsub.h"
#include "loadcmdline.h"
#include "byteswap.h"
#include "worldvertextransitionfixup.h"

//Carl
#include "utlbuffer.h"
#include <windows.h>

#include <io.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/stat.h>
#include <limits.h>

#include <tchar.h>
#include "builddisp.h"
//Carl end

extern float		g_maxLightmapDimension;

char		source[1024];
char		mapbase[ 64 ];
char		name[1024];
char		materialPath[1024];

vec_t		microvolume = 1.0;
qboolean	noprune;
qboolean	glview;
qboolean	nodetail;
qboolean	fulldetail;
qboolean	onlyents;
bool		onlyprops;
qboolean	nomerge;
qboolean	nomergewater = false;
qboolean	nowater;
qboolean	nocsg;
qboolean	noweld;
qboolean	noshare;
qboolean	nosubdiv;
qboolean	notjunc;
qboolean	noopt;
qboolean	leaktest;
qboolean	verboseentities;
qboolean	dumpcollide = false;
qboolean	g_bLowPriority = false;
qboolean	g_DumpStaticProps = false;
qboolean	g_bSkyVis = false;			// skybox vis is off by default, toggle this to enable it
bool		g_bLightIfMissing = false;
bool		g_snapAxialPlanes = false;
bool		g_bKeepStaleZip = false;
bool		g_NodrawTriggers = false;
bool		g_DisableWaterLighting = false;
bool		g_bAllowDetailCracks = false;
bool		g_bNoVirtualMesh = false;

float		g_defaultLuxelSize = DEFAULT_LUXEL_SIZE;
float		g_luxelScale = 1.0f;
float		g_minLuxelScale = 1.0f;
bool		g_BumpAll = false;

int			g_nDXLevel = 0; // default dxlevel if you don't specify it on the command-line.
CUtlVector<int> g_SkyAreas;
char		outbase[32];

//Carl
int numverts = 0;
bool logging = false;

char *sourcefolder;
bool dobodygroup = false;

bool objExport = false;
bool studioCompile = true;
bool fixMaterials = true;
bool mat_nonormal = false;
int smdmaterials = 0;

//This gets initialized twice. Hrm...
char targetPath[1024];

model_t propper_models[MAX_PROPPER_MODELS];
int num_models = 0;

smd_triangle_t smd_tris[MAX_SMD_TRIS];
smd_point_t smd_pts[MAX_SMD_VERTS+1];

bodygroups_t bodygroups;

char FixdTextures[1048576];

smd_texture_t* smd_textures;
//Carl end

// HLTOOLS: Introduce these calcs to make the block algorithm proportional to the proper 
// world coordinate extents.  Assumes square spatial constraints.
#define BLOCKS_SIZE		1024
#define BLOCKS_SPACE	(COORD_EXTENT/BLOCKS_SIZE)
#define BLOCKX_OFFSET	((BLOCKS_SPACE/2)+1)
#define BLOCKY_OFFSET	((BLOCKS_SPACE/2)+1)
#define BLOCKS_MIN		(-(BLOCKS_SPACE/2))
#define BLOCKS_MAX		((BLOCKS_SPACE/2)-1)

int			block_xl = BLOCKS_MIN, block_xh = BLOCKS_MAX, block_yl = BLOCKS_MIN, block_yh = BLOCKS_MAX;

int			entity_num;


node_t		*block_nodes[BLOCKS_SPACE+2][BLOCKS_SPACE+2];

//-----------------------------------------------------------------------------
// Assign occluder areas (must happen *after* the world model is processed)
//-----------------------------------------------------------------------------
void AssignOccluderAreas( tree_t *pTree );
static void Compute3DSkyboxAreas( node_t *headnode, CUtlVector<int>& areas );


/*
============
BlockTree

============
*/
node_t	*BlockTree (int xl, int yl, int xh, int yh)
{
	node_t	*node;
	Vector	normal;
	float	dist;
	int		mid;

	if (xl == xh && yl == yh)
	{
		node = block_nodes[xl+BLOCKX_OFFSET][yl+BLOCKY_OFFSET];
		if (!node)
		{	// return an empty leaf
			node = AllocNode ();
			node->planenum = PLANENUM_LEAF;
			node->contents = 0; //CONTENTS_SOLID;
			return node;
		}
		return node;
	}

	// create a seperator along the largest axis
	node = AllocNode ();

	if (xh - xl > yh - yl)
	{	// split x axis
		mid = xl + (xh-xl)/2 + 1;
		normal[0] = 1;
		normal[1] = 0;
		normal[2] = 0;
		dist = mid*BLOCKS_SIZE;
		node->planenum = g_MainMap->FindFloatPlane (normal, dist);
		node->children[0] = BlockTree ( mid, yl, xh, yh);
		node->children[1] = BlockTree ( xl, yl, mid-1, yh);
	}
	else
	{
		mid = yl + (yh-yl)/2 + 1;
		normal[0] = 0;
		normal[1] = 1;
		normal[2] = 0;
		dist = mid*BLOCKS_SIZE;
		node->planenum = g_MainMap->FindFloatPlane (normal, dist);
		node->children[0] = BlockTree ( xl, mid, xh, yh);
		node->children[1] = BlockTree ( xl, yl, xh, mid-1);
	}

	return node;
}

/*
============
ProcessBlock_Thread

============
*/
int			brush_start, brush_end;
void ProcessBlock_Thread (int threadnum, int blocknum)
{
	int		xblock, yblock;
	Vector		mins, maxs;
	bspbrush_t	*brushes;
	tree_t		*tree;
	node_t		*node;

	yblock = block_yl + blocknum / (block_xh-block_xl+1);
	xblock = block_xl + blocknum % (block_xh-block_xl+1);

	qprintf ("############### block %2i,%2i ###############\n", xblock, yblock);

	mins[0] = xblock*BLOCKS_SIZE;
	mins[1] = yblock*BLOCKS_SIZE;
	mins[2] = MIN_COORD_INTEGER;
	maxs[0] = (xblock+1)*BLOCKS_SIZE;
	maxs[1] = (yblock+1)*BLOCKS_SIZE;
	maxs[2] = MAX_COORD_INTEGER;

	// the makelist and chopbrushes could be cached between the passes...
	brushes = MakeBspBrushList (brush_start, brush_end, mins, maxs, NO_DETAIL);
	if (!brushes)
	{
		node = AllocNode ();
		node->planenum = PLANENUM_LEAF;
		node->contents = CONTENTS_SOLID;
		block_nodes[xblock+BLOCKX_OFFSET][yblock+BLOCKY_OFFSET] = node;
		return;
	}    

	FixupAreaportalWaterBrushes( brushes );
	if (!nocsg)
		brushes = ChopBrushes (brushes);

	tree = BrushBSP (brushes, mins, maxs);
	
	block_nodes[xblock+BLOCKX_OFFSET][yblock+BLOCKY_OFFSET] = tree->headnode;
}


/*
============
ProcessWorldModel

============
*/
void SplitSubdividedFaces( node_t *headnode ); // garymcthack
void ProcessWorldModel (void)
{
	entity_t	*e;
	tree_t		*tree = NULL;
	qboolean	leaked;
	int	optimize;
	int			start;

	e = &entities[entity_num];

	brush_start = e->firstbrush;
	brush_end = brush_start + e->numbrushes;
	leaked = false;

	//
	// perform per-block operations
	//
	if (block_xh * BLOCKS_SIZE > g_MainMap->map_maxs[0])
	{
		block_xh = floor(g_MainMap->map_maxs[0]/BLOCKS_SIZE);
	}
	if ( (block_xl+1) * BLOCKS_SIZE < g_MainMap->map_mins[0])
	{
		block_xl = floor(g_MainMap->map_mins[0]/BLOCKS_SIZE);
	}
	if (block_yh * BLOCKS_SIZE > g_MainMap->map_maxs[1])
	{
		block_yh = floor(g_MainMap->map_maxs[1]/BLOCKS_SIZE);
	}
	if ( (block_yl+1) * BLOCKS_SIZE < g_MainMap->map_mins[1])
	{
		block_yl = floor(g_MainMap->map_mins[1]/BLOCKS_SIZE);
	}

	// HLTOOLS: updated to +/- MAX_COORD_INTEGER ( new world size limits / worldsize.h )
	if (block_xl < BLOCKS_MIN)
	{
		block_xl = BLOCKS_MIN;
	}
	if (block_yl < BLOCKS_MIN)
	{
		block_yl = BLOCKS_MIN;
	}
	if (block_xh > BLOCKS_MAX)
	{
		block_xh = BLOCKS_MAX;
	}
	if (block_yh > BLOCKS_MAX)
	{
		block_yh = BLOCKS_MAX;
	}

	for (optimize = 0 ; optimize <= 1 ; optimize++)
	{
		qprintf ("--------------------------------------------\n");

		RunThreadsOnIndividual ((block_xh-block_xl+1)*(block_yh-block_yl+1),
			!verbose, ProcessBlock_Thread);

		//
		// build the division tree
		// oversizing the blocks guarantees that all the boundaries
		// will also get nodes.
		//

		qprintf ("--------------------------------------------\n");

		tree = AllocTree ();
		tree->headnode = BlockTree (block_xl-1, block_yl-1, block_xh+1, block_yh+1);

		tree->mins[0] = (block_xl)*BLOCKS_SIZE;
		tree->mins[1] = (block_yl)*BLOCKS_SIZE;
		tree->mins[2] = g_MainMap->map_mins[2] - 8;

		tree->maxs[0] = (block_xh+1)*BLOCKS_SIZE;
		tree->maxs[1] = (block_yh+1)*BLOCKS_SIZE;
		tree->maxs[2] = g_MainMap->map_maxs[2] + 8;

		//
		// perform the global operations
		//

		// make the portals/faces by traversing down to each empty leaf
		/*MakeTreePortals (tree);

		if (FloodEntities (tree))
		{
			// turns everthing outside into solid
			FillOutside (tree->headnode);
		}
		else
		{
			Warning( ("**** leaked ****\n") );
			leaked = true;
			LeakFile (tree);
			if (leaktest)
			{
				Warning( ("--- MAP LEAKED ---\n") );
				exit (0);
			}
		}
		*/

		// mark the brush sides that actually turned into faces
		MarkVisibleSides (tree, brush_start, brush_end, NO_DETAIL);
		if (noopt || leaked)
			break;
		if (!optimize)
		{
			// If we are optimizing, free the tree.  Next time we will construct it again, but
			// we'll use the information in MarkVisibleSides() so we'll only split with planes that
			// actually contribute renderable geometry
			FreeTree (tree);
		}
	}

	//FloodAreas (tree);

	RemoveAreaPortalBrushes_R( tree->headnode );

	start = Plat_FloatTime();
	//Msg("Building Faces...");
	// this turns portals with one solid side into faces
	// it also subdivides each face if necessary to fit max lightmap dimensions
	//MakeFaces (tree->headnode);
	//Msg("done (%d)\n", (int)(Plat_FloatTime() - start) );

	if (0)
	{
		WriteGLView (tree, source);
	}

	//AssignOccluderAreas( tree );
	Compute3DSkyboxAreas( tree->headnode, g_SkyAreas );
	face_t *pLeafFaceList = NULL;
	if ( !nodetail )
	{
		pLeafFaceList = MergeDetailTree( tree, brush_start, brush_end );
	}

	start = Plat_FloatTime();

	//Msg("FixTjuncs...\n");
	
	// This unifies the vertex list for all edges (splits collinear edges to remove t-junctions)
	// It also welds the list of vertices out of each winding/portal and rounds nearly integer verts to integer
	pLeafFaceList = FixTjuncs (tree->headnode, pLeafFaceList);

	// this merges all of the solid nodes that have separating planes
	if (!noprune)
	{
		//Msg("PruneNodes...\n");
		PruneNodes (tree->headnode);
	}

//	Msg( "SplitSubdividedFaces...\n" );
//	SplitSubdividedFaces( tree->headnode );

//	Msg("WriteBSP...\n");
	WriteBSP (tree->headnode, pLeafFaceList);
//	Msg("done (%d)\n", (int)(Plat_FloatTime() - start) );

//	if (!leaked)
//	{
//		WritePortalFile (tree);
//	}

	FreeTree( tree );
	FreeLeafFaces( pLeafFaceList );
}

/*
============
ProcessSubModel

============
*/
void ProcessSubModel( )
{
	entity_t	*e;
	int			start, end;
	tree_t		*tree;
	bspbrush_t	*list;
	Vector		mins, maxs;

	e = &entities[entity_num];

	start = e->firstbrush;
	end = start + e->numbrushes;

	mins[0] = mins[1] = mins[2] = MIN_COORD_INTEGER;
	maxs[0] = maxs[1] = maxs[2] = MAX_COORD_INTEGER;
	list = MakeBspBrushList (start, end, mins, maxs, FULL_DETAIL);

	if (!nocsg)
		list = ChopBrushes (list);
	tree = BrushBSP (list, mins, maxs);
	
	// This would wind up crashing the engine because we'd have a negative leaf index in dmodel_t::headnode.
	if ( tree->headnode->planenum == PLANENUM_LEAF )
	{
		const char *pClassName = ValueForKey( e, "classname" );
		const char *pTargetName = ValueForKey( e, "targetname" );
		Error( "bmodel %d has no head node (class '%s', targetname '%s')", entity_num, pClassName, pTargetName );
	}

	MakeTreePortals (tree);
	
#if DEBUG_BRUSHMODEL
	if ( entity_num == DEBUG_BRUSHMODEL )
		WriteGLView( tree, "tree_all" );
#endif

	MarkVisibleSides (tree, start, end, FULL_DETAIL);
	MakeFaces (tree->headnode);

	FixTjuncs( tree->headnode, NULL );
	WriteBSP( tree->headnode, NULL );
	
#if DEBUG_BRUSHMODEL
	if ( entity_num == DEBUG_BRUSHMODEL )
	{
		WriteGLView( tree, "tree_vis" );
		WriteGLViewFaces( tree, "tree_faces" );
	}
#endif

	FreeTree (tree);
}


//-----------------------------------------------------------------------------
// Returns true if the entity is a func_occluder
//-----------------------------------------------------------------------------
bool IsFuncOccluder( int entity_num )
{
	entity_t *mapent = &entities[entity_num];
	const char *pClassName = ValueForKey( mapent, "classname" );
	return (strcmp("func_occluder", pClassName) == 0);
}


//-----------------------------------------------------------------------------
// Computes the area of a brush's occluders
//-----------------------------------------------------------------------------
float ComputeOccluderBrushArea( mapbrush_t *pBrush )
{
	float flArea = 0.0f;
	for ( int j = 0; j < pBrush->numsides; ++j )
	{
		side_t *pSide = &(pBrush->original_sides[j]);

		// Skip nodraw surfaces
		if ( texinfo[pSide->texinfo].flags & SURF_NODRAW )
			continue;

		if ( !pSide->winding )
			continue;

		flArea += WindingArea( pSide->winding );
	}

	return flArea;
}


//-----------------------------------------------------------------------------
// Clips all occluder brushes against each other
//-----------------------------------------------------------------------------
static tree_t *ClipOccluderBrushes( )
{
	// Create a list of all occluder brushes in the level
	CUtlVector< mapbrush_t * > mapBrushes( 1024, 1024 );
	for ( entity_num=0; entity_num < g_MainMap->num_entities; ++entity_num )
	{
		if (!IsFuncOccluder(entity_num))
			continue;

		entity_t *e = &entities[entity_num];
		int end = e->firstbrush + e->numbrushes;
		int i;
		for ( i = e->firstbrush; i < end; ++i )
		{
			mapBrushes.AddToTail( &g_MainMap->mapbrushes[i] );
		}
	}

	int nBrushCount = mapBrushes.Count();
	if ( nBrushCount == 0 )
		return NULL;

	Vector mins, maxs;
	mins[0] = mins[1] = mins[2] = MIN_COORD_INTEGER;
	maxs[0] = maxs[1] = maxs[2] = MAX_COORD_INTEGER;

	bspbrush_t *list = MakeBspBrushList( mapBrushes.Base(), nBrushCount, mins, maxs );

	if (!nocsg)
		list = ChopBrushes (list);
	tree_t *tree = BrushBSP (list, mins, maxs);
	MakeTreePortals (tree);
	MarkVisibleSides (tree, mapBrushes.Base(), nBrushCount);
	MakeFaces( tree->headnode );

	// NOTE: This will output the occluder face vertices + planes
	FixTjuncs( tree->headnode, NULL );

	return tree;
}


//-----------------------------------------------------------------------------
// Generate a list of unique sides in the occluder tree
//-----------------------------------------------------------------------------
static void GenerateOccluderSideList( int nEntity, CUtlVector<side_t*> &occluderSides )
{
	entity_t *e = &entities[nEntity];
	int end = e->firstbrush + e->numbrushes;
	int i, j;
	for ( i = e->firstbrush; i < end; ++i )
	{
		mapbrush_t *mb = &g_MainMap->mapbrushes[i];
		for ( j = 0; j < mb->numsides; ++j )
		{
			occluderSides.AddToTail( &(mb->original_sides[j]) );
		}
	}
}


//-----------------------------------------------------------------------------
// Generate a list of unique faces in the occluder tree
//-----------------------------------------------------------------------------
static void GenerateOccluderFaceList( node_t *pOccluderNode, CUtlVector<face_t*> &occluderFaces )
{
	if (pOccluderNode->planenum == PLANENUM_LEAF)
		return;

	for ( face_t *f=pOccluderNode->faces ; f ; f = f->next )
	{
		occluderFaces.AddToTail( f );
	}

	GenerateOccluderFaceList( pOccluderNode->children[0], occluderFaces );
	GenerateOccluderFaceList( pOccluderNode->children[1], occluderFaces );
}


//-----------------------------------------------------------------------------
// For occluder area assignment
//-----------------------------------------------------------------------------
struct OccluderInfo_t
{
	int m_nOccluderEntityIndex;
};

static CUtlVector< OccluderInfo_t > g_OccluderInfo;


//-----------------------------------------------------------------------------
// Emits occluder brushes
//-----------------------------------------------------------------------------
static void EmitOccluderBrushes()
{
	char str[64];

	g_OccluderData.RemoveAll();
	g_OccluderPolyData.RemoveAll();
	g_OccluderVertexIndices.RemoveAll();

	tree_t *pOccluderTree = ClipOccluderBrushes();
	if (!pOccluderTree)
		return;

	CUtlVector<face_t*> faceList( 1024, 1024 );
	CUtlVector<side_t*> sideList( 1024, 1024 );
	GenerateOccluderFaceList( pOccluderTree->headnode, faceList );

#ifdef _DEBUG
	int *pEmitted = (int*)stackalloc( faceList.Count() * sizeof(int) );
	memset( pEmitted, 0, faceList.Count() * sizeof(int) );
#endif

	for ( entity_num=1; entity_num < num_entities; ++entity_num )
	{
		if (!IsFuncOccluder(entity_num))
			continue;

		// Output only those parts of the occluder tree which are a part of the brush
		int nOccluder = g_OccluderData.AddToTail();
		doccluderdata_t &occluderData = g_OccluderData[ nOccluder ];
		occluderData.firstpoly = g_OccluderPolyData.Count();
		occluderData.mins.Init( FLT_MAX, FLT_MAX, FLT_MAX );
		occluderData.maxs.Init( -FLT_MAX, -FLT_MAX, -FLT_MAX );
		occluderData.flags = 0;
		occluderData.area = -1;

		// NOTE: If you change the algorithm by which occluder numbers are allocated,
		// then you must also change FixupOnlyEntsOccluderEntities() below
		sprintf (str, "%i", nOccluder);
		SetKeyValue (&entities[entity_num], "occludernumber", str);

		int nIndex = g_OccluderInfo.AddToTail();
		g_OccluderInfo[nIndex].m_nOccluderEntityIndex = entity_num;
		
		sideList.RemoveAll();
		GenerateOccluderSideList( entity_num, sideList );
		for ( int i = faceList.Count(); --i >= 0; )
		{
			// Skip nodraw surfaces, but not triggers that have been marked as nodraw
			face_t *f = faceList[i];
			if ( ( texinfo[f->texinfo].flags & SURF_NODRAW ) &&
				 (( texinfo[f->texinfo].flags & SURF_TRIGGER ) == 0 ) )
				continue;

			// Only emit faces that appear in the side list of the occluder
			for ( int j = sideList.Count(); --j >= 0; )
			{
				if ( sideList[j] != f->originalface )
					continue;

				if ( f->numpoints < 3 )
					continue;

				// not a final face
				Assert ( !f->merged && !f->split[0] && !f->split[1] );

#ifdef _DEBUG
				Assert( !pEmitted[i] );
				pEmitted[i] = entity_num;
#endif

				int k = g_OccluderPolyData.AddToTail();
				doccluderpolydata_t *pOccluderPoly = &g_OccluderPolyData[k];

				pOccluderPoly->planenum = f->planenum;
				pOccluderPoly->vertexcount = f->numpoints;
				pOccluderPoly->firstvertexindex = g_OccluderVertexIndices.Count();
				for( k = 0; k < f->numpoints; ++k )
				{
					g_OccluderVertexIndices.AddToTail( f->vertexnums[k] );

					const Vector &p = dvertexes[f->vertexnums[k]].point; 
					VectorMin( occluderData.mins, p, occluderData.mins );
					VectorMax( occluderData.maxs, p, occluderData.maxs );
				}

				break;
			}
		}

		occluderData.polycount = g_OccluderPolyData.Count() - occluderData.firstpoly;

		// Mark this brush as not having brush geometry so it won't be re-emitted with a brush model
		entities[entity_num].numbrushes = 0;
	}

	FreeTree( pOccluderTree );
}


//-----------------------------------------------------------------------------
// Set occluder area
//-----------------------------------------------------------------------------
void SetOccluderArea( int nOccluder, int nArea, int nEntityNum )
{
	if ( g_OccluderData[nOccluder].area <= 0 )
	{
		g_OccluderData[nOccluder].area = nArea;
	}
	else if ( (nArea != 0) && (g_OccluderData[nOccluder].area != nArea) )
	{
		const char *pTargetName = ValueForKey( &entities[nEntityNum], "targetname" );
		if (!pTargetName)
		{
			pTargetName = "<no name>";
		}
		Warning("Occluder \"%s\" straddles multiple areas. This is invalid!\n", pTargetName );
	}
}


//-----------------------------------------------------------------------------
// Assign occluder areas (must happen *after* the world model is processed)
//-----------------------------------------------------------------------------
void AssignAreaToOccluder( int nOccluder, tree_t *pTree, bool bCrossAreaPortals )
{
	int nFirstPoly = g_OccluderData[nOccluder].firstpoly;
	int nEntityNum = g_OccluderInfo[nOccluder].m_nOccluderEntityIndex;
	for ( int j = 0; j < g_OccluderData[nOccluder].polycount; ++j )
	{
		doccluderpolydata_t *pOccluderPoly = &g_OccluderPolyData[nFirstPoly + j];
		int nFirstVertex = pOccluderPoly->firstvertexindex;
		for ( int k = 0; k < pOccluderPoly->vertexcount; ++k )
		{
			int nVertexIndex = g_OccluderVertexIndices[nFirstVertex + k];
			node_t *pNode = NodeForPoint( pTree->headnode, dvertexes[ nVertexIndex ].point );

			SetOccluderArea( nOccluder, pNode->area, nEntityNum );

			int nOtherSideIndex;
			portal_t *pPortal;
			for ( pPortal = pNode->portals; pPortal; pPortal = pPortal->next[!nOtherSideIndex] )
			{
				nOtherSideIndex = (pPortal->nodes[0] == pNode) ? 1 : 0;
				if (!pPortal->onnode)
					continue;		// edge of world

				// Don't cross over area portals for the area check
				if ((!bCrossAreaPortals) && pPortal->nodes[nOtherSideIndex]->contents & CONTENTS_AREAPORTAL)
					continue;

				int nAdjacentArea = pPortal->nodes[nOtherSideIndex] ? pPortal->nodes[nOtherSideIndex]->area : 0; 
				SetOccluderArea( nOccluder, nAdjacentArea, nEntityNum );
			}
		}
	}
}


//-----------------------------------------------------------------------------
// Assign occluder areas (must happen *after* the world model is processed)
//-----------------------------------------------------------------------------
void AssignOccluderAreas( tree_t *pTree )
{
	for ( int i = 0; i < g_OccluderData.Count(); ++i )
	{
		AssignAreaToOccluder( i, pTree, false );

		// This can only have happened if the only valid portal out leads into an areaportal
		if ( g_OccluderData[i].area <= 0 )
		{
			AssignAreaToOccluder( i, pTree, true );
		}
	}
}



//-----------------------------------------------------------------------------
// Make sure the func_occluders have the appropriate data set
//-----------------------------------------------------------------------------
void FixupOnlyEntsOccluderEntities()
{
	char str[64];
	int nOccluder = 0;
	for ( entity_num=1; entity_num < num_entities; ++entity_num )
	{
		if (!IsFuncOccluder(entity_num))
			continue;

		// NOTE: If you change the algorithm by which occluder numbers are allocated above,
		// then you must also change this
		sprintf (str, "%i", nOccluder);
		SetKeyValue (&entities[entity_num], "occludernumber", str);
		++nOccluder;
	}
}


void MarkNoDynamicShadowSides()
{
	for ( int iSide=0; iSide < g_MainMap->nummapbrushsides; iSide++ )
	{
		g_MainMap->brushsides[iSide].m_bDynamicShadowsEnabled = true;
	}

	for ( int i=0; i < g_NoDynamicShadowSides.Count(); i++ )
	{
		int brushSideID = g_NoDynamicShadowSides[i];
	
		// Find the side with this ID.
		for ( int iSide=0; iSide < g_MainMap->nummapbrushsides; iSide++ )
		{
			if ( g_MainMap->brushsides[iSide].id == brushSideID )
				g_MainMap->brushsides[iSide].m_bDynamicShadowsEnabled = false;
		}
	}
}

//-----------------------------------------------------------------------------
// Compute the 3D skybox areas
//-----------------------------------------------------------------------------
static void Compute3DSkyboxAreas( node_t *headnode, CUtlVector<int>& areas )
{
	for (int i = 0; i < g_MainMap->num_entities; ++i)
	{
		char* pEntity = ValueForKey(&entities[i], "classname");
		if (!strcmp(pEntity, "sky_camera"))
		{
			// Found a 3D skybox camera, get a leaf that lies in it
			node_t *pLeaf = PointInLeaf( headnode, entities[i].origin );
			if (pLeaf->contents & CONTENTS_SOLID)
			{
				Error ("Error! Entity sky_camera in solid volume! at %.1f %.1f %.1f\n", entities[i].origin.x, entities[i].origin.y, entities[i].origin.z);
			}
			areas.AddToTail( pLeaf->area );
		}
	}
}

bool Is3DSkyboxArea( int area )
{
	for ( int i = g_SkyAreas.Count(); --i >=0; )
	{
		if ( g_SkyAreas[i] == area )
			return true;
	}
	return false;
}

		
/*
============
ProcessModels
============
*/
void ProcessModels (void)
{
	BeginBSPFile ();

	// Mark sides that have no dynamic shadows.
	MarkNoDynamicShadowSides();

	// emit the displacement surfaces
	EmitInitialDispInfos();

	// Clip occluder brushes against each other, 
	// Remove them from the list of models to process below
	EmitOccluderBrushes( );

	for ( entity_num=0; entity_num < num_entities; ++entity_num )
	{
		entity_t *pEntity = &entities[entity_num];
		if ( !pEntity->numbrushes )
			continue;

		qprintf ("############### model %i ###############\n", nummodels);

		BeginModel ();

		if (entity_num == 0)
		{
			ProcessWorldModel();
		}
		else
		{
			ProcessSubModel( );
		}

		EndModel ();

		if (!verboseentities)
		{
			verbose = false;	// don't bother printing submodels
		}
	}

	// Turn the skybox into a cubemap in case we don't build env_cubemap textures.
	//Cubemap_CreateDefaultCubemaps();
	EndBSPFile ();
}


void LoadPhysicsDLL( void )
{
	PhysicsDLLPath( "vphysics.dll" );
}


void PrintCommandLine( int argc, char **argv )
{
	Warning( "Command line: " );
	for ( int z=0; z < argc; z++ )
	{
		Warning( "\"%s\" ", argv[z] );
	}
	Warning( "\n\n" );
}

void EnsureFileDirectoryExists( const char *pFileName )
{
	char pPath[MAX_PATH];
	V_strcpy (pPath, pFileName); 
	V_FixSlashes( pPath );
	V_StripFilename(pPath);
	char *pLastSlash = strrchr( pPath, CORRECT_PATH_SEPARATOR );
	if ( pLastSlash )
	{
		if (!CreateDirectory(pPath, NULL) && GetLastError()==ERROR_PATH_NOT_FOUND) {
			EnsureFileDirectoryExists(pPath); //This will strip off another subdirectory and try again.
			CreateDirectory(pPath, NULL);
		}
	}
}
void weldVertList(smd_point_t* vertices, float weldvertices){
	int weldnum = 1;
	Vector weldtotal;
	for (int v=1; v<numverts; v++){
		weldnum = 0;
		VectorClear(weldtotal);
		//Don't bother if this already has a weld value
		if (vertices[v].weld > 0) continue;
		//run through and total all nearby verts (including the current one!)
		for (int v2=v; v2 < numverts; v2++) {
			//All the verts that are close to the first one (and haven't been welded)
			if (vertices[v2].weld == 0 && VectorsAreEqual(vertices[v].p, vertices[v2].p, weldvertices)){
				vertices[v2].weld = v;
				weldnum++;
				VectorAdd(vertices[v2].p, weldtotal, weldtotal);
			}
		}
		if (weldnum>1) {	//optimization
			VectorDivide(weldtotal, weldnum, weldtotal);
			//run through the ENTIRE list and move each vert that matches v
			for (int v3=1; v3 < numverts; v3++) {
				if (vertices[v3].weld == v){
					VectorCopy(weldtotal, vertices[v3].p);
				}
			}
		}
	}
}
void SmoothPoints (smd_point_t* vList){
	Vector Normal;
	for (int s=1; s<numverts; s++){
		VectorClear( Normal );
		for (int v=1; v<numverts; v++){
			if (vList[v].smooth == s) Normal += vList[v].n ; //Adding up
		}
		Normal.NormalizeInPlace();
		for (int v=1; v<numverts; v++){
			if (vList[v].smooth == s){
				VectorCopy( Normal, vList[v].n); //assignment
			}
		}
	}
}

bool SmoothGroupTest(unsigned int g1, unsigned int g2){
	if ((g1 & 0xFF000000) || (g2 & 0xFF000000)) return false; //indicates a "hard" group (25-32).
	if (g1 & g2) return true;
	return false;
}
bool AngleTest(Vector* v1, Vector* v2, int smoothangle){
	float angle;
	//Msg("%f ", (float)DotProduct(*v1, *v2)/VectorLength(*v1)/VectorLength(*v2));
	angle = (float)DotProduct(*v1, *v2)/VectorLength(*v1)/VectorLength(*v2);
	if (angle > cos((float)smoothangle) ) return true; else return false;
}
void MakeTriangle(smd_point_t* p0, smd_point_t* p1, smd_point_t* p2, int num_tris, smd_triangle_t* tri, smd_point_t *vertices){
	if (num_tris==MAX_SMD_TRIS) Error("Too many polies in mesh. %i max.", MAX_SMD_TRIS);
	tri->p[0] = num_tris*3+1;
	tri->p[1] = num_tris*3+2;
	tri->p[2] = num_tris*3+3;
	//Copying all the shit from the temporary dispverts into the new triangle
	VectorCopy(p0->p, vertices[num_tris*3+1].p);
	VectorCopy(p1->p, vertices[num_tris*3+2].p);
	VectorCopy(p2->p, vertices[num_tris*3+3].p);

	VectorCopy(p0->n, vertices[num_tris*3+1].n);
	VectorCopy(p1->n, vertices[num_tris*3+2].n);
	VectorCopy(p2->n, vertices[num_tris*3+3].n);

	vertices[num_tris*3+1].u = p0->u;
	vertices[num_tris*3+2].u = p1->u;
	vertices[num_tris*3+3].u = p2->u;
	vertices[num_tris*3+1].v = p0->v;
	vertices[num_tris*3+2].v = p1->v;
	vertices[num_tris*3+3].v = p2->v;

	vertices[num_tris*3+1].smooth = 0;
	vertices[num_tris*3+2].smooth = 0;
	vertices[num_tris*3+3].smooth = 0;
}
static qboolean StringIsTrue( const char *str )
{
	if( Q_strcasecmp( str, "true" ) == 0 )
	{
		return true;
	}
	if( Q_strcasecmp( str, "1" ) == 0 )
	{
		return true;
	}
	return false;
}
bool MaterialIsInvisible(MaterialSystemMaterial_t hMaterial){
	const char* propVal;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileHint" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileSkip" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileOrigin" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileTrigger" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileWater" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileSky" ) ) &&		StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileClip" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%playerClip" ) ) &&		StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileNpcClip" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileNoChop" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compilePlayerControlClip" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileNoDraw" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileInvisible" ) ) &&	StringIsTrue( propVal ) )return true;
	return false;
}
bool MaterialIsNonSolid(MaterialSystemMaterial_t hMaterial){
	const char* propVal;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileHint" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileSkip" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileOrigin" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileTrigger" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileWater" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileNonsolid" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compileSlime" ) ) &&	StringIsTrue( propVal ) )return true;
	if( ( propVal = GetMaterialVar( hMaterial, "%compilePlayerControlClip" ) ) &&	StringIsTrue( propVal ) )return true;
	return false;
}
int compareShaderName(const char* str){
	if (strstr(str, "VertexLitGeneric")) return 0;
	if (strstr(str, "Refract")) return 0; //0 because nothing needs to be done
	if (strstr(str, "LightmappedGeneric")) return 1;
	if (strstr(str, "UnlitGeneric")) return 2;
	if (strstr(str, "WorldTwoTextureBlend")) return 3;
	if (strstr(str, "WorldVertexTransition")) return 4;
	if (strstr(str, "SpriteCard")) return 5;
	if (strstr(str, "Cable")) return 6;
	else return 0;
}
bool validateShaderParam(char* str){ //leave out unsupported shader properties
	strlwr(str);
	if (mat_nonormal){
		if (strstr(str, "$bump")) return false;
		if (strstr(str, "$forcebump")) return false;
		if (strstr(str, "$nodiffusebumplighting")) return false;
		if (strstr(str, "$normalmap")) return false;
	}
	if (strstr(str, "$ssbump")) return false;
	//if (strstr(str, "$detail")) return false;
	if (strstr(str, "$model")) return false;//Because I'm putting it in anyway. Don't want two.
	if (strstr(str, "$basetexture2")) return false;
	if (strstr(str, "$surfaceprop2")) return false;
	if (strstr(str, "$blendmodulatetexture")) return false;
	if (strstr(str, "$decal")) return false;
	if (strstr(str, "$seamless_scale")) return false;
	if (strstr(str, "$blendmodulatetexture")) return false;
	if (strstr(str, "$basetexturetransform2")) return false;
	if (strstr(str, "$reflectivity")) return false;
	if (strstr(str, "$bumpmap2")) return false;
	else return true;
}
//Materials are not converted twice from the same source.
//However, if we have 2 with the same base name we add a suffix.
int MaterialDupe(char* FileName){
	int num = -1; //one for the initial search.
	strlwr(FileName);
	smd_texture_t* p_tex = smd_textures;
	while (p_tex){
		if (!strcmp(p_tex->texname, FileName)) num++;
		p_tex = p_tex->next;
	}
	if (num < 0)Warning("What?\n");
	return num;
}
bool MaterialUsed(char* PathIn){
	smd_texture_t* p_tex = smd_textures;
	while(p_tex){
		if (!strcmp(p_tex->texpath, PathIn)) return true;
		p_tex = p_tex->next;
	}
	//Allocate and record new texture.
	//Adding to the head of the list is easier.
	//p_tex now refers to the old head entry
	p_tex = smd_textures;
	smd_textures = (smd_texture_t*)malloc(sizeof(smd_texture_t));
	assert(p_tex);
	smd_textures->next = p_tex;
	smd_textures->texpath = (char*)malloc( strlen(PathIn) + 1);
	V_strncpy(smd_textures->texpath, PathIn, strlen(PathIn) + 1);
	smd_textures->texname = (char*)malloc( 512);
	V_FileBase(PathIn, smd_textures->texname, 512);
	return false;
}
int fixupMaterial(const char* pMatName, const char* qc_cdmaterials, bool count){
	int suffix = 0;
	char matLwr[256];
	//The base material name plus suffix
	char FileName[256];
	//The file to read from -gamedir
	char PathIn[1024];
	//The full file path to write
	char PathOut[1024];

	V_strncpy( &matLwr[0], pMatName, 256 );
	strlwr(&matLwr[0]);

	//Don't fix materials what already been fixd.
	if (!MaterialUsed(&matLwr[0])){
		if (count) smdmaterials++;
		bool addModel = false;
		CUtlBuffer buffer(0,0,1);

		V_snprintf(&PathIn[0], 1024, "materials/%s.vmt", matLwr);

		//Just the file name + suffix + extension to write. 
		V_FileBase( &PathIn[0], &FileName[0], 256 );
		//add numbers for dupe file names.
		suffix = MaterialDupe(&FileName[0]);

		if (suffix > 0)	V_snprintf(&FileName[0], 256, "%s(%i)", FileName, suffix);
		V_DefaultExtension(&FileName[0], ".vmt", 256);

		//The material to convert might be in materials\ root:
		if (strlen(qc_cdmaterials))	V_snprintf(&PathOut[0], 1024, "%smaterials/%s/%s", gamedir, qc_cdmaterials, FileName);
		else V_snprintf(&PathOut[0], 1024, "%smaterials/%s", gamedir, FileName);

		Msg("Material: ");
		Msg(matLwr);
		Msg(" - ");
		bool pFound = true;
		MaterialSystemMaterial_t hMaterial = FindMaterial( matLwr, &pFound, false );
		if (!pFound) return 0;
		if (MaterialIsInvisible(hMaterial)){
			Msg("Material deemed invisible. No conversion needed.\n");
			return 0;
		}
		const char* pShaderName = GetMaterialShaderName(hMaterial);
//		Msg(pShaderName);
//		Msg("\n");
		if (!g_pFullFileSystem->FileExists( PathIn )) {Warning("Material not found!\n"); return 0;}
		FileHandle_t matfile;
		matfile = g_pFullFileSystem->Open( PathIn, "r" );
//		if (g_pFullFileSystem->ReadToBuffer( matfile, buffer, 0, 0 )) Msg("Read successfully\n");
		g_pFullFileSystem->ReadToBuffer( matfile, buffer, 0, 0 );
		g_pFullFileSystem->Close(matfile);

		const char* subShaderName = "Dont_replace";
		switch (compareShaderName(pShaderName)){
			case 0: subShaderName = "Dont_replace";
				Msg ("VertexLitGeneric, Refract, or unrecognized shader found. No conversion.\n");
				break;
			case 1: subShaderName = "LightmappedGeneric";
				Msg ("LightmappedGeneric converted to vertexlitgeneric.\n");
				break;
			case 2: subShaderName = "Dont_replace";
				addModel = true;
				Msg ("UnlitGeneric shader: Adding $model to VMT.\n");
				break;
			case 3: subShaderName = "WorldTwoTextureBlend";
				Msg ("WorldTwoTextureBlend converted to vertexlitgeneric. Using $basetexture only.\n");
				break;
			case 4: subShaderName = "WorldVertexTransition";
				Msg ("WorldVertexTransition converted to vertexlitgeneric. Using $basetexture only.\n");
				break;
			case 5: subShaderName = "SpriteCard";
				Msg ("SpriteCard converted to vertexlitgeneric.\n");
				break;
			case 6: subShaderName = "Cable";
				Msg ("Cable converted to vertexlitgeneric.\n");
				break;
		}
		//Make that new vmt!
		FileHandle_t matfile2;
		EnsureFileDirectoryExists(&PathOut[0]);
//		Msg(PathOut);
		matfile2 = g_pFullFileSystem->Open( PathOut, "w" );
		if (!matfile2) Error ("Could not open material %s for writing! Make sure the directory exists.\n", PathOut);

		while(buffer.GetBytesRemaining()>0){
			char Line[1024];
			char LineIn[1024];
			buffer.GetLine( &LineIn[0], 1024 );
			V_StrSubst( &LineIn[0], subShaderName, "VertexLitGeneric", &Line[0], 1024, false );
			if (addModel && strstr(Line, "$basetexture")){
				g_pFullFileSystem->Write( "\t$model 1 \r", 11, matfile2 ); //just put $model in before basetexture, since I know it will be there.
				addModel = false;
			}
			if (validateShaderParam(&Line[0])) g_pFullFileSystem->Write( Line, V_strlen(Line), matfile2 );
		}
		g_pFullFileSystem->Close(matfile2);
	}
	return suffix;
}
int OutputDisp(mapdispinfo_t* pMapDisp, smd_triangle_t *tri, smd_point_t *vertices, int num_tris, brush_texture_t* pTexture, bool disp_nowarp, const char* qc_cdmaterials){
	const char *cTexFileName;
	int suffix = 0;
	if(!pTexture) Error("Texture not found");
	cTexFileName = pTexture->name;
	MaterialSystemMaterial_t hMaterial;
	hMaterial = FindMaterial( cTexFileName, NULL, false );
	smd_point_t dispVerts[MAX_DISPVERTS];
	if (MaterialIsInvisible(hMaterial)) {
		Msg("Displacement with invisible material found. Skipping...\n");
		return num_tris;
	}
	int texHeight = 512, texWidth = 512;
	GetMaterialDimensions( hMaterial, &texWidth, &texHeight );

	CCoreDispInfo coreDispInfo;
	DispMapToCoreDispInfo( pMapDisp, &coreDispInfo, 0, 0 );
	int nverts = coreDispInfo.GetSize();
	Vector2D UVCoord;

	Vector *sVector = &pTexture->UAxis;
	Vector *tVector = &pTexture->VAxis;
	tVector->Negate();
	Vector point;
	for( int i = 0; i < nverts; i++ ){
		coreDispInfo.GetVert(i, dispVerts[i].p);
		coreDispInfo.GetNormal(i, dispVerts[i].n);
		dispVerts[i].p -= entities[pMapDisp->entitynum].origin;

		if (disp_nowarp){ //Do UVS based on offset positioning
			coreDispInfo.GetVert(i, point);
		}
		else{
			coreDispInfo.GetFlatVert(i, point);
		}
		dispVerts[i].u = (DotProduct(point, *sVector)/pTexture->textureWorldUnitsPerTexel[0]+pTexture->shift[0])/texWidth;
		dispVerts[i].v = (DotProduct(point, *tVector)/pTexture->textureWorldUnitsPerTexel[1]-pTexture->shift[1])/texHeight;
	}

	//material fixing
	if (fixMaterials) {
		suffix = fixupMaterial(cTexFileName, qc_cdmaterials, true);
	}

	//Keep just the name, for the smd.
	char texname[128];
	V_FileBase( pTexture->name, &texname[0], 128);
	if (suffix > 0)	V_snprintf(&texname[0], 128, "%s(%i)", texname, suffix);
	strlwr( texname );

	//make tris, get normal vectors
	unsigned short v1, v2, v3;
	for( int i = 0; i < coreDispInfo.GetTriCount(); i++ ){
		V_snprintf(tri[num_tris].material, 128, "%s.vmt\r\n", texname);
		coreDispInfo.GetTriIndices(i, v1, v2, v3);
		MakeTriangle(&dispVerts[v3], &dispVerts[v2], &dispVerts[v1], num_tris, &tri[num_tris], vertices);
		num_tris++;
	}
	return num_tris;
}
bool ValidTriangle(Vector v1, Vector v2, Vector v3 ){
	//Skip triangles with zero area
	Vector r1, r2;
	r1 = v1-v2;
	r2 = v1-v3;
	if (!VectorLength(CrossProduct(r1, r2))) return false;
	return true;
}
void SaveOBJ( smd_triangle_t *tri, smd_point_t *vertices, const char *OBJfilename, int num_tris ){
	FileHandle_t OBJFile01;
	Msg("Writing %s\n", OBJfilename);
	EnsureFileDirectoryExists(OBJfilename);
	char FN_Base[256];
	V_FileBase(OBJfilename,&FN_Base[0], 256);
	OBJFile01 = g_pFileSystem->Open(OBJfilename, "wb");
	int num_tris_final = num_tris;

	if (!OBJFile01)
	{
		Error("Failed to create OBJ file! Make sure the folder exists.");
	}
	CmdLib_FPrintf(OBJFile01, "#OBJ created by Propper\r\n");
//	CmdLib_FPrintf(OBJFile01, "mtllib %s.mtl\r\n", FN_Base);
	//Write out all vertices
	//TODO3: is it worth it to combine identical vertices? Probably not.
	for (int v=1; v < numverts; v++){
		//List of Vertices, with (x,y,z[,w]) coordinates, w is optional.
		CmdLib_FPrintf(OBJFile01, "v %f %f %f\r\n", vertices[v].p.x, vertices[v].p.y, vertices[v].p.z);
	}
	CmdLib_FPrintf(OBJFile01, "\r\n");
	for (int v=1; v < numverts; v++){
		//Texture coordinates, in (u,v[,w]) coordinates, w is optional.
		CmdLib_FPrintf(OBJFile01, "vt %f %f\r\n",  vertices[v].u, vertices[v].v);
	}
	CmdLib_FPrintf(OBJFile01, "\r\n");
	for (int v=1; v < numverts; v++){
		//Normals in (x,y,z) form; normals might not be unit.
		CmdLib_FPrintf(OBJFile01, "vn %f %f %f\r\n", vertices[v].n.x, vertices[v].n.y, vertices[v].n.z);
	}
	CmdLib_FPrintf(OBJFile01, "\r\n");
	//Write out all faces
	//TODO3: group faces by material
	for( int i=0; i < num_tris; i++ )
	{
		if (ValidTriangle(vertices[tri[i].p[0]].p, vertices[tri[i].p[1]].p, vertices[tri[i].p[2]].p)){
			for (int v=0; v<3; v++){
			//f v1/vt1/vn1 v2/vt2/vn2 v3/vt3/vn3 points, uv, and normals will all be indexed the same, so don't worry.
			//counter-clockwise, same as SMD 
			CmdLib_FPrintf(OBJFile01, "usemap %s", tri[i].material);
			CmdLib_FPrintf(OBJFile01, "f %i/%i/%i ", tri[i].p[0], tri[i].p[0], tri[i].p[0]);//in OBJ, vertices are 1-indexed
			CmdLib_FPrintf(OBJFile01, "%i/%i/%i ", tri[i].p[1], tri[i].p[1], tri[i].p[1]);
			CmdLib_FPrintf(OBJFile01, "%i/%i/%i\r\n", tri[i].p[2], tri[i].p[2], tri[i].p[2]);
			}
		}
		else num_tris_final--;
	}
	Msg("%i triangles written.\n", num_tris_final);
	Msg("------------------------\n");
	CmdLib_FPrintf(OBJFile01, "end");
	g_pFileSystem->Close(OBJFile01);
}
void SaveSMD( smd_triangle_t *tri, smd_point_t *vertices, const char *SMDfilename, int num_tris )
{
	Msg("Writing %s\n", SMDfilename);
	FileHandle_t SMDFile01;
	EnsureFileDirectoryExists(SMDfilename);
	SMDFile01 = g_pFileSystem->Open(SMDfilename, "wb");
	int num_tris_final = num_tris;

	if (!SMDFile01)
	{
		Error("Failed to create SMD file! Make sure the folder exists.");
	}
	CmdLib_FPrintf(SMDFile01, "version 1\r\n"
		"nodes\r\n"
		"0 \"static_prop\" -1\r\n"
		"end\r\n"
		"skeleton\r\n"
		"time 0\r\n"
		"0 0.000000 0.000000 0.000000 0.000000 0.000000 0.000000\r\n"
		"end\r\n"
		"triangles\r\n"
	);
	for( int i=0; i < num_tris; i++ )
	{
		if (ValidTriangle(vertices[tri[i].p[0]].p, vertices[tri[i].p[1]].p, vertices[tri[i].p[2]].p)){
			CmdLib_FPrintf(SMDFile01, "%s", tri[i].material);
			CmdLib_FPrintf(SMDFile01, "0 %f %f %f %f %f %f %f %f\r\n", vertices[tri[i].p[0]].p.x, vertices[tri[i].p[0]].p.y, vertices[tri[i].p[0]].p.z, vertices[tri[i].p[0]].n.x, vertices[tri[i].p[0]].n.y, vertices[tri[i].p[0]].n.z,  vertices[tri[i].p[0]].u, vertices[tri[i].p[0]].v);
			CmdLib_FPrintf(SMDFile01, "0 %f %f %f %f %f %f %f %f\r\n", vertices[tri[i].p[1]].p.x, vertices[tri[i].p[1]].p.y, vertices[tri[i].p[1]].p.z, vertices[tri[i].p[1]].n.x, vertices[tri[i].p[1]].n.y, vertices[tri[i].p[1]].n.z,  vertices[tri[i].p[1]].u, vertices[tri[i].p[1]].v);
			CmdLib_FPrintf(SMDFile01, "0 %f %f %f %f %f %f %f %f\r\n", vertices[tri[i].p[2]].p.x, vertices[tri[i].p[2]].p.y, vertices[tri[i].p[2]].p.z, vertices[tri[i].p[2]].n.x, vertices[tri[i].p[2]].n.y, vertices[tri[i].p[2]].n.z,  vertices[tri[i].p[2]].u, vertices[tri[i].p[2]].v);
		}
		else num_tris_final--;
	}
	Msg("%i triangles written.\n", num_tris_final);
	Msg("------------------------\n");
	CmdLib_FPrintf(SMDFile01, "end");
	g_pFileSystem->Close(SMDFile01);
}
entity_t* EntityByName2( char const *pTestName )
{
	if( !pTestName )
		return 0;

	for( int i=0; i < num_entities; i++ )
	{
		entity_t *e = &entities[i];

		const char *pName = ValueForKey( e, "targetname" );
		if( stricmp( pName, pTestName ) == 0 )
			return e;
	}

	return 0;
}
void MakeSMD(bool phys, char *SMDfilename, int ent, float weldvertices, model_t* m )
{
//This causes stack overflow WTF computers are hard
//	smd_triangle_t smd_tris[MAX_SMD_TRIS];
//	smd_point_t smd_pts[MAX_SMD_VERTS+1];
//	smd_triangle_t *tri = &smd_tris[0];
//	smd_point_t *vertices = &smd_pts[0];

	//TODO2: be sure to reset stuff in the points/tris array, esp. smoothing
	for (int v=1; v < numverts; v++){
		smd_pts[v].smooth = 0;
		smd_pts[v].weld = 0;
	}
	smdmaterials = 0;
	int suffix = 0;
	Vector Offset;
	const char *cTexFileName;
	int num_tris = 0;
	winding_t *wind;
	int texHeight = 512, texWidth = 512;
	brush_texture_t* pTexture;
	MaterialSystemMaterial_t hMaterial;
	if (phys) Msg("Building physics mesh...\n");
	else Msg("Building mesh...\n");
	//Displacements first. Why? Why not?
	if (!phys){
		for(int i=0; i< nummapdispinfo; i++){
			if (mapdispinfo[i].entitynum == ent){
				pTexture = &g_MainMap->side_brushtextures[mapdispinfo[i].td_num];
				num_tris = OutputDisp(&mapdispinfo[i], &smd_tris[0], &smd_pts[0], num_tris, pTexture, m->disp_nowarp, m->qc_cdmaterials);
			}
		}
	}
	for( int i=0; i < g_MainMap->nummapbrushes; i++ )
	{
		if (g_MainMap->mapbrushes[i].entitynum == ent)//ignore everything not in the specified entity
		{
			//bool thisBrushSolid = true; //We no longer use this.
			if (g_MainMap->mapbrushes[i].entitynum != 0) {
				Offset = g_MainMap->entities[g_MainMap->mapbrushes[i].entitynum].origin;
			}
			else VectorClear(Offset);
			//if (phys && !thisBrushSolid)continue; //skip to the next solid.

			//counting physics hulls
			if (phys) m->num_physhulls++;

			//Now write out each side in the brush.
			for( int j=0; j < g_MainMap->mapbrushes[i].numsides; j++ )
			{
				suffix = 0;
				wind = g_MainMap->mapbrushes[i].original_sides[j].winding;
				if (wind) //There are extra sides that have no winding. Ignore em.
				{
					pTexture = &g_MainMap->side_brushtextures[g_MainMap->mapbrushes[i].original_sides[j].td_num];
					if(!pTexture) Error("Texture not found");
					cTexFileName = pTexture->name;
					if (fixMaterials && !phys) {
						suffix = fixupMaterial(cTexFileName, m->qc_cdmaterials, true);
					}
					//DEBUG: Msg("td_num: %i, %s\n", mapbrushes[i].original_sides[j].td_num, cTexFileName);
					hMaterial = FindMaterial( cTexFileName, NULL, false );
					//These faces will be invisible. Skip to the next face.
					if (!phys){
						if (MaterialIsInvisible(hMaterial)) continue;
					}
					GetMaterialDimensions( hMaterial, &texWidth, &texHeight );

					//Keep just the name, for the smd.
					char texname[128];
					V_FileBase( cTexFileName, &texname[0], 128);
					if (suffix > 0)	V_snprintf(&texname[0], 128, "%s(%i)", texname, suffix);
					strlwr( texname );

					//Find winding normal
					Vector	t1, t2, normal;

					VectorSubtract (wind->p[1], wind->p[0], t1);
					VectorSubtract (wind->p[1], wind->p[2], t2);
					CrossProduct (t1, t2, normal);
					VectorNormalize (normal);

					//texture vectors
					Vector *sVector = &pTexture->UAxis;
					Vector *tVector = &pTexture->VAxis;
					tVector->Negate();
					
//					for (int point=0; point>wind->numpoints; point++){
//						wind->p[point] += Offset;
//					}

					//Save triangles, each starting with the last point in the winding.
					//winding is clockwise, smd tris are counter-clockwise.
					for ( int t=wind->numpoints-2; t > 0; t-- ){
						if (num_tris==MAX_SMD_TRIS) Error("Too many polies in mesh. %i max.", MAX_SMD_TRIS);
						smd_tris[num_tris].p[0] = num_tris*3+1;
						smd_tris[num_tris].p[1] = num_tris*3+2;
						smd_tris[num_tris].p[2] = num_tris*3+3;

						smd_point_t* p0 = &smd_pts[smd_tris[num_tris].p[0]];
						smd_point_t* p1 = &smd_pts[smd_tris[num_tris].p[1]];
						smd_point_t* p2 = &smd_pts[smd_tris[num_tris].p[2]];

						VectorCopy(wind->p[wind->numpoints-1], p0->p);
						VectorCopy(normal,                     p0->n);
						VectorCopy(wind->p[t], p1->p);
						VectorCopy(normal,     p1->n);
						VectorCopy(wind->p[t-1], p2->p);
						VectorCopy(normal,       p2->n);

						if (phys) V_snprintf(smd_tris[num_tris].material, 128, "physbox.vmt\r\n"); //this avoids the "no refract on physbox" problem.
						else V_snprintf(smd_tris[num_tris].material, 128, "%s.vmt\r\n", texname);

						p0->u = (DotProduct(wind->p[wind->numpoints-1] + Offset, *sVector)/pTexture->textureWorldUnitsPerTexel[0]+pTexture->shift[0])/texWidth;
						p0->v = (DotProduct(wind->p[wind->numpoints-1] + Offset, *tVector)/pTexture->textureWorldUnitsPerTexel[1]-pTexture->shift[1])/texHeight;
						p1->u = (DotProduct(wind->p[t] + Offset, *sVector)/pTexture->textureWorldUnitsPerTexel[0]+pTexture->shift[0])/texWidth;
						p1->v = (DotProduct(wind->p[t] + Offset, *tVector)/pTexture->textureWorldUnitsPerTexel[1]-pTexture->shift[1])/texHeight;
						p2->u = (DotProduct(wind->p[t-1] + Offset, *sVector)/pTexture->textureWorldUnitsPerTexel[0]+pTexture->shift[0])/texWidth;
						p2->v = (DotProduct(wind->p[t-1] + Offset, *tVector)/pTexture->textureWorldUnitsPerTexel[1]-pTexture->shift[1])/texHeight;


						smd_tris[num_tris].brush = g_MainMap->mapbrushes[i].id;
						p0->brush = g_MainMap->mapbrushes[i].id;
						p1->brush = g_MainMap->mapbrushes[i].id;
						p2->brush = g_MainMap->mapbrushes[i].id;

						p0->wcSmooth = g_MainMap->mapbrushes[i].original_sides[j].smoothingGroups;
						p1->wcSmooth = g_MainMap->mapbrushes[i].original_sides[j].smoothingGroups;
						p2->wcSmooth = g_MainMap->mapbrushes[i].original_sides[j].smoothingGroups;
						num_tris++;
					}
				}
			}
		}
	}
	numverts = num_tris*3+1;//right? because we leave the first one blank?
	if (phys){
		Msg("Collision model created with %i pieces.\n", m->num_physhulls);
		if (m->num_physhulls > 30) Warning("That is a \"costly collision model\". Try using fewer brushes for collision to make the model more efficient.\n");
	}
	if (!phys && weldvertices > 0) weldVertList(&smd_pts[0], weldvertices); //Might want to force some welding to overcome float errors.
	if (phys) weldVertList(&smd_pts[0], 0.1);//Physics models need welded regardless.

	if (m->snaptogrid){
		for (int v=1; v < numverts; v++){
			smd_pts[v].p.x = floor(smd_pts[v].p.x + 0.5);
			smd_pts[v].p.y = floor(smd_pts[v].p.y + 0.5);
			smd_pts[v].p.z = floor(smd_pts[v].p.z + 0.5);
		}
	}
//	Msg("Building smoothing groups...\n");
	if (phys)
	{
		for (int v=1; v < numverts; v++){
			if (smd_pts[v].smooth > 0) continue; 
			smd_pts[v].smooth = v;
			for (int s=v+1; s < numverts; s++) {
				if (VectorsAreEqual(smd_pts[v].p, smd_pts[s].p, 0.01) && smd_pts[v].brush == smd_pts[s].brush){
					smd_pts[s].smooth = v;
				}
			}
		}
	}
	if (!phys && m->smoothing == SMOOTH_DEFAULT)
	{
		for (int v=1; v < numverts; v++){
			if (smd_pts[v].smooth > 0) continue; 
			smd_pts[v].smooth = v;
			for (int s=v+1; s < numverts; s++) {
				if (VectorsAreEqual(smd_pts[v].p, smd_pts[s].p, 0.1) && AngleTest(&smd_pts[v].n, &smd_pts[s].n, m->smoothangle)){
					smd_pts[s].smooth = v;
				}
			}
		}
	}
	if (!phys && m->smoothing == SMOOTH_GROUPSONLY)
	{
		for (int v=1; v < numverts; v++){
			if (smd_pts[v].smooth > 0) continue; 
			smd_pts[v].smooth = v;
			for (int s=v+1; s < numverts; s++) {
				if (VectorsAreEqual(smd_pts[v].p, smd_pts[s].p, 0.1) && SmoothGroupTest(smd_pts[v].wcSmooth, smd_pts[s].wcSmooth)){
					smd_pts[s].smooth = v;
				}
			}
		}
	}
	//smooth that shit!
	SmoothPoints(&smd_pts[0]);
	if (objExport) 	SaveOBJ( &smd_tris[0], &smd_pts[0], SMDfilename, num_tris );
	else SaveSMD( &smd_tris[0], &smd_pts[0], SMDfilename, num_tris );
}
void model_t::getMapProperties(){
	//Look for shit to apply to this model
	entity_t* mapent;
	char *pClassName;
	for (int i=0; i<num_entities; i++){
		mapent = &entities[i];
		pClassName = ValueForKey( mapent, "classname" );
		if ( !strcmp( phys_entname, ValueForKey( mapent, "targetname" ) ) ){
			phys_entnum = g_MainMap->mapbrushes[mapent->firstbrush].entitynum;
		}
		if ( !strcmp( ent_name, ValueForKey( mapent, "my_model" ) ) ){
			if ( !strcmp( "info_prop_physics", pClassName ) || !strcmp( "propper_physics", pClassName) ){
				if (!phy) phy = new phys_data_t();
				assert(phy != 0);
				physicsprop = true;
//				dophysmodel = true;
				phy->base = ValueForKey( mapent, "base" );
				phy->health = IntForKey( mapent, "health" );
				phy->physicsmode = IntForKey( mapent, "physicsmode" );
				phy->flammable = IntForKey( mapent, "flammable" ) !=0;
				phy->ignite = IntForKey( mapent, "ignite_at_half_health" ) !=0;
				phy->explosive_resist = IntForKey( mapent, "explosive_resist" ) !=0;
				phy->explosive_damage = FloatForKey( mapent, "explosive_damage" );
				phy->explosive_radius = FloatForKey( mapent, "explosive_radius" );
				phy->breakable_model = ValueForKey( mapent, "breakable_model" );
				phy->breakable_count = IntForKey( mapent, "breakable_count" );
				phy->breakable_skin = IntForKey( mapent, "breakable_skin" );
			}
			if ( !strcmp( "propper_physgun_interactions", pClassName ) )
			{
				if (!phys_int) phys_int = new phys_interactions_t();
				assert(phys_int != 0);
				phys_interactions = true;
				GetVectorForKey( mapent, "angles", phys_int->angles);
				phys_int->preferred_carryangles = IntForKey( mapent, "preferred_carryangles" ) !=0;
				phys_int->stick = IntForKey( mapent, "stick" ) !=0;
				phys_int->bloodsplat = IntForKey( mapent, "bloodsplat" ) !=0;
				//break is a keyword lol
				phys_int->break_ = IntForKey( mapent, "break" ) !=0;
				phys_int->paintsplat = IntForKey( mapent, "paintsplat" ) !=0;
				phys_int->impale = IntForKey( mapent, "impale" ) !=0;
				phys_int->onlaunch = ValueForKey( mapent, "onlaunch" );
				phys_int->explode_fire = IntForKey( mapent, "explode_fire" ) !=0;
			}
			if ( !strcmp( "propper_attachment", pClassName ) )
			{
				if (num_attachments == 16) Error("Too many \"propper_attachment\" entities in your map. 16 max.\n");
				att[num_attachments].name = ValueForKey( mapent, "targetname" );
				GetVectorForKey( mapent, "angles", att[num_attachments].angles);
				GetVectorForKey( mapent, "origin", att[num_attachments].origin);
				//Offset based on the origin of the propper_model
				att[num_attachments].origin -= origin;
				num_attachments++;
			}
			if ( !strcmp( "propper_bodygroup", pClassName ) )
			{
				entity_t* myent;
				dobodygroup = true;
				bodygroups.groupname = ValueForKey(mapent, "groupname");
				myent = EntityByName2(ValueForKey(mapent, "body01"));
				if (myent!=0) bodygroups.body_ents[0] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body02"));
				if (myent!=0) bodygroups.body_ents[1] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body03"));
				if (myent!=0) bodygroups.body_ents[2] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body04"));
				if (myent!=0) bodygroups.body_ents[3] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body05"));
				if (myent!=0) bodygroups.body_ents[4] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body06"));
				if (myent!=0) bodygroups.body_ents[5] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body07"));
				if (myent!=0) bodygroups.body_ents[6] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body08"));
				if (myent!=0) bodygroups.body_ents[7] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body09"));
				if (myent!=0) bodygroups.body_ents[8] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body10"));
				if (myent!=0) bodygroups.body_ents[9] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body11"));
				if (myent!=0) bodygroups.body_ents[10] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body12"));
				if (myent!=0) bodygroups.body_ents[11] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body13"));
				if (myent!=0) bodygroups.body_ents[12] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body14"));
				if (myent!=0) bodygroups.body_ents[13] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body15"));
				if (myent!=0) bodygroups.body_ents[14] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
				myent = EntityByName2(ValueForKey(mapent, "body16"));
				if (myent!=0) bodygroups.body_ents[15] = g_MainMap->mapbrushes[myent->firstbrush].entitynum;
			}
			if ( !strcmp( "propper_lod", pClassName ) )
			{
				//TODO2: Sort by switch metric
				if (num_lods == 16) Error("Too many \"propper_lod\" entities in your map. 16 max.\n");
	//			lods[num_lods].entname = ValueForKey(mapent, "targetname");
				lods[num_lods].entnum = g_MainMap->mapbrushes[mapent->firstbrush].entitynum;
				lods[num_lods].weldvertices = FloatForKey(mapent, "weldvertices");
				lods[num_lods].distance = IntForKey(mapent, "distance");
				num_lods++;
			}
			if ( !strcmp( "propper_gibs", pClassName ) )
			{
				if (num_gibs == 16) Error("Too many \"propper_gibs\" entities in your map. 16 max.\n");
				gibs[num_gibs].gibmodel = ValueForKey(mapent, "model");
				gibs[num_gibs].ragdoll = ValueForKey(mapent, "ragdoll");
				gibs[num_gibs].debris = IntForKey(mapent, "debris");
				gibs[num_gibs].burst = IntForKey(mapent, "burst");
				gibs[num_gibs].fadetime = IntForKey(mapent, "fadetime");
				gibs[num_gibs].fademindist = IntForKey(mapent, "fademindist");
				gibs[num_gibs].fademaxdist = IntForKey(mapent, "fademaxdist");
				num_gibs++;
			}
			if ( !strcmp( "propper_particles", pClassName ) )
			{
				if (num_particles == 16) Error("Too many \"propper_particles\" entities in your map. 16 max.\n");
				particles[num_particles].name = ValueForKey(mapent, "name");
				particles[num_particles].attachment_type = ValueForKey(mapent, "attachment_type");
				particles[num_particles].attachment_point = ValueForKey(mapent, "attachment_point");
				num_particles++;
			}
			if ( !strcmp( "propper_cables", pClassName ) )
			{
				if (num_cables == 16) Error("Too many \"propper_cables\" entities in your map. 16 max.\n");
				cables[num_cables].start = ValueForKey(mapent, "StartAttachment");
				cables[num_cables].end = ValueForKey(mapent, "EndAttachment");
				cables[num_cables].mat = ValueForKey(mapent, "Material");
				cables[num_cables].width = IntForKey(mapent, "Width");
				cables[num_cables].segments = IntForKey(mapent, "NumSegments");
				cables[num_cables].length = IntForKey(mapent, "Length");
				num_cables++;
			}
			if ( !strcmp( "propper_skins", pClassName ) )
			{
				if (num_skinfamilies == 16) Error("Too many \"propper_skins\" entities in your map. 16 max.\n");
				skins[num_skinfamilies].mat[0] = ValueForKey(mapent, "mat0");
				skins[num_skinfamilies].mat[1] = ValueForKey(mapent, "mat1");
				skins[num_skinfamilies].mat[2] = ValueForKey(mapent, "mat2");
				skins[num_skinfamilies].mat[3] = ValueForKey(mapent, "mat3");
				skins[num_skinfamilies].mat[4] = ValueForKey(mapent, "mat4");
				skins[num_skinfamilies].mat[5] = ValueForKey(mapent, "mat5");
				skins[num_skinfamilies].mat[6] = ValueForKey(mapent, "mat6");
				skins[num_skinfamilies].mat[7] = ValueForKey(mapent, "mat7");
				skins[num_skinfamilies].mat[8] = ValueForKey(mapent, "mat8");
				skins[num_skinfamilies].mat[9] = ValueForKey(mapent, "mat9");
				skins[num_skinfamilies].mat[10] = ValueForKey(mapent, "mat10");
				skins[num_skinfamilies].mat[11] = ValueForKey(mapent, "mat11");
				skins[num_skinfamilies].mat[12] = ValueForKey(mapent, "mat12");
				skins[num_skinfamilies].mat[13] = ValueForKey(mapent, "mat13");
				skins[num_skinfamilies].mat[14] = ValueForKey(mapent, "mat14");
				num_skinfamilies++;
			}
		}
	}
}

void model_t::MakeQC(){
	char QCfilename[1024];
	V_snprintf(QCfilename, 1024,"%s\\%s.qc", sourcefolder, qc_modelname);
	Msg("Writing %s\n", QCfilename);
	FileHandle_t QCFile;
	EnsureFileDirectoryExists(&QCfilename[0]);
	QCFile = g_pFileSystem->Open(QCfilename, "wb");

	if (!QCfilename)
	{
		Error("Failed to write to the QC file! Make sure the folder exists.");
	}

	//Staticprop doesn't preclude physics
	CmdLib_FPrintf(QCFile, "$staticprop\r\n");

	CmdLib_FPrintf(QCFile, "$modelname \"%s\"\r\n", qc_modelname);
	//might want to check and see if it's a number.
	CmdLib_FPrintf(QCFile, "$scale \"%f\"\r\n", qc_scale); 
	CmdLib_FPrintf(QCFile, "$body \"Body\" \"%s_ref\"\r\n", basename);
	CmdLib_FPrintf(QCFile, "$cdmaterials \"%s\"\r\n", qc_cdmaterials);
	CmdLib_FPrintf(QCFile, "$sequence idle \"%s_ref\"\r\n", basename);
	CmdLib_FPrintf(QCFile, "$surfaceprop \"%s\"\r\n", qc_surfaceprop);
	if (qc_autocenter){
		CmdLib_FPrintf(QCFile, "$autocenter\r\n");
	}
	else{
//		origin = origin*qc_scale; //want the origin point to move along with $scale
//		CmdLib_FPrintf(QCFile, "$origin %f %f %f\r\n", origin.y, origin.x, origin.z );
	}
	char texname[128];
	int max_skins = 1;
	if (num_skinfamilies>0){
		//Loop through first and see how many skins we'll have.
		for (int h=0; h<15; h++){
			for (int i=0; i<num_skinfamilies; i++){
				if (V_strlen(skins[i].mat[h])){
					if (h > max_skins) max_skins = h+1;
				}
			}
		}
		//Hack because I don't wanna fix the above for cases with one alt skin.
		if (max_skins == 1) max_skins = 2;

		CmdLib_FPrintf(QCFile, "$texturegroup skinfamilies {\r\n");
		for (int h=0; h<max_skins; h++){
			CmdLib_FPrintf(QCFile, "	{");
			for (int i=0; i<num_skinfamilies; i++){
				//no skin specified? ok, just use skin 0
				if (!V_strlen(skins[i].mat[h])){
					skins[i].mat[h] = skins[i].mat[0];
					//V_strcpy (&texname[0], skins[i].mat[0]); 
				}
				V_FileBase( skins[i].mat[h], &texname[0], 128);
				if (skins[i].suffix[h] > 0)	V_snprintf(&texname[0], 128, "%s(%i)", texname, skins[i].suffix[h]);
				strlwr( texname );
				CmdLib_FPrintf(QCFile, " \"%s\"", texname);
			}
			CmdLib_FPrintf(QCFile, " }\r\n");
		}
		CmdLib_FPrintf(QCFile, "}\r\n");
	}
	if (dophysmodel){
		if (qc_concave){
			CmdLib_FPrintf(QCFile, "$collisionmodel \"%s_phys\"  {\r\n	$concave\r\n", basename);
		}
		else{ //Use phys model here also because it might differ from ref.
			CmdLib_FPrintf(QCFile, "$collisionmodel \"%s_phys\"  {\r\n", basename);
		}
//VERSIONSHIT
//		CmdLib_FPrintf(QCFile, "	$maxconvexpieces %i\r\n", num_physhulls);
		if (mass > 0){
			CmdLib_FPrintf(QCFile, "	$mass %f\r\n}\r\n", mass);
		}
		else{
			CmdLib_FPrintf(QCFile, "	$automass\r\n}\r\n");
		}
	}
	//Print LODs in ascending order
	while (1){
		int lodnum = -1;
		int loddist = 9999;
		//Find the nearest
		for (int i=0; i<num_lods; i++){
			if (!lods[i].written && lods[i].distance < loddist ){
				loddist = lods[i].distance;
				lodnum = i;
			}
		}
		//if none left unwritten 
		if (lodnum == -1) break;
		CmdLib_FPrintf(QCFile, "$lod %i\r\n{\r\n", lods[lodnum].distance);
		CmdLib_FPrintf(QCFile, "	replacemodel \"%s_ref\" \"%s_lod%i\"\r\n}\r\n", basename, basename, lodnum+1);
		lods[lodnum].written = true;
	}

	if  (dobodygroup){
		CmdLib_FPrintf(QCFile, "$bodygroup %s\r\n{\r\n", bodygroups.groupname);
		for (int i=0; i<16; i++){
			if (bodygroups.body_ents[i]) CmdLib_FPrintf(QCFile, "	studio \"%s_group%i\"\r\n", basename, i+1);
		}
		CmdLib_FPrintf(QCFile, "	blank\r\n}\r\n");
		dobodygroup = false;
	}
	if (physicsprop || num_particles || num_cables){
		CmdLib_FPrintf(QCFile, "\r\n$keyvalues {\r\n");
		if (physicsprop){
			CmdLib_FPrintf(QCFile, "	\"prop_data\" {\r\n		base		%s\r\n", phy->base);
			if (phy->health>-1) CmdLib_FPrintf(QCFile, "		health		%i\r\n", phy->health);
			if (phy->physicsmode) CmdLib_FPrintf(QCFile, "		physicsmode	%i\r\n", phy->physicsmode);
			CmdLib_FPrintf(QCFile, "		allowstatic	true\r\n");

			if(phy->explosive_damage > 0 && phy->explosive_radius > 0)
				CmdLib_FPrintf(QCFile, 
				"		explosive_damage  %f\r\n"
				"		explosive_radius  %f\r\n",
				phy->explosive_damage, phy->explosive_radius);
			if(phy->flammable){
				CmdLib_FPrintf(QCFile, "		fire_interactions {\r\n			flammable	\"yes\"\r\n");
				if (phy->ignite)CmdLib_FPrintf(QCFile, "			ignite	\"halfhealth\"\r\n");
				if (phy->explosive_resist)CmdLib_FPrintf(QCFile, "			explosive_resist	\"yes\"\r\n");
				CmdLib_FPrintf(QCFile, "		}\r\n"	);
			}
			if (strlen(phy->breakable_model)>0)CmdLib_FPrintf(QCFile, "		breakable_model	%s\r\n		breakable_count	%i\r\n		breakable_skin	%i\r\n", phy->breakable_model, phy->breakable_count, phy->breakable_skin);
			CmdLib_FPrintf(QCFile,"	}\r\n");
			//Only do this if prop_data exists, because it would be stupid otherwise.
			if (phys_interactions){
				CmdLib_FPrintf(QCFile,"	physgun_interactions\r\n	{\r\n");
				if (phys_int->preferred_carryangles) CmdLib_FPrintf(QCFile,"		preferred_carryangles \"%f %f %f\"\r\n", phys_int->angles.x, phys_int->angles.y, phys_int->angles.z);
				if (phys_int->stick) CmdLib_FPrintf(QCFile,"		onworldimpact 		stick\r\n");
				if (phys_int->bloodsplat) CmdLib_FPrintf(QCFile,"		onworldimpact 		bloodsplat\r\n");
				if (phys_int->break_) CmdLib_FPrintf(QCFile,"		onfirstimpact 		break\r\n");
				if (phys_int->paintsplat) CmdLib_FPrintf(QCFile,"		onfirstimpact 		paintsplat\r\n");
				if (phys_int->impale) CmdLib_FPrintf(QCFile,"		onfirstimpact 		impale\r\n");
				if (phys_int->explode_fire) CmdLib_FPrintf(QCFile,"		onbreak 		explode_fire\r\n");
				CmdLib_FPrintf(QCFile,"		onlaunch 		%s\r\n", phys_int->onlaunch);
				CmdLib_FPrintf(QCFile,"	}\r\n");
			}
		}
		if (num_particles){
			CmdLib_FPrintf(QCFile, "	particles\r\n		{\r\n");
			for(int i=0; i<num_particles; i++){
				CmdLib_FPrintf(QCFile,"		effect\r\n		{\r\n");
				CmdLib_FPrintf(QCFile,"			name	\"%s\"\r\n", particles[i].name);
				CmdLib_FPrintf(QCFile,"			attachment_type	\"%s\"\r\n", particles[i].attachment_type);
				CmdLib_FPrintf(QCFile,"			attachment_point	\"%s\"\r\n", particles[i].attachment_point);
				CmdLib_FPrintf(QCFile,"		}\r\n", particles[i].attachment_point);
			}
			CmdLib_FPrintf(QCFile,"	}\r\n");
		}
		if (num_cables){
			CmdLib_FPrintf(QCFile, "	cables\r\n	{\r\n");
			for(int i=0; i<num_cables; i++){
				CmdLib_FPrintf(QCFile,
					"		\"Cable\"\r\n"
					"		{\r\n"
					"			\"StartAttachment\" \"%s\"\r\n"
					"			\"EndAttachment\" \"%s\"\r\n"
					"			\"Width\" \"%i\"\r\n"
					"			\"Material\" \"%s\"\r\n"
					"			\"NumSegments\" \"%i\"\r\n"
					"			\"Length\" \"%i\"\r\n"
					"		}\r\n",
					cables[i].start, cables[i].end, cables[i].width, cables[i].mat, cables[i].segments, cables[i].length);
			}
			CmdLib_FPrintf(QCFile,"	}\r\n");
		}
	CmdLib_FPrintf(QCFile,"}\r\n");//end of $keyvalues
	}
	for(int i=0; i<num_attachments; i++){
		CmdLib_FPrintf(QCFile,"$attachment \"%s\" \"\" %f %f %f absolute rigid rotate %f %f %f\r\n", att[i].name, att[i].origin.x, att[i].origin.y, att[i].origin.z, att[i].angles.x, att[i].angles.y, att[i].angles.z );
	}
	if (num_gibs){
		CmdLib_FPrintf(QCFile,"$collisiontext\r\n{\r\n");
		for(int i=0; i<num_gibs; i++){
			CmdLib_FPrintf(QCFile,"	break { %s %s debris %i burst %i fadetime %i fademindist %i fademaxdist %i }\r\n", gibs[i].ragdoll, gibs[i].gibmodel, gibs[i].debris, gibs[i].burst, gibs[i].fadetime, gibs[i].fademindist, gibs[i].fademaxdist );
		}
		CmdLib_FPrintf(QCFile,"}\r\n");
	}
	g_pFileSystem->Close(QCFile);
	Msg("Done.\n");
}


int RunVBSP( int argc, char **argv )
{
	int		i;
	double		start, end;
//	char		path[1024];

	CommandLine()->CreateCmdLine( argc, argv );
	MathLib_Init( 2.2f, 2.2f, 0.0f, OVERBRIGHT, false, false, false, false );
	InstallSpewFunction();
	SpewActivate( "developer", 1 );
	
	CmdLib_InitFileSystem( argv[ argc-1 ] );

	Q_StripExtension( ExpandArg( argv[ argc-1 ] ), source, sizeof( source ) );
	//Carl: kill any line breaks
	for (int i=0; i<strlen(source); i++){
		if (source[i] < 0x20) { //Everything below here is control/break chracters
			source[i] = 0x0; 
			break;
		}
	}
	Q_FileBase( source, mapbase, sizeof( mapbase ) );
	strlwr( mapbase );
	//basename = &mapbase[0]; //source uses the mapname as default
	//Carl
	V_memcpy(&targetPath, &source, 1024);
	V_StripFilename( &targetPath[0] );

	LoadCmdLineFromFile( argc, argv, mapbase, "vbsp" );

	Msg( "Propper 0.31 by Carl Foust. Adapted from vbsp.exe by Valve Software. (%s)\n", __DATE__ );

	for (i=1 ; i<argc ; i++)
	{
				if (!stricmp(argv[i],"-logging"))
		{
			logging = true;
		}
		else if (!stricmp(argv[i],"-nocompile"))
		{
			Msg("No Compile--Propper will not run studiomdl.\n");
			studioCompile = false;
		}
		else if (!stricmp(argv[i],"-nomaterials"))
		{
			Msg("No Materials--Propper will not convert any materials.\n");
			fixMaterials = false;
		}
		else if ( !stricmp(argv[i], "-obj") )
		{
			Msg("OBJ export enabled.\n");
			objExport = true;
		}
		#if 0
		else if (!stricmp(argv[i],"-threads"))
		{
			numthreads = atoi (argv[i+1]);
			i++;
		}
		else if (!Q_stricmp(argv[i],"-glview"))
		{
			glview = true;
		}
		else if ( !Q_stricmp(argv[i], "-v") || !Q_stricmp(argv[i], "-verbose") )
		{
			Msg("verbose = true\n");
			verbose = true;
		}
		else if (!Q_stricmp(argv[i], "-noweld"))
		{
			Msg ("noweld = true\n");
			noweld = true;
		}
		else if (!Q_stricmp(argv[i], "-nocsg"))
		{
			Msg ("nocsg = true\n");
			nocsg = true;
		}
		else if (!Q_stricmp(argv[i], "-noshare"))
		{
			Msg ("noshare = true\n");
			noshare = true;
		}
		else if (!Q_stricmp(argv[i], "-notjunc"))
		{
			Msg ("notjunc = true\n");
			notjunc = true;
		}
		else if (!Q_stricmp(argv[i], "-nowater"))
		{
			Msg ("nowater = true\n");
			nowater = true;
		}
		else if (!Q_stricmp(argv[i], "-noopt"))
		{
			Msg ("noopt = true\n");
			noopt = true;
		}
		else if (!Q_stricmp(argv[i], "-noprune"))
		{
			Msg ("noprune = true\n");
			noprune = true;
		}
		else if (!Q_stricmp(argv[i], "-nomerge"))
		{
			Msg ("nomerge = true\n");
			nomerge = true;
		}
		else if (!Q_stricmp(argv[i], "-nomergewater"))
		{
			Msg ("nomergewater = true\n");
			nomergewater = true;
		}
		else if (!Q_stricmp(argv[i], "-nosubdiv"))
		{
			Msg ("nosubdiv = true\n");
			nosubdiv = true;
		}
		else if (!Q_stricmp(argv[i], "-nodetail"))
		{
			Msg ("nodetail = true\n");
			nodetail = true;
		}
		else if (!Q_stricmp(argv[i], "-fulldetail"))
		{
			Msg ("fulldetail = true\n");
			fulldetail = true;
		}
		else if (!Q_stricmp(argv[i], "-onlyents"))
		{
			Msg ("onlyents = true\n");
			onlyents = true;
		}
		else if (!Q_stricmp(argv[i], "-onlyprops"))
		{
			Msg ("onlyprops = true\n");
			onlyprops = true;
		}
		else if (!Q_stricmp(argv[i], "-micro"))
		{
			microvolume = atof(argv[i+1]);
			Msg ("microvolume = %f\n", microvolume);
			i++;
		}
		else if (!Q_stricmp(argv[i], "-leaktest"))
		{
			Msg ("leaktest = true\n");
			leaktest = true;
		}
		else if (!Q_stricmp(argv[i], "-verboseentities"))
		{
			Msg ("verboseentities = true\n");
			verboseentities = true;
		}
		else if (!Q_stricmp(argv[i], "-snapaxial"))
		{
			Msg ("snap axial = true\n");
			g_snapAxialPlanes = true;
		}
#if 0
		else if (!Q_stricmp(argv[i], "-maxlightmapdim"))
		{
			g_maxLightmapDimension = atof(argv[i+1]);
			Msg ("g_maxLightmapDimension = %f\n", g_maxLightmapDimension);
			i++;
		}
#endif
		else if (!Q_stricmp(argv[i], "-block"))
		{
			block_xl = block_xh = atoi(argv[i+1]);
			block_yl = block_yh = atoi(argv[i+2]);
			Msg ("block: %i,%i\n", block_xl, block_yl);
			i+=2;
		}
		else if (!Q_stricmp(argv[i], "-blocks"))
		{
			block_xl = atoi(argv[i+1]);
			block_yl = atoi(argv[i+2]);
			block_xh = atoi(argv[i+3]);
			block_yh = atoi(argv[i+4]);
			Msg ("blocks: %i,%i to %i,%i\n", 
				block_xl, block_yl, block_xh, block_yh);
			i+=4;
		}
		else if ( !Q_stricmp( argv[i], "-dumpcollide" ) )
		{
			Msg("Dumping collision models to collideXXX.txt\n" );
			dumpcollide = true;
		}
		else if ( !Q_stricmp( argv[i], "-dumpstaticprop" ) )
		{
			Msg("Dumping static props to staticpropXXX.txt\n" );
			g_DumpStaticProps = true;
		}
		else if ( !Q_stricmp( argv[i], "-forceskyvis" ) )
		{
			Msg("Enabled vis in 3d skybox\n" );
			g_bSkyVis = true;
		}
		else if (!Q_stricmp (argv[i],"-tmpout"))
		{
			strcpy (outbase, "/tmp");
		}
#if 0
		else if( !Q_stricmp( argv[i], "-defaultluxelsize" ) )
		{
			g_defaultLuxelSize = atof( argv[i+1] );
			i++;
		}
#endif
		else if( !Q_stricmp( argv[i], "-luxelscale" ) )
		{
			g_luxelScale = atof( argv[i+1] );
			i++;
		}
		else if( !strcmp( argv[i], "-minluxelscale" ) )
		{
			g_minLuxelScale = atof( argv[i+1] );
			if (g_minLuxelScale < 1)
				g_minLuxelScale = 1;
			i++;
		}
		else if( !Q_stricmp( argv[i], "-dxlevel" ) )
		{
			g_nDXLevel = atoi( argv[i+1] );
			Msg( "DXLevel = %d\n", g_nDXLevel );
			i++;
		}
		else if( !Q_stricmp( argv[i], "-bumpall" ) )
		{
			g_BumpAll = true;
		}
		else if( !Q_stricmp( argv[i], "-low" ) )
		{
			g_bLowPriority = true;
		}
		else if( !Q_stricmp( argv[i], "-lightifmissing" ) )
		{
			g_bLightIfMissing = true;
		}
		else if ( !Q_stricmp( argv[i], CMDLINEOPTION_NOVCONFIG ) )
		{
		}
		else if ( !Q_stricmp( argv[i], "-allowdebug" ) || !Q_stricmp( argv[i], "-steam" ) )
		{
			// nothing to do here, but don't bail on this option
		}
#endif
		else if ( !Q_stricmp( argv[i], "-vproject" ) || !Q_stricmp( argv[i], "-game" ) )
		{
			++i;
		}
#if 0
		else if ( !Q_stricmp( argv[i], "-keepstalezip" ) )
		{
			g_bKeepStaleZip = true;
		}
		else if ( !Q_stricmp( argv[i], "-xbox" ) )
		{
			// enable mandatory xbox extensions
			g_NodrawTriggers = true;
			g_DisableWaterLighting = true;
		}
		else if ( !Q_stricmp( argv[i], "-allowdetailcracks"))
		{
			g_bAllowDetailCracks = true;
		}
		else if ( !Q_stricmp( argv[i], "-novirtualmesh"))
		{
			g_bNoVirtualMesh = true;
		}
		else if ( !Q_stricmp( argv[i], "-replacematerials" ) )
		{
			g_ReplaceMaterials = true;
		}
		else if ( !Q_stricmp(argv[i], "-nodrawtriggers") )
		{
			g_NodrawTriggers = true;
		}
		else if ( !Q_stricmp( argv[i], "-FullMinidumps" ) )
		{
			EnableFullMinidumps( true );
		}
#endif
		else if (argv[i][0] == '-')
		{
			Warning("Propper: Unknown option \"%s\"\n\n", argv[i]);
			i = 100000;	// force it to print the usage
			break;
		}
		else
			break;
	}

	if (i != argc - 1)
	{
		PrintCommandLine( argc, argv );

		Warning(	
			"usage  : propper [options...] mapfile\n"
			"example: propper -game \"c:\\program files\\steam\\steamapps\\username\\half-life 2\\hl2 c:\\maps\\test.vmf\n"
			"\n"
			"Common options (use -v to see all options):\n"
			"\n"
			"  -v (or -verbose): Turn on verbose output (also shows more command\n"
			"                    line options).\n"
			"\n"
			"  -low        : Run as an idle-priority process.\n"
			"\n"
			"  -vproject <directory> : Override the VPROJECT environment variable.\n"
			"  -game <directory>     : Same as -vproject.\n"
			"  -logging				 : enable .log file.\n"
			"  -nomaterials			 : Makes propper skip conversion of material files.\n"
			"  -nocompile			 : Makes propper skip running studiomdl to compile props.\n"
			"\n" );

/*		if ( verbose )
		{
			Warning(
				"Other options  :\n"
				"  -novconfig   : Don't bring up graphical UI on vproject errors.\n"
				"  -threads     : Control the number of threads vbsp uses (defaults to the # of\n"
				"                 processors on your machine).\n"
				"  -verboseentities: If -v is on, this disables verbose output for submodels.\n"
				"  -noweld      : Don't join face vertices together.\n"
				"  -nocsg       : Don't chop out intersecting brush areas.\n"
				"  -noshare     : Emit unique face edges instead of sharing them.\n"
				"  -notjunc     : Don't fixup t-junctions.\n"
				"  -noopt       : By default, vbsp removes the 'outer shell' of the map, which\n"
				"                 are all the faces you can't see because you can never get\n"
				"                 outside the map. -noopt disables this behaviour.\n"
				"  -noprune     : Don't prune neighboring solid nodes.\n"
				"  -nomerge     : Don't merge together chopped faces on nodes.\n"
				"  -nomergewater: Don't merge together chopped faces on water.\n"
				"  -nosubdiv    : Don't subdivide faces for lightmapping.\n"
				"  -micro <#>   : vbsp will warn when brushes are output with a volume less\n"
				"                 than this number (default: 1.0).\n"
				"  -fulldetail  : Mark all detail geometry as normal geometry (so all detail\n"
				"                 geometry will affect visibility).\n"
				"  -leaktest    : Stop processing the map if a leak is detected. Whether or not\n"
				"                 this flag is set, a leak file will be written out at\n"
				"                 <vmf filename>.lin, and it can be imported into Hammer.\n"
				"  -bumpall     : Force all surfaces to be bump mapped.\n"
				"  -snapaxial   : Snap axial planes to integer coordinates.\n"
				"  -block # #      : Control the grid size mins that vbsp chops the level on.\n"
				"  -blocks # # # # : Enter the mins and maxs for the grid size vbsp uses.\n"
				"  -dumpstaticprops: Dump static props to staticprop*.txt\n"
				"  -dumpcollide    : Write files with collision info.\n"
				"  -luxelscale #   : Scale all lightmaps by this amount (default: 1.0).\n"
				"  -minluxelscale #: No luxel scale will be lower than this amount (default: 1.0).\n"
				"  -lightifmissing : Force lightmaps to be generated for all surfaces even if\n"
				"                    they don't need lightmaps.\n"
				"  -keepstalezip   : Keep the BSP's zip files intact but regenerate everything\n"
				"                    else.\n"
				"  -virtualdispphysics : Use virtual (not precomputed) displacement collision models\n"
				"  -xbox           : Enable mandatory xbox options\n"
				"  -replacematerials : Substitute materials according to materialsub.txt in content\\maps\n"
				"  -FullMinidumps  : Write large minidumps on crash.\n"
				);
			}*/

		DeleteCmdLine( argc, argv );
		CmdLib_Cleanup();
		CmdLib_Exit( 1 );
	}

	start = Plat_FloatTime();

	// Run in the background?
	if( g_bLowPriority )
	{
		SetLowPriority();
	}

	if( ( g_nDXLevel != 0 ) && ( g_nDXLevel < 80 ) )
	{
		g_BumpAll = false;
	}

	if( g_luxelScale == 1.0f )
	{
		if ( g_nDXLevel == 70 )
		{
			g_luxelScale = 4.0f;
		}
	}

	ThreadSetDefault ();
	numthreads = 1;		// multiple threads aren't helping...

	// Setup the logfile.
	if (logging){
		char logFile[512];
		_snprintf( logFile, sizeof(logFile), "%s.log", source );
		SetSpewFunctionLogFile( logFile );
	}

//	LoadPhysicsDLL();
	LoadSurfaceProperties();

#if 0
	Msg( "qdir: %s  This is the the path of the initial source file \n", qdir );
	Msg( "gamedir: %s This is the base engine + mod-specific game dir (e.g. d:/tf2/mytfmod/) \n", gamedir );
	Msg( "basegamedir: %s This is the base engine + base game directory (e.g. e:/hl2/hl2/, or d:/tf2/tf2/ )\n", basegamedir );
#endif

	sprintf( materialPath, "%smaterials", gamedir );
	InitMaterialSystem( materialPath, CmdLib_GetFileSystemFactory() );
	Msg( "materialPath: %s\n", materialPath );
	
	// delete portal and line files
	//sprintf (path, "%s.prt", source);
	//remove (path);
	//sprintf (path, "%s.lin", source);
	//remove (path);

	strcpy (name, ExpandArg (argv[i]));	

	const char *pszExtension = V_GetFileExtension( name );
	if ( !pszExtension )
	{
		V_SetExtension( name, ".vmm", sizeof( name ) );
		if ( !FileExists( name ) )
		{
			V_SetExtension( name, ".vmf", sizeof( name ) );
		}
	}

	char platformBSPFileName[1024];
	GetPlatformMapPath( source, platformBSPFileName, g_nDXLevel, 1024 );
	
	// if we're combining materials, load the script file
	if ( g_ReplaceMaterials )
	{
		LoadMaterialReplacementKeys( gamedir, mapbase );
	}

	//
	// if onlyents, just grab the entites and resave
	//
	if (0) // onlyents
	{
		LoadBSPFile (platformBSPFileName);
		num_entities = 0;
		// Clear out the cubemap samples since they will be reparsed even with -onlyents
		g_nCubemapSamples = 0;

		// Mark as stale since the lighting could be screwed with new ents.
		AddBufferToPak( GetPakFile(), "stale.txt", "stale", strlen( "stale" ) + 1, false );

		LoadMapFile (name);
		SetModelNumbers ();
		SetLightStyles ();

		// NOTE: If we ever precompute lighting for static props in
		// vrad, EmitStaticProps should be removed here

		// Emit static props found in the .vmf file
		EmitStaticProps();

		// NOTE: Don't deal with detail props here, it blows away lighting

		// Recompute the skybox
		ComputeBoundsNoSkybox();

		// Make sure that we have a water lod control eneity if we have water in the map.
		EnsurePresenceOfWaterLODControlEntity();

		// Make sure the func_occluders have the appropriate data set
		FixupOnlyEntsOccluderEntities();

		// Doing this here because stuff abov may filter out entities
		UnparseEntities ();

		WriteBSPFile (platformBSPFileName);
	}
	else if (onlyprops)
	{
		// In the only props case, deal with static + detail props only
		LoadBSPFile (platformBSPFileName);

		LoadMapFile(name);
		SetModelNumbers();
		SetLightStyles();

		// Emit static props found in the .vmf file
		EmitStaticProps();

		// Place detail props found in .vmf and based on material properties
		LoadEmitDetailObjectDictionary( gamedir );
		EmitDetailObjects();

		WriteBSPFile (platformBSPFileName);
	}
	else
	{
		//
		// start from scratch
		//

		// Load just the file system from the bsp
		if( g_bKeepStaleZip && FileExists( platformBSPFileName ) )
		{
			LoadBSPFile_FileSystemOnly (platformBSPFileName);
			// Mark as stale since the lighting could be screwed with new ents.
			AddBufferToPak( GetPakFile(), "stale.txt", "stale", strlen( "stale" ) + 1, false );
		}

		LoadMapFile (name);
		WorldVertexTransitionFixup();
		if( ( g_nDXLevel == 0 ) || ( g_nDXLevel >= 70 ) )
		{
			Cubemap_FixupBrushSidesMaterials();
			Cubemap_AttachDefaultCubemapToSpecularSides();
			Cubemap_AddUnreferencedCubemaps();
		}
		SetModelNumbers ();
		SetLightStyles ();
		LoadEmitDetailObjectDictionary( gamedir );
		ProcessModels ();
				
		//char basename[128];//Not used?
		if (!sourcefolder) sourcefolder = &targetPath[0];//put source files in with vmf by default.
		char SMDfilename[1024];
		char QCfilename[1024];
		char studioCommand[1024];
//		entity_t *mapent = &entities[num_entities];
		for (int i=0; i<num_models; i++){
			model_t* m = &propper_models[i];

			if (!strlen(m->qc_modelname)){
				Warning("propper_model encountered with no \"Model Name\". Skipping...\n");
				continue;
			}
			Msg("===============================\n");
			Msg("Creating model: \"%s\"\n", m->qc_modelname);
			Msg("===============================\n");
			//mat_nonormal is a global, but change it for each model.
			mat_nonormal = IntForKey(EntityByName2(m->ent_name), "mat_nonormal") !=0;
			propper_models[i].getMapProperties();
			//Use the ref. as collision if the chosen physics entity can't be found
			if (m->phys_entnum == 0)m->phys_entnum = m->ref_entnum;
			if (objExport) V_snprintf(&SMDfilename[0], 1024,"%s\\%s_ref.obj", sourcefolder, m->qc_modelname);
			else V_snprintf(&SMDfilename[0], 1024,"%s\\%s_ref.smd", sourcefolder, m->qc_modelname);
			MakeSMD(false, &SMDfilename[0], m->ref_entnum, m->ref_weldvertices, m);

			for (int i=0; i<m->num_lods; i++){
				if (objExport) V_snprintf(SMDfilename, 1024,"%s\\%s_lod%i.obj", sourcefolder, m->qc_modelname, i+1);
				else V_snprintf(SMDfilename, 1024,"%s\\%s_lod%i.smd", sourcefolder, m->qc_modelname, i+1);
				MakeSMD(false, &SMDfilename[0], m->lods[i].entnum, m->lods[i].weldvertices, m);
			}
			if (m->physicsprop || strlen(m->phys_entname)){
				m->dophysmodel = true;
				//OBJ is not an option here, studiomdl don't like.
				V_snprintf(SMDfilename, 1024,"%s\\%s_phys.smd", sourcefolder, m->qc_modelname);
				MakeSMD(true, &SMDfilename[0], m->phys_entnum, 0.01, m);
			}
			if (dobodygroup){
				for (int i=0; i<16; i++){
					if (bodygroups.body_ents[i]){
						if (objExport) V_snprintf(SMDfilename, 1024,"%s\\%s_group%i.obj", sourcefolder, m->qc_modelname, i+1);
						else V_snprintf(SMDfilename, 1024,"%s\\%s_group%i.smd", sourcefolder, m->qc_modelname, i+1);
						MakeSMD(false, &SMDfilename[0], bodygroups.body_ents[i], m->ref_weldvertices, m);
					}
				}
			}
			m->MakeQC();
			//Fixup any alternate skins we got.
			if (m->num_skinfamilies>0 && fixMaterials){
				Msg("Converting Alternate skins...\n");
				for (int h=0; h<15; h++){
					for (int i=0; i<m->num_skinfamilies; i++){
						if (V_strlen(m->skins[i].mat[h])){
							m->skins[i].suffix[h] = fixupMaterial(m->skins[i].mat[h], m->qc_cdmaterials, false);
						}
					}
				}
			}
			if (studioCompile){
				V_snprintf(QCfilename, 1024,"%s\\%s.qc", sourcefolder, m->qc_modelname);
				V_StripTrailingSlash( &gamedir[0] );
				V_snprintf(studioCommand, 1024,"studiomdl.exe -fullcollide -game \"%s\" \"%s\"", gamedir, QCfilename);
				Q_AppendSlash( gamedir, sizeof( gamedir ) );//So retarded
				Msg("Compiling the model:\n");
				Msg(studioCommand);
				Msg("\n---Please Wait---\n");
	//			Msg("Studiomdl output proceeds below...\n\n----------------------\n");

				STARTUPINFO si;
				PROCESS_INFORMATION pi;
				ZeroMemory( &si, sizeof(si) );
				si.cb = sizeof(si);
				ZeroMemory( &pi, sizeof(pi) );
				/*
				http://msdn.microsoft.com/en-us/library/ms682425(v=VS.85).aspx
				BOOL WINAPI CreateProcess(
				  __in_opt     LPCTSTR lpApplicationName,
				  __inout_opt  LPTSTR lpCommandLine,
				  __in_opt     LPSECURITY_ATTRIBUTES lpProcessAttributes,
				  __in_opt     LPSECURITY_ATTRIBUTES lpThreadAttributes,
				  __in         BOOL bInheritHandles,
				  __in         DWORD dwCreationFlags,
				  __in_opt     LPVOID lpEnvironment,
				  __in_opt     LPCTSTR lpCurrentDirectory,
				  __in         LPSTARTUPINFO lpStartupInfo,
				  __out        LPPROCESS_INFORMATION lpProcessInformation
				};
				*/
				if (!CreateProcess(
					NULL,
					studioCommand,
					NULL,
					NULL,
					false,
					0x00000000, 
					NULL,
					NULL, 
					&si,            // Pointer to STARTUPINFO structure
					&pi )           // Pointer to PROCESS_INFORMATION structure
					) Error("Studiomdl could not start!\n");
				// Wait until child process exits.
				WaitForSingleObject( pi.hProcess, INFINITE );

				// Close process and thread handles. 
				CloseHandle( pi.hProcess );
				CloseHandle( pi.hThread );
	//			Msg("\n----------------------\n");
				Msg("Studiomdl complete!\n");
			}
		}
	}

	end = Plat_FloatTime();
	
	char str[512];
	GetHourMinuteSecondsString( (int)( end - start ), str, sizeof( str ) );
	Msg( "%s elapsed\n", str );

	DeleteCmdLine( argc, argv );
	ReleasePakFileLumps();
	DeleteMaterialReplacementKeys();
	ShutdownMaterialSystem();
	CmdLib_Cleanup();
	return 0;
}


/*
=============
main
============
*/
int main (int argc, char **argv)
{
	// Install an exception handler.
	SetupDefaultToolsMinidumpHandler();
	return RunVBSP( argc, argv );
}


