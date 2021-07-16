module Iso where

import Data.Foldable (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import Graph
import Leavitt
import Reduction (FlowEquiv (..), Reducible (..))

-- During reduction, keeps track of a source graph E, projection p in L(E),
-- range graph F, and a star-isomorphism h from p L(E) p to h(p) L(F) h(p).
data CornerIso = CornerIso
  { isoSource :: Graph,
    isoProjection :: LPA Int,
    isoRange :: Graph,
    isoMap :: LPA Int -> LPA Int,
    isoInverseMap :: LPA Int -> LPA Int
  }

-- A CornerIso representing the identity map.
identityIso :: Graph -> CornerIso
identityIso g =
  CornerIso
    { isoSource = g,
      isoProjection = Pure 1,
      isoRange = g,
      isoMap = id,
      isoInverseMap = id
    }

-- Composes an isomorphism f from p L(E) p to f(p) L(E) f(p), and an isomorphism
-- g from q L(F) q -> g(q) L(G) g(q), to get an isomorphism (g . f) from
-- p L(E) p to g(q * f(p)) L(G) g(q * f(p)).
composeIso :: CornerIso -> CornerIso -> CornerIso
composeIso iso1 iso2 =
  CornerIso
    { isoSource = isoSource iso1,
      isoProjection = isoProjection iso1,
      isoRange = isoRange iso2,
      isoMap = isoMap iso2 . isoMap iso1,
      isoInverseMap = isoInverseMap iso1 . isoInverseMap iso2
    }

instance Reducible CornerIso where
  size iso = fromIntegral $ Set.size (vertices (isoRange iso))

  iso ! (i, j) =
    fromIntegral $
      Set.size
        ( (invSource (isoRange iso) Map.! s)
            `Set.intersection` (invRange (isoRange iso) Map.! r)
        )
    where
      s = Vertex i
      r = Vertex j

  rowMove r s iso =
    iso
      `composeIso` CornerIso
        { isoSource = isoRange iso,
          isoProjection = Pure 1,
          isoRange = newGraph,
          isoMap = starMap (isoRange iso) vertMap edgeMap,
          isoInverseMap = starMap newGraph invVertMap invEdgeMap
        }
    where
      vr = Set.elemAt (fromIntegral r) (vertices (isoRange iso))
      vs = Set.elemAt (fromIntegral s) (vertices (isoRange iso))
      moveEdge = Set.findMin (edgesBetween (isoRange iso) vs vr)
      outgoing = Set.toList (invSource (isoRange iso) Map.! vr)
      newEdges = zip outgoing (freshEdges (isoRange iso))
      invNewEdges = Map.fromList [(v, k) | (k, v) <- newEdges]

      newGraph =
        foldl'
          (\g (f, e') -> insEdge vs e' (range g Map.! f) g)
          (delEdge moveEdge (isoRange iso))
          newEdges

      vertMap v = vertex newGraph v
      edgeMap e
        | e == moveEdge =
          sum [edge newGraph e' * star (edge newGraph f) | (f, e') <- newEdges]
        | otherwise = edge newGraph e

      invVertMap v = vertex (isoSource iso) v
      invEdgeMap e
        | e `Map.member` invNewEdges =
          edge (isoSource iso) moveEdge
            * edge (isoSource iso) (invNewEdges Map.! e)
        | otherwise = edge (isoSource iso) e

  rowUnmove r s iso =
    iso
      `composeIso` CornerIso
        { isoSource = isoRange iso,
          isoProjection = Pure 1,
          isoRange = newGraph,
          isoMap = undefined,
          isoInverseMap = undefined
        }
    where
      vr = Set.elemAt (fromIntegral r) (vertices (isoRange iso))
      vs = Set.elemAt (fromIntegral s) (vertices (isoRange iso))
      unmoveEdge = head (freshEdges (isoRange iso))
      outgoing = Set.toList (invSource (isoRange iso) Map.! vr)

      newGraph =
        insEdge vs unmoveEdge vr $
          foldl'
            ( \g f ->
                delEdge (Set.findMax (edgesBetween g vs (range g Map.! f))) g
            )
            (isoRange iso)
            outgoing

  columnMove _p _q iso =
    iso
      `composeIso` CornerIso
        { isoSource = undefined,
          isoProjection = undefined,
          isoRange = undefined,
          isoMap = undefined,
          isoInverseMap = undefined
        }

  columnUnmove _p _q iso =
    iso
      `composeIso` CornerIso
        { isoSource = undefined,
          isoProjection = undefined,
          isoRange = undefined,
          isoMap = undefined,
          isoInverseMap = undefined
        }

instance FlowEquiv CornerIso where
  splitTopCorner iso =
    iso
      `composeIso` CornerIso
        { isoSource = isoRange iso,
          isoProjection = Pure 1,
          isoRange = newGraph,
          isoMap = starMap (isoRange iso) vertMap edgeMap,
          isoInverseMap = starMap newGraph invVertMap invEdgeMap
        }
    where
      newGraph = undefined
      vertMap = undefined
      edgeMap = undefined
      invVertMap = undefined
      invEdgeMap = undefined

  deleteSource p iso =
    iso
      `composeIso` CornerIso
        { isoSource = isoRange iso,
          isoProjection = 1 - vertex (isoRange iso) sourceVertex,
          isoRange = newGraph,
          isoMap = starMap (isoRange iso) vertMap edgeMap,
          isoInverseMap = starMap newGraph invVertMap invEdgeMap
        }
    where
      sourceVertex = Set.elemAt (fromIntegral p) (vertices (isoRange iso))
      newGraph = delVertex sourceVertex (isoRange iso)
      vertMap = vertex newGraph
      edgeMap = edge newGraph
      invVertMap = vertex (isoRange iso)
      invEdgeMap = edge (isoRange iso)
