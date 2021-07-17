module CornerIso where

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
        { isoSource = g0,
          isoProjection = Pure 1,
          isoRange = newGraph,
          isoMap = starMap g0 vertMap edgeMap,
          isoInverseMap = starMap newGraph invVertMap invEdgeMap
        }
    where
      g0 = isoRange iso
      vr = Set.elemAt (fromIntegral r) (vertices g0)
      vs = Set.elemAt (fromIntegral s) (vertices g0)
      moveEdge = Set.findMin (edgesBetween g0 vs vr)
      outgoing = Set.toList (invSource g0 Map.! vr)
      newEdges = zip outgoing (freshEdges g0)
      invNewEdges = Map.fromList [(v, k) | (k, v) <- newEdges]

      newGraph =
        foldl'
          (\g (f, e') -> insEdge vs e' (range g Map.! f) g)
          (delEdge moveEdge g0)
          newEdges

      vertMap v = vertex newGraph v
      edgeMap e
        | e == moveEdge =
          sum [edge newGraph e' * star (edge newGraph f) | (f, e') <- newEdges]
        | otherwise = edge newGraph e

      invVertMap v = vertex g0 v
      invEdgeMap e
        | e `Map.member` invNewEdges =
          edge g0 moveEdge * edge g0 (invNewEdges Map.! e)
        | otherwise = edge g0 e

  rowUnmove r s iso =
    iso
      `composeIso` CornerIso
        { isoSource = g0,
          isoProjection = Pure 1,
          isoRange = newGraph,
          isoMap = starMap g0 vertMap edgeMap,
          isoInverseMap = starMap newGraph invVertMap invEdgeMap
        }
    where
      g0 = isoRange iso
      vr = Set.elemAt (fromIntegral r) (vertices g0)
      vs = Set.elemAt (fromIntegral s) (vertices g0)
      unmoveEdge = head (freshEdges g0)
      outgoing =
        Map.fromListWith (++) $
          [(range g0 Map.! e, [e]) | e <- Set.toList (invSource g0 Map.! vr)]
      oldEdges =
          concatMap
            (\v -> zip (outgoing Map.! v) (Set.toList (edgesBetween g0 vs v)))
            (Map.keys outgoing)
      invOldEdges = Map.fromList [(v, k) | (k, v) <- oldEdges]

      newGraph =
        insEdge vs unmoveEdge vr $ foldl' (flip delEdge) g0 (map snd oldEdges)

      vertMap v = vertex newGraph v
      edgeMap e
        | e `Map.member` invOldEdges =
          edge g0 unmoveEdge * edge g0 (invOldEdges Map.! e)
        | otherwise = edge g0 e

      invVertMap v = vertex g0 v
      invEdgeMap e
        | e == unmoveEdge =
          sum [edge newGraph e' * star (edge newGraph f) | (f, e') <- oldEdges]
        | otherwise = edge newGraph e

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
