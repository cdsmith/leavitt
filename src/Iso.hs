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
          isoMap = starMap (isoSource iso) vertMap edgeMap,
          isoInverseMap = starMap newGraph invVertMap invEdgeMap
        }
    where
      moveEdge =
        Set.findMin
          ( edgesBetween
              (isoRange iso)
              (Set.elemAt (fromIntegral s) (vertices (isoRange iso)))
              (Set.elemAt (fromIntegral r) (vertices (isoRange iso)))
          )
      outgoing =
        Set.toList
          ( invSource (isoRange iso)
              Map.! Set.elemAt (fromIntegral r) (vertices (isoRange iso))
          )

      newEdges = Map.fromList (zip outgoing (freshEdges (isoRange iso)))
      invNewEdges = Map.fromList [(v, k) | (k, v) <- Map.toList newEdges]

      newGraph =
        foldl'
          ( \g (f, e') ->
              insEdge
                (Set.elemAt (fromIntegral s) (vertices (isoRange iso)))
                e'
                (range (isoRange iso) Map.! f)
                g
          )
          (delEdge moveEdge (isoRange iso))
          (Map.toList newEdges)

      vertMap v = vertex newGraph v
      edgeMap e
        | e == moveEdge =
          sum
            [ edge newGraph e' * starEdge newGraph f
              | (f, e') <- Map.toList newEdges
            ]
        | otherwise = edge newGraph e

      invVertMap v = vertex (isoSource iso) v
      invEdgeMap e
        | e `Map.member` invNewEdges =
          edge (isoSource iso) moveEdge
            * edge (isoSource iso) (invNewEdges Map.! e)
        | otherwise = edge (isoSource iso) e

  rowUnmove _p _q iso =
    iso
      `composeIso` CornerIso
        { isoSource = undefined,
          isoProjection = undefined,
          isoRange = undefined,
          isoMap = undefined,
          isoInverseMap = undefined
        }

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
        { isoSource = undefined,
          isoProjection = undefined,
          isoRange = undefined,
          isoMap = undefined,
          isoInverseMap = undefined
        }

  deleteSource _p iso =
    iso
      `composeIso` CornerIso
        { isoSource = undefined,
          isoProjection = undefined,
          isoRange = undefined,
          isoMap = undefined,
          isoInverseMap = undefined
        }
