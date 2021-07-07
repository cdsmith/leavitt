module Iso where

import qualified Data.Map as Map
import qualified Data.Set as Set
import Graph
import Leavitt
import Reduction (FlowEquiv (..), Reducible (..))

-- Represents a choice of corner p L(E) p of a Leavitt path algebra, where p
-- is a projection of the graph.
data Corner = Corner
  { cornerGraph :: Graph,
    cornerProjection :: LPA Int
  }

-- During reduction, keeps track of the range graph F, and a star-isomorphism
-- from L(F) to p L(E) p, for some projection p which can change as graph moves
-- are added.
--
-- isoMap gives a map to the *inner* element, so if isoMap x = y, then the true
-- isomorphism maps x to p y p.
--
-- Because this is a star isomorphism, one only needs to know where each vertex
-- and edge maps.
data IsoToCorner = IsoToCorner
  { isoSource :: Graph,
    isoRange :: Corner,
    isoMap :: LPA Int -> LPA Int
  }

identityIsoToCorner :: Graph -> IsoToCorner
identityIsoToCorner g =
  IsoToCorner
    { isoSource = g,
      isoRange = Corner g (Pure 1),
      isoMap = id
    }

-- Composes an isomorphism from L(F) to p L(E) p, with an isomorphism from
-- L(G) -> q L(F) q, to get an isomorphism from L(G) -> p q' L(E) p q', where
-- q' is the image of q under the first isomorphism.
composeIsoToCorner :: IsoToCorner -> IsoToCorner -> IsoToCorner
composeIsoToCorner iso1 iso2 =
  IsoToCorner
    { isoSource = isoSource iso2,
      isoRange = let Corner g1 p1 = isoRange iso1
                     Corner _ p2 = isoRange iso2
                 in Corner g1 (p1 * isoMap iso1 p2),
      isoMap = isoMap iso1 . isoMap iso2
    }

instance Reducible IsoToCorner where
  size iso = fromIntegral $ Set.size (vertices (isoSource iso))

  iso ! (i, j) =
    fromIntegral $
      Set.size
        ( (invSource (isoSource iso) Map.! s)
            `Set.intersection` (invRange (isoSource iso) Map.! r)
        )
    where
      s = Vertex i
      r = Vertex j

  rowMove _p _q _iso =
    IsoToCorner
      { isoSource = undefined,
        isoRange = undefined,
        isoMap = undefined
      }

  rowUnmove _p _q _iso =
    IsoToCorner
      { isoSource = undefined,
        isoRange = undefined,
        isoMap = undefined
      }

  columnMove _p _q _iso =
    IsoToCorner
      { isoSource = undefined,
        isoRange = undefined,
        isoMap = undefined
      }

  columnUnmove _p _q _iso =
    IsoToCorner
      { isoSource = undefined,
        isoRange = undefined,
        isoMap = undefined
      }

instance FlowEquiv IsoToCorner where
  splitTopCorner _iso =
    IsoToCorner
    { isoSource = undefined,
      isoRange = undefined,
      isoMap = undefined
    }

  deleteSource _p _iso =
    IsoToCorner
    { isoSource = undefined,
      isoRange = undefined,
      isoMap = undefined
    }
