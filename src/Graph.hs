{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Graph where

import Control.Monad (forM_, when)
import Data.List (foldl')
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Numeric.Natural (Natural)
import Reduction (FlowEquiv (..), Matrix, Reducible (..))
import Render (Render (..))

newtype Vertex = Vertex Natural deriving (Eq, Ord, Enum, Show)

newtype Edge = Edge Natural deriving (Eq, Ord, Enum, Show)

instance Render Vertex where render (Vertex i) = "v_{" ++ show i ++ "}"

instance Render Edge where render (Edge i) = "e_{" ++ show i ++ "}"

data Graph = Graph
  { vertices :: Set Vertex,
    edges :: Set Edge,
    source :: Map Edge Vertex,
    range :: Map Edge Vertex,
    invSource :: Map Vertex (Set Edge),
    invRange :: Map Vertex (Set Edge)
  }
  deriving (Show, Eq)

empty :: Graph
empty =
  Graph
    { vertices = Set.empty,
      edges = Set.empty,
      source = Map.empty,
      range = Map.empty,
      invSource = Map.empty,
      invRange = Map.empty
    }

insVertex :: Vertex -> Graph -> Graph
insVertex v g
  | v `Set.member` vertices g = g
  | otherwise =
    g
      { vertices = Set.insert v (vertices g),
        invSource = Map.insert v Set.empty (invSource g),
        invRange = Map.insert v Set.empty (invRange g)
      }

insEdge ::
  Vertex ->
  Edge ->
  Vertex ->
  Graph ->
  Graph
insEdge v1 e v2 g
  | not (v1 `Set.member` vertices g) = insEdge v1 e v2 (insVertex v1 g)
  | not (v2 `Set.member` vertices g) = insEdge v1 e v2 (insVertex v2 g)
  | e `Set.member` edges g,
    Map.lookup e (source g) == Just v1,
    Map.lookup e (range g) == Just v2 =
    g
  | e `Set.member` edges g = error "Inconsistent edge"
  | otherwise =
    g
      { edges = Set.insert e (edges g),
        source = Map.insert e v1 (source g),
        range = Map.insert e v2 (range g),
        invSource = Map.update (Just . Set.insert e) v1 (invSource g),
        invRange = Map.update (Just . Set.insert e) v2 (invRange g)
      }

delVertex ::
  Vertex ->
  Graph ->
  Graph
delVertex v g
  | not (v `Set.member` vertices g) = g
  | otherwise =
    g
      { vertices = Set.delete v (vertices g),
        edges = Set.difference (edges g) adjacentEdges,
        source = Set.foldl' (flip Map.delete) (source g) adjacentEdges,
        range = Set.foldl' (flip Map.delete) (range g) adjacentEdges,
        invSource =
          Set.foldl'
            (flip $ Map.update $ Just . (`Set.difference` incoming))
            (Map.delete v (invSource g))
            ( Set.delete v $
                Set.foldl'
                  (\s -> (`Set.insert` s) . (source g Map.!))
                  Set.empty
                  incoming
            ),
        invRange =
          Set.foldl'
            (flip $ Map.update $ Just . (`Set.difference` outgoing))
            (Map.delete v (invRange g))
            ( Set.delete v $
                Set.foldl'
                  (\s -> (`Set.insert` s) . (range g Map.!))
                  Set.empty
                  outgoing
            )
      }
  where
    outgoing = invSource g Map.! v
    incoming = invRange g Map.! v
    adjacentEdges = outgoing `Set.union` incoming

delEdge ::
  Edge ->
  Graph ->
  Graph
delEdge e g
  | not (e `Set.member` edges g) = g
  | otherwise =
    g
      { edges = Set.delete e (edges g),
        source = Map.delete e (source g),
        range = Map.delete e (range g),
        invSource =
          Map.update (Just . Set.delete e) (source g Map.! e) (invSource g),
        invRange =
          Map.update (Just . Set.delete e) (range g Map.! e) (invRange g)
      }

renameVertices ::
  (Vertex -> Vertex) ->
  Graph ->
  Graph
renameVertices f g =
  g
    { vertices = Set.map f (vertices g),
      source = Map.map f (source g),
      range = Map.map f (range g),
      invSource = Map.mapKeys f (invSource g),
      invRange = Map.mapKeys f (invRange g)
    }

isConsistent :: Graph -> Bool
isConsistent g =
  edges g == Map.keysSet (source g)
    && edges g == Map.keysSet (range g)
    && all (`Set.member` vertices g) (Map.elems (source g))
    && all (`Set.member` vertices g) (Map.elems (range g))
    && vertices g == Map.keysSet (invSource g)
    && vertices g == Map.keysSet (invRange g)
    && all invSourceConsistent (Set.elems (vertices g))
    && all invRangeConsistent (Set.elems (vertices g))
  where
    invSourceConsistent v =
      invSource g Map.! v == Set.filter (\e -> source g Map.! e == v) (edges g)
    invRangeConsistent v =
      invRange g Map.! v == Set.filter (\e -> range g Map.! e == v) (edges g)

printGraph :: Graph -> IO ()
printGraph g = do
  forM_ (edges g) $ \e ->
    putStrLn
      ( render (source g Map.! e)
          ++ " -- "
          ++ render e
          ++ " --> "
          ++ render (range g Map.! e)
      )
  forM_ (vertices g) $ \v ->
    when (Set.null (invSource g Map.! v) && null (invRange g Map.! v)) $
      putStrLn (render v ++ " (isolated)")

freshVertices :: Graph -> [Vertex]
freshVertices g = case Set.lookupMax (vertices g) of
  Just v -> tail (iterate succ v)
  Nothing -> iterate succ (toEnum 0)

freshEdges :: Graph -> [Edge]
freshEdges g = case Set.lookupMax (edges g) of
  Just v -> tail (iterate succ v)
  Nothing -> iterate succ (toEnum 0)

newtype Path = Path (Either Vertex [Edge]) deriving (Eq, Ord, Show)

instance Render Path where
  render (Path (Left v)) = render v
  render (Path (Right es)) = unwords (map render es)

class IsPath p where
  toPath :: p -> Path

instance IsPath Vertex where
  toPath v = Path (Left v)

instance IsPath Edge where
  toPath e = Path (Right [e])

instance IsPath Path where
  toPath = id

pathLen :: Path -> Int
pathLen (Path (Left _)) = 0
pathLen (Path (Right es)) = length es

pathSource :: Graph -> Path -> Vertex
pathSource _ (Path (Left v)) = v
pathSource g (Path (Right es)) = source g Map.! head es

pathRange :: Graph -> Path -> Vertex
pathRange _ (Path (Left v)) = v
pathRange g (Path (Right es)) = range g Map.! last es

concatPaths :: Graph -> Path -> Path -> Maybe Path
concatPaths g p q | pathRange g p /= pathSource g q = Nothing
concatPaths _ (Path (Left _)) q = Just q
concatPaths _ p (Path (Left _)) = Just p
concatPaths _ (Path (Right es)) (Path (Right fs)) = Just (Path (Right (es ++ fs)))

edgesBetween :: Graph -> Vertex -> Vertex -> Set Edge
edgesBetween g s r =
  (invSource g Map.! s) `Set.intersection` (invRange g Map.! r)

fromAMinusI :: Matrix Integer -> Graph
fromAMinusI m =
  foldl' addEdges g0 [(s, r) | s <- vs, r <- vs]
  where
    vs = [Vertex i | i <- [0 .. size m - 1]]
    g0 = foldl' (flip insVertex) empty vs

    addEdges :: Graph -> (Vertex, Vertex) -> Graph
    addEdges g1 (Vertex s, Vertex r) =
      foldl'
        (\g e -> insEdge (Vertex s) e (Vertex r) g)
        g1
        ( take
            (fromIntegral (m ! (s, r)) + if s == r then 1 else 0)
            (freshEdges g1)
        )

-- | A graph is reducible to a canonical form by running Franks' matrix
-- algorithm on the matrix A - I.  The row and column operations are interpreted
-- as graph moves.
instance Reducible Graph where
  size g = fromIntegral $ Set.size (vertices g)

  g ! (i, j) =
    fromIntegral
      ( Set.size
          ( edgesBetween
              g
              (Set.elemAt (fromIntegral i) (vertices g))
              (Set.elemAt (fromIntegral j) (vertices g))
          )
      )
      - if i == j then 1 else 0

  rowMove r s g0 =
    foldl'
      (\g (f, e') -> insEdge vs e' (range g Map.! f) g)
      (delEdge moveEdge g0)
      newEdges
    where
      vr = Set.elemAt (fromIntegral r) (vertices g0)
      vs = Set.elemAt (fromIntegral s) (vertices g0)
      moveEdge = Set.findMin (edgesBetween g0 vs vr)
      outgoing = Set.toList (invSource g0 Map.! vr)
      newEdges = zip outgoing (freshEdges g0)

  rowUnmove r s g0 =
    insEdge vs unmoveEdge vr $
      foldl'
        ( \g f ->
            delEdge (Set.findMax (edgesBetween g vs (range g Map.! f))) g
        )
        g0
        outgoing
    where
      vr = Set.elemAt (fromIntegral r) (vertices g0)
      vs = Set.elemAt (fromIntegral s) (vertices g0)
      unmoveEdge = head (freshEdges g0)
      outgoing = Set.toList (invSource g0 Map.! vr)

  columnMove s r g0 =
    foldl'
      (\g (f, e') -> insEdge (source g Map.! f) e' vr g)
      (delEdge moveEdge g0)
      newEdges
    where
      vr = Set.elemAt (fromIntegral r) (vertices g0)
      vs = Set.elemAt (fromIntegral s) (vertices g0)
      moveEdge = Set.findMin (edgesBetween g0 vs vr)
      incoming = Set.toList (invRange g0 Map.! vs)
      newEdges = zip incoming (freshEdges g0)

  columnUnmove s r g0 =
    insEdge vs unmoveEdge vr $
      foldl'
        ( \g f ->
            delEdge (Set.findMax (edgesBetween g (source g Map.! f) vr)) g
        )
        g0
        incoming
    where
      vr = Set.elemAt (fromIntegral r) (vertices g0)
      vs = Set.elemAt (fromIntegral s) (vertices g0)
      unmoveEdge = head (freshEdges g0)
      incoming = Set.toList (invRange g0 Map.! vs)

instance FlowEquiv Graph where
  splitTopCorner g0 =
    foldl'
      dupIncoming
      (foldl' moveOutgoing (insVertex w g0) (Set.toList otherOutgoing))
      (Map.toList newIncoming)
    where
      v = Set.elemAt 0 (vertices g0)
      w = head (freshVertices g0)
      loop = Set.findMin (edgesBetween g0 v v)
      otherOutgoing = Set.delete loop (invSource g0 Map.! v)
      incoming = invRange g0 Map.! v
      newIncoming = Map.fromList (zip (Set.toList incoming) (freshEdges g0))
      moveOutgoing g e = insEdge w e (range g Map.! e) (delEdge e g)
      dupIncoming g (oldE, newE) = insEdge (source g Map.! oldE) newE w g

  deleteSource p g = delVertex (Set.elemAt (fromIntegral p) (vertices g)) g