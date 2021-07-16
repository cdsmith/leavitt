{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Reduction where

import Data.Coerce (coerce)
import Data.Functor.Identity (Identity (Identity))
import Data.List (foldl', (\\))
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Vector (Vector)
import qualified Data.Vector as Vector
import GHC.Stack (HasCallStack)
import Linear (Additive, (*^), (^+^))
import Numeric.Natural (Natural)

class Reducible m where
  -- | Returns the size of the square matrix.
  size :: m -> Natural

  -- | Accesses one element of the matrix.
  (!) :: m -> (Natural, Natural) -> Integer

  -- | Adds row p to row q.  Requires that p =/= q, and a_{qp} > 0.
  --
  -- See Franks (1984) Lemma 2.1 and Corollary 2.2
  rowMove ::
    HasCallStack =>
    -- | row to add
    Natural ->
    -- | row to add it to
    Natural ->
    m ->
    m
  rowMove = addKTimesRowToRow 1

  -- | Subtracts row p from row q.  Requires that p =/= q, and a_{qp} > 0 after
  -- the subtraction.
  --
  -- See Franks (1984) Lemma 2.1 and Corollary 2.2
  rowUnmove ::
    HasCallStack =>
    -- | row to subtract
    Natural ->
    -- | row to subtract it from
    Natural ->
    m ->
    m
  rowUnmove = addKTimesRowToRow (-1)

  -- | Adds column p to column q.  Requires that p =/= q, and a_{pq} > 0.
  --
  -- See Franks (1984) Lemma 2.1 and Corollary 2.2
  columnMove ::
    HasCallStack =>
    -- | column to add
    Natural ->
    -- | column to add it to
    Natural ->
    m ->
    m
  columnMove = addKTimesColToCol 1

  -- | Subtracts column p from column q.  Requires that p =/= q, and a_{pq} > 0
  -- after the subtraction.
  --
  -- See Franks (1984) Lemma 2.1 and Corollary 2.2
  columnUnmove ::
    HasCallStack =>
    -- | column to subtract
    Natural ->
    -- | column to subtract it from
    Natural ->
    m ->
    m
  columnUnmove = addKTimesColToCol (-1)

  -- | Adds a multiple of a row to another row.  Requires the matrix to be
  -- non-negative.
  --
  -- See Franks (1984) Theorem 2.4
  addKTimesRowToRow ::
    HasCallStack =>
    -- | k
    Integer ->
    -- | row to add
    Natural ->
    -- | row to add it to
    Natural ->
    m ->
    m
  addKTimesRowToRow k q p m0
    | k > 0 = addKTimesRowToRow (k - 1) q p addedRowToRow
    | k < 0 = addKTimesRowToRow (k + 1) q p subtractedRowFromRow
    | otherwise = m0
    where
      addedRowToRow =
        let is = shortestPath p q m0
         in foldl'
              subRow
              (foldl' addRow m0 (tail is))
              (tail (reverse (tail is)))
      subtractedRowFromRow =
        let m' = addKTimesElemToElem (-1) q p (toMatrix m0)
            is = shortestPath p q m'
         in foldl'
              subRow
              (foldl' addRow m0 (init (tail is)))
              (reverse (tail is))
      addRow m i = rowMove i p m
      subRow m i = rowUnmove i p m

  -- | Adds a multiple of a column to another column.
  --
  -- See Franks (1984) Theorem 2.4
  addKTimesColToCol ::
    HasCallStack =>
    -- | k
    Integer ->
    -- | column to add
    Natural ->
    -- | column to add it to
    Natural ->
    m ->
    m
  addKTimesColToCol k p q = unTranspose . addKTimesRowToRow k p q . Transpose

  {-# MINIMAL
    size,
    (!),
    (rowMove, rowUnmove | addKTimesRowToRow),
    (columnMove, columnUnmove | addKTimesColToCol)
    #-}

class Reducible m => FlowEquiv m where
  -- | Increases the size of a matrix by splitting the first row and replicating
  -- the first column.  The top left corner of the matrix must be strictly
  -- positive.
  --
  -- See Franks (1984) Proposition 1.7
  splitTopCorner :: HasCallStack => m -> m

  -- | Deletes a source from the matrix.  Requires that column p is entirely
  -- zero, except that a_{pp} is -1.
  --
  -- See Franks (1984) Remark 1.8
  deleteSource ::
    HasCallStack =>
    -- | column to delete
    Natural ->
    m ->
    m

newtype Transpose a = Transpose {unTranspose :: a}

instance Reducible a => Reducible (Transpose a) where
  size = size . unTranspose
  m ! (i, j) = unTranspose m ! (j, i)
  rowMove p q = Transpose . columnMove p q . unTranspose
  rowUnmove p q = Transpose . columnUnmove p q . unTranspose
  columnMove p q = Transpose . rowMove p q . unTranspose
  columnUnmove p q = Transpose . rowUnmove p q . unTranspose

-- | Find a shortest path from p to q through non-zero entries of a matrix.
-- Requires p =/= q.
shortestPath :: Reducible m => Natural -> Natural -> m -> [Natural]
shortestPath p q m = go (Seq.singleton [p])
  where
    go (path Seq.:<| paths)
      | m ! (head path, q) > 0 = reverse (q : path)
      | otherwise =
        go
          ( paths
              <> Seq.fromList
                [r : path | r <- [0 .. size m - 1], m ! (head path, r) > 0]
          )
    go _ = error "no path"

type Matrix a = Vector (Vector a)

makeMatrix :: [[Integer]] -> Matrix Integer
makeMatrix = Vector.fromList . map Vector.fromList

addKTimesElemToElem ::
  (HasCallStack, Additive f) =>
  Integer ->
  Natural ->
  Natural ->
  Vector (f Integer) ->
  Vector (f Integer)
addKTimesElemToElem k i j v =
  Vector.update v $
    Vector.singleton
      ( fromIntegral j,
        k *^ v Vector.! fromIntegral i ^+^ v Vector.! fromIntegral j
      )

instance Reducible (Matrix Integer) where
  size = fromIntegral . Vector.length

  v ! (i, j) = v Vector.! fromIntegral i Vector.! fromIntegral j

  rowMove p q m
    | p == q = error "cannot add row to itself"
    | m ! (q, p) < 1 = error "missing edge before row move"
    | otherwise = addKTimesElemToElem 1 p q m

  rowUnmove p q m
    | p == q = error "cannot subtract row from itself"
    | m' ! (q, p) < 1 =
      error
        ( unwords
            [ "missing edge after row unmove",
              show p,
              show q
            ]
        )
    | otherwise = m'
    where
      m' = addKTimesElemToElem (-1) p q m

  columnMove p q m
    | p == q = error "cannot add col to itself"
    | m ! (p, q) < 1 = error "missing edge before col move"
    | otherwise =
      coerce $
        Vector.map (addKTimesElemToElem @Identity 1 p q) $
          coerce m

  columnUnmove p q m
    | p == q = error "cannot subtract row from itself"
    | m' ! (p, q) < 1 = error "missing edge after col unmove"
    | otherwise = m'
    where
      m' =
        coerce $
          Vector.map (addKTimesElemToElem @Identity (-1) p q) $
            coerce m

toMatrix :: Reducible m => m -> Matrix Integer
toMatrix m =
  makeMatrix
    [ [m ! (i, j) | j <- [0 .. size m - 1]]
      | i <- [0 .. size m - 1]
    ]

instance FlowEquiv (Matrix Integer) where
  splitTopCorner m =
    Vector.cons row1 (Vector.snoc (Vector.map dup (Vector.tail m)) row2)
    where
      n = m ! (0, 0)
      row1 =
        Vector.cons 0 $
          Vector.snoc (Vector.replicate (fromIntegral (size m) - 1) 0) 1
      row2 = Vector.cons n $ Vector.snoc (Vector.tail (m Vector.! 0)) (n - 1)
      dup v =
        Vector.cons (v Vector.! 0) $ Vector.snoc (Vector.tail v) (v Vector.! 0)

  deleteSource p m =
    makeMatrix
      [ [m ! (i, j) | j <- [0 .. size m - 1] \\ [p]]
        | i <- [0 .. size m - 1] \\ [p]
      ]

isIrreducible :: Reducible m => m -> Bool
isIrreducible m =
  and
    [ j `Set.member` (r Map.! i)
      | i <- [0 .. size m - 1],
        j <- [0 .. size m - 1]
    ]
  where
    r = reachable m

reachable :: Reducible m => m -> Map Natural (Set Natural)
reachable m =
  Map.fromList
    [ (i, reachableFrom (Set.singleton i) i)
      | i <- [0 .. size m - 1]
    ]
  where
    reachableFrom visited i =
      foldl'
        (\v j -> reachableFrom (Set.insert j v) j)
        visited
        [ j
          | j <- [0 .. size m - 1],
            m ! (i, j) > 0,
            not (j `Set.member` visited)
        ]

isNonTrivial :: Reducible m => m -> Bool
isNonTrivial m =
  any (> 1) [sum [m ! (i, j) | j <- [0 .. size m - 1]] | i <- [0 .. size m - 1]]
