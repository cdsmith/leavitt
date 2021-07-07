module FranksNormalForm where

import Data.Foldable (foldl')
import Data.List ((\\))
import GHC.Stack (HasCallStack)
import Numeric.Natural (Natural)
import Reduction (FlowEquiv (..), Reducible (..), Transpose (..))

-- Converts any matrix (A - I) into a flox equivalent matrix where the diagonal
-- elements are non-negative.
--
-- See Franks (1984) Corollary 2.3
makeNonNegativeDiagonal :: FlowEquiv m => m -> m
makeNonNegativeDiagonal m0 = case ps of
  [] -> m0
  (p : _) ->
    makeNonNegativeDiagonal
      (deleteSource p (foldl' (zeroCol p) m0 ([0 .. size m0 - 1] \\ [p])))
  where
    ps = [i | i <- [0 .. size m0 - 1], m0 ! (i, i) < 0]
    zeroCol p m q = iterate (rowMove p q) m !! fromIntegral (m ! (p, q))

-- | Uses elementary row and column operations to convert any matrix to a
-- similar matrix with all positive elements.
--
-- See Franks (1984) Corollary 2.5
makeStrictPositive :: (HasCallStack, FlowEquiv m) => m -> m
makeStrictPositive m0 =
  foldl'
    ( \m j ->
        let k =
              max
                0
                ( maximum
                    [ (pivot - mWithPositiveColumn ! (i, j)) `quot` pivot
                      | i <- [0 .. size m - 1],
                        let pivot = mWithPositiveColumn ! (i, posCol)
                    ]
                )
         in addKTimesColToCol k posCol j m
    )
    mWithPositiveColumn
    ([0 .. size m1 - 1] \\ [posCol])
  where
    m1 = makeNonNegativeDiagonal m0
    (posVal, posRow, posCol) =
      minimum
        [ (val, i, j)
          | i <- [0 .. size m1 - 1],
            j <- [0 .. size m1 - 1],
            let val = m1 ! (i, j),
            val > 0
        ]
    mWithPositiveColumn =
      foldl'
        ( \m i ->
            addKTimesRowToRow
              (max 0 ((posVal - m ! (i, posCol)) `quot` posVal))
              posRow
              i
              m
        )
        m1
        ([0 .. size m1 - 1] \\ [posRow])

-- | Converts a matrix to a similar matrix with all positive elements and whose
-- size is the maximum of this matrix size, and the given size.
--
-- See Franks (1984) Corollary 2.6
makeStrictPositiveWithSize :: (HasCallStack, FlowEquiv m) => Natural -> m -> m
makeStrictPositiveWithSize n m
  | size m < n =
    makeStrictPositiveWithSize n $ splitTopCorner $ makeStrictPositive m
  | otherwise = makeStrictPositive m

-- | Augments given columns by adding copies of column c, until the element at
-- row p is less than the element at row q.
--
-- See Franks (1984) Definition 2.7 and Lemma 2.8
columnAugment ::
  (HasCallStack, Reducible m) =>
  -- | columns to augment
  [Natural] ->
  -- | c
  Natural ->
  -- | p
  Natural ->
  -- | q
  Natural ->
  m ->
  m
columnAugment cs c p q m0 = foldl' augmentOne m0 cs
  where
    augmentOne m j =
      let dc = m ! (q, c) - m ! (p, c)
          dj = m ! (q, j) - m ! (p, j)
          k = max 0 ((dc - dj) `quot` dc)
       in addKTimesColToCol k c j m

-- | In column c, subtract row p from row q, after augmenting the other columns
-- with c so that the subtraction leaves the matrix strictly positive.
--
-- See Franks (1984) Definition 2.7 and Lemma 2.8
columnAugmentAndRowSubtract ::
  (HasCallStack, Reducible m) =>
  -- | c
  Natural ->
  -- | p
  Natural ->
  -- | q
  Natural ->
  m ->
  m
columnAugmentAndRowSubtract c p q m =
  addKTimesRowToRow (-1) p q (columnAugment ([0 .. size m - 1] \\ [c]) c p q m)

-- | Augments given rows by adding copies of row r, until the element at
-- column p is less than the element at column q.
--
-- See Franks (1984) Definition 2.7 and Lemma 2.8
rowAugment ::
  (HasCallStack, Reducible m) =>
  -- rows to augment
  [Natural] ->
  -- r
  Natural ->
  -- p
  Natural ->
  -- q
  Natural ->
  m ->
  m
rowAugment rs r p q = unTranspose . columnAugment rs r p q . Transpose

-- | In row r, subtract column p from column q, after augmenting the other rows
-- with r so that the subtraction leaves the matrix strictly positive.
--
-- See Franks (1984) Definition 2.7 and Lemma 2.8
rowAugmentAndColumnSubtract ::
  (HasCallStack, Reducible m) =>
  -- | r
  Natural ->
  -- | p
  Natural ->
  -- | q
  Natural ->
  m ->
  m
rowAugmentAndColumnSubtract r p q =
  unTranspose . columnAugmentAndRowSubtract r p q . Transpose

isStrictPositive :: Reducible m => m -> Bool
isStrictPositive m =
  all (> 0) [m ! (i, j) | i <- [0 .. size m - 1], j <- [0 .. size m - 1]]

-- | Converts m to a similar matrix m' whose first column consists entirely of
-- d1, the greatest common divisor of the elements of m'.
--
-- See Franks (1984) Proposition 2.9, but we do things a little differently.
-- If the smallest element of m is not in the first column, we can perform a
-- row augmentation and column subtraction to subtract the column containing
-- the minimal element from the first column.  Iterated enough times, this
-- yields a matrix whose minimum element is in the first column.  Doing this
-- avoids the need for conjugation by a permutation matrix, so that we need
-- fewer primitive operations.
gcdFirstColumn :: (HasCallStack, Reducible m) => m -> m
gcdFirstColumn m
  | not (isStrictPositive m) = error "m is not strict positive"
  | q > 0 = gcdFirstColumn (rowAugmentAndColumnSubtract p q 0 m)
  | (i : _) <- [i | i <- [0 .. size m - 1], m ! (i, 0) > d0] =
    gcdFirstColumn (columnAugmentAndRowSubtract q p i m)
  | otherwise =
    case [ (m ! (i, j), i, j)
           | i <- [0 .. size m - 1],
             j <- [0 .. size m - 1],
             gcd (m ! (i, j)) d0 /= d0
         ] of
      ((_, r, s) : _) ->
        gcdFirstColumn (rowAugmentAndColumnSubtract r q s m)
      _ -> m
  where
    (d0, q, p) =
      minimum
        [(m ! (i, j), j, i) | i <- [0 .. size m - 1], j <- [0 .. size m - 1]]

-- | Add row p to row q enough times that all but the first element of row q are
-- greater than row r, then subtract row r from row q.
--
-- See Franks (1984) Theorem 3.3, where this operation is used in two parts of
-- the reduction to obtain zeros in the first column.
augmentAndSubtractRow ::
  (HasCallStack, Reducible m) =>
  -- | p
  Natural ->
  -- | q
  Natural ->
  -- | r
  Natural ->
  m ->
  m
augmentAndSubtractRow p q r m =
  addKTimesRowToRow (-1) r q (addKTimesRowToRow k p q m)
  where
    k =
      max 0 $
        maximum
          [ (m ! (r, j) - m ! (q, j) + m ! (p, j)) `quot` m ! (p, j)
            | j <- [1 .. size m - 1]
          ]

-- | Modifies the first column of a matrix so that all entries except for row 1
-- are equal to zero.  Row p must be less than row q in column c, and all
-- entries in the first column must be equal.
--
-- See Franks (1984) Theorem 3.3, where this is the main step of the induction
zeroFirstColumnAndSecondRow ::
  (HasCallStack, Reducible m) =>
  -- | c
  Natural ->
  -- | p
  Natural ->
  -- | q
  Natural ->
  m ->
  m
zeroFirstColumnAndSecondRow c p q m0 =
  foldl'
    (\m i -> addKTimesColToCol (- m ! (1, i) `quot` m ! (1, 0)) 0 i m)
    zeroedFirstColumn
    [1 .. size m0 - 1]
  where
    oneZero =
      addKTimesRowToRow (-1) p q $
        columnAugment ([1 .. size m0 - 1] \\ [c]) c p q m0
    clearAllBut zr =
      let zeroRow m i = augmentAndSubtractRow q i zr m
       in foldl' zeroRow oneZero ([0 .. size m0 - 1] \\ [zr, q])
    zeroedFirstColumn
      | q == 1 =
        augmentAndSubtractRow 0 2 1 $ addKTimesRowToRow 1 2 1 $ clearAllBut 2
      | otherwise = clearAllBut 1

newtype WithoutRow2Col1 m = WithoutRow2Col1 {restore :: m}

instance Reducible m => Reducible (WithoutRow2Col1 m) where
  size (WithoutRow2Col1 m) = size m - 1

  WithoutRow2Col1 m ! (i, j) = m ! (if i > 0 then i + 1 else i, j + 1)

  addKTimesRowToRow k p q =
    WithoutRow2Col1
      . addKTimesRowToRow
        k
        (if p > 0 then p + 1 else p)
        (if q > 0 then q + 1 else q)
      . restore

  addKTimesColToCol k p q =
    WithoutRow2Col1
      . addKTimesColToCol k (p + 1) (q + 1)
      . restore

-- Reduce a matrix to its Franks normal form of the given size.  The target size
-- should be at least the size of the input (though occasionally it works a
-- little smaller if there are negative values on the diagonal).
--
-- See Franks (1984) Theorem 3.3
reduceToNormalForm :: (HasCallStack, FlowEquiv m) => Natural -> m -> m
reduceToNormalForm sz m0 = go (makeStrictPositiveWithSize sz m0)
  where
    go :: (HasCallStack, Reducible m) => m -> m
    go m1 =
      let colReduced = gcdFirstColumn m1
          differences =
            [ (p, q, c)
              | c <- [1 .. size m1 - 1],
                p <- [0 .. size m1 - 1],
                q <- [0 .. size m1 - 1],
                colReduced ! (p, c) < colReduced ! (q, c)
            ]
       in case differences of
            [] ->
              -- matrix is rank 1.  Terminating case.
              let uniformCol m c = addKTimesColToCol (1 - k) 0 c m
                    where
                      d0 = m ! (0, 0)
                      k = m ! (0, c) `quot` d0
               in foldl' uniformCol colReduced [1 .. size m1 - 1]
            ((p, q, c) : _)
              | q == 1 && size m1 == 2 ->
                -- det(I - A) > 0, size = 2.  Terminating case.
                let k = colReduced ! (0, 1) `quot` colReduced ! (0, 0) - 1
                 in addKTimesColToCol (- k) 0 1 colReduced
              | otherwise ->
                restore $
                  go $
                    WithoutRow2Col1 $
                      zeroFirstColumnAndSecondRow c p q colReduced
