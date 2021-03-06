{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

import Control.Monad (forM)
import Data.Foldable (foldl')
import qualified Data.Map as Map
import qualified Data.Set as Set
import FranksNormalForm
import Graph
import Leavitt
import Numeric.Natural (Natural)
import Reduction
import Test.Hspec
import Test.Hspec.QuickCheck
import Test.QuickCheck

instance Arbitrary Graph where
  arbitrary = do
    Positive (Small nverts) <- arbitrary
    let vs = take nverts (freshVertices empty)
    let g0 = foldl' (flip insVertex) empty vs
    es <- fmap concat $
      forM ((,) <$> vs <*> vs) $ \(v, w) -> do
        NonNegative (Small mult) <- arbitrary
        return (replicate mult (v, w))
    return $
      foldl'
        (\g ((v, w), e) -> insEdge v e w g)
        g0
        (zip es (freshEdges g0))

  shrink g =
    [delVertex v g | v <- Set.toList (vertices g)]
      ++ [delEdge e g | e <- Set.toList (edges g)]

instance Arbitrary Natural where
  arbitrary = fromInteger . getNonNegative <$> arbitrary
  shrink = map (fromInteger . getNonNegative) . shrink . NonNegative . toInteger

main :: IO ()
main = hspec $ do
  describe "Matrix" $ do
    it "reduces to normal form (det (I - A) = 0)" $
      example $ do
        let m = makeMatrix [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
        reduceToNormalForm 3 m
          `shouldBe` makeMatrix [[0, 3, 3], [1, 0, 0], [0, 3, 3]]

    it "reduces to normal form (det (I - A) < 0)" $
      example $ do
        let m = makeMatrix [[1, 1, 1], [4, 5, 6], [7, 8, 11]]
        reduceToNormalForm 3 m
          `shouldBe` makeMatrix [[0, 0, 2], [1, 0, 0], [0, 1, 0]]

    it "reduces to normal form (det (I - A) > 0)" $
      example $ do
        let m = makeMatrix [[1, 1, 1], [4, 5, 6], [7, 8, 5]]
        reduceToNormalForm 3 m
          `shouldBe` makeMatrix [[0, 1, 1], [1, 0, 0], [0, 1, 5]]

    it "expands to larger normal forms" $
      example $ do
        let m = makeMatrix [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
        reduceToNormalForm 10 m
          `shouldBe` makeMatrix
            [ [0, 0, 0, 0, 0, 0, 0, 0, 3, 3],
              [1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
              [0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
              [0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
              [0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
              [0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
              [0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
              [0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
              [0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
              [0, 0, 0, 0, 0, 0, 0, 0, 3, 3]
            ]

  describe "Graph" $ do
    it "implements row move" $ do
      let g =
            insEdge (Vertex 0) (Edge 1) (Vertex 1) $
              insEdge (Vertex 1) (Edge 2) (Vertex 0) $
                insEdge (Vertex 1) (Edge 3) (Vertex 2) $
                  insEdge (Vertex 2) (Edge 4) (Vertex 0) empty
      toMatrix (rowMove 1 0 g) `shouldBe` rowMove 1 0 (toMatrix g)

    it "implements row unmove" $ do
      let g =
            insEdge (Vertex 1) (Edge 2) (Vertex 0) $
              insEdge (Vertex 1) (Edge 3) (Vertex 2) $
                insEdge (Vertex 2) (Edge 4) (Vertex 0) $
                  insEdge (Vertex 0) (Edge 5) (Vertex 0) $
                    insEdge (Vertex 0) (Edge 6) (Vertex 2) empty
      toMatrix (rowUnmove 1 0 g) `shouldBe` rowUnmove 1 0 (toMatrix g)

    it "implements column move" $ do
      let g =
            insEdge (Vertex 0) (Edge 1) (Vertex 1) $
              insEdge (Vertex 1) (Edge 2) (Vertex 0) $
                insEdge (Vertex 1) (Edge 3) (Vertex 2) $
                  insEdge (Vertex 2) (Edge 4) (Vertex 0) $
                    insEdge (Vertex 0) (Edge 5) (Vertex 0) empty
      toMatrix (columnMove 0 1 g) `shouldBe` columnMove 0 1 (toMatrix g)

    it "implements column unmove" $ do
      let g =
            insEdge (Vertex 0) (Edge 1) (Vertex 1) $
              insEdge (Vertex 1) (Edge 2) (Vertex 0) $
                insEdge (Vertex 1) (Edge 3) (Vertex 2) $
                  insEdge (Vertex 2) (Edge 4) (Vertex 1) $
                    insEdge (Vertex 2) (Edge 5) (Vertex 0) $
                      insEdge (Vertex 0) (Edge 6) (Vertex 0) $
                        insEdge (Vertex 1) (Edge 7) (Vertex 1) empty
      toMatrix (columnUnmove 0 1 g) `shouldBe` columnUnmove 0 1 (toMatrix g)

    it "implements source deletion" $ do
      let g =
            insEdge (Vertex 0) (Edge 1) (Vertex 1) $
              insEdge (Vertex 1) (Edge 2) (Vertex 1) $
                insEdge (Vertex 1) (Edge 3) (Vertex 1) empty
      toMatrix (deleteSource 0 g) `shouldBe` deleteSource 0 (toMatrix g)

    it "implements splitTopCorner" $ do
      let g =
            insEdge (Vertex 0) (Edge 1) (Vertex 0) $
              insEdge (Vertex 0) (Edge 2) (Vertex 0) $
                insEdge (Vertex 0) (Edge 3) (Vertex 1) $
                  insEdge (Vertex 1) (Edge 4) (Vertex 0) empty
      toMatrix (splitTopCorner g) `shouldBe` splitTopCorner (toMatrix g)

  describe "Leavitt" $ do
    modifyMaxSuccess (const 10) $
      it "satisfies CK1" $
        property $
          \(g :: Graph) ->
            let ck1Holds e f =
                  star (edge g e) * edge g f
                    == ( if e == f
                           then vertex g (range g Map.! e)
                           else 0 :: LPA Int
                       )
             in and
                  [ ck1Holds e f
                    | e <- Set.toList (edges g),
                      f <- e : Set.toList (Set.take 2 (edges g))
                  ]
    it "satisfies CK2" $
      example $ do
        let g =
              insEdge (Vertex 0) (Edge 0) (Vertex 0) $
                insEdge (Vertex 0) (Edge 1) (Vertex 0) empty
        edge g (Edge 0) * star (edge g (Edge 0))
          + edge g (Edge 1) * star (edge g (Edge 1))
          `shouldBe` (vertex g (Vertex 0) :: LPA Int)
        return ()