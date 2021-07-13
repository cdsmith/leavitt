{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TupleSections #-}

module Leavitt where

import Data.List (intercalate)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import Graph
import Render (Render (..))

-- | And algebra determined by some piece of structure.  The structure is a
-- parameter to all of the operations.
class StructuredAlgebra structure k a | a -> k where
  scale :: structure -> k -> a -> a
  one :: structure -> a
  plus :: structure -> a -> a -> a
  neg :: structure -> a -> a
  times :: structure -> a -> a -> a
  equal :: structure -> a -> a -> Bool

data StructuredTerm structure k a = Pure k | WithStructure structure a
  deriving (Show, Functor)

interpret ::
  StructuredAlgebra structure k a =>
  structure ->
  StructuredTerm structure k a ->
  a
interpret structure (Pure k) = scale structure k (one structure)
interpret _ (WithStructure _ a) = a

metaOp ::
  StructuredAlgebra structure k a =>
  (k -> k -> k) ->
  (structure -> a -> a -> a) ->
  StructuredTerm structure k a ->
  StructuredTerm structure k a ->
  StructuredTerm structure k a
metaOp opA _ (Pure a) (Pure b) = Pure (opA a b)
metaOp _ opB a (WithStructure structure b) =
  WithStructure structure (opB structure (interpret structure a) b)
metaOp _ opB (WithStructure structure a) b =
  WithStructure structure (opB structure a (interpret structure b))

instance
  (StructuredAlgebra structure k a, Num k) =>
  Num (StructuredTerm structure k a)
  where
  fromInteger = Pure . fromInteger

  (+) = metaOp (+) plus
  (-) = metaOp (-) (\structure a b -> plus structure a (neg structure b))
  (*) = metaOp (*) times

  abs = error "abs not defined"
  signum = error "signum not defined"

instance
  (StructuredAlgebra structure k a, Eq k) =>
  Eq (StructuredTerm structure k a)
  where
  Pure a == Pure b = a == b
  WithStructure s a == b = equal s a (interpret s b)
  a == WithStructure s b = equal s (interpret s a) b

instance (Render k, Render a) => Render (StructuredTerm structure k a) where
  render (Pure k) = render k
  render (WithStructure _ a) = render a

newtype Leavitt k = Leavitt {leavittCoeffs :: Map (Path, Path) k}
  deriving (Eq, Ord, Show)

instance (Eq k, Num k, Render k) => Render (Leavitt k) where
  render (Leavitt m)
    | Map.null m = "0"
    | otherwise =
      intercalate
        " + "
        [ unwords $
            [render lambda | lambda /= 1]
              ++ [render alpha | pathLen alpha > 0 || pathLen beta == 0]
              ++ [w ++ "^\\ast" | pathLen beta > 0, w <- words (render beta)]
          | ((alpha, beta), lambda) <- Map.toAscList m
        ]

instance (Eq k, Num k) => StructuredAlgebra Graph k (Leavitt k) where
  scale g k (Leavitt m) = normalize g $ Leavitt (Map.map (* k) m)

  one g =
    normalize g $
      Leavitt $
        Map.fromList
          [((Path (Left v), Path (Left v)), 1) | v <- Set.toList (vertices g)]

  plus g (Leavitt m1) (Leavitt m2) =
    normalize g $
      Leavitt (Map.unionWith (+) m1 m2)

  neg g (Leavitt m) = normalize g $ Leavitt (Map.map negate m)

  times g (Leavitt m1) (Leavitt m2) =
    normalize g $
      Leavitt
        ( Map.fromList
            [ case timesTerm g t1 t2 of
                Just t -> (t, k1 * k2)
                Nothing -> (t1, 0)
              | (t1, k1) <- Map.toAscList m1,
                (t2, k2) <- Map.toAscList m2
            ]
        )

  equal g (Leavitt m1) (Leavitt m2) =
    let len m = maximum (map (pathLen . snd) (Set.toList (Map.keysSet m)))
        maxLen = max (len m1) (len m2)
        Leavitt n1 = normalizeAtLen g maxLen (Leavitt m1)
        Leavitt n2 = normalizeAtLen g maxLen (Leavitt m2)
     in n1 == n2

normalize :: (Eq k, Num k) => Graph -> Leavitt k -> Leavitt k
normalize g (Leavitt m) = Leavitt (Map.filterWithKey goodTerm m)
  where
    goodTerm (alpha, beta) lambda =
      lambda /= 0
        && pathRange g alpha == pathRange g beta

timesTerm :: Graph -> (Path, Path) -> (Path, Path) -> Maybe (Path, Path)
timesTerm g (alpha1, Path (Left v)) (alpha2, beta2)
  | pathSource g alpha2 == v = (,beta2) <$> concatPaths g alpha1 alpha2
  | otherwise = Nothing
timesTerm g (alpha1, beta1) (Path (Left v), beta2)
  | pathSource g beta1 == v = (alpha1,) <$> concatPaths g beta2 beta1
  | otherwise = Nothing
timesTerm g (alpha1, Path (Right (e : es))) (Path (Right (f : fs)), beta2)
  | e == f =
    timesTerm
      g
      (alpha1, Path (if null es then Left (range g Map.! e) else Right es))
      (Path (if null fs then Left (range g Map.! f) else Right fs), beta2)
  | otherwise = Nothing
timesTerm g (alpha1, Path (Right [])) (alpha2, beta2) =
  (,beta2) <$> concatPaths g alpha1 alpha2
timesTerm g (alpha1, beta1) (Path (Right []), beta2) =
  (alpha1,) <$> concatPaths g beta2 beta1

normalizeAtLen :: (Eq k, Num k) => Graph -> Int -> Leavitt k -> Leavitt k
normalizeAtLen g len (Leavitt m) =
  normalize g $
    Leavitt (Map.fromList (concatMap expand (Map.assocs m)))
  where
    expand ((alpha, beta), k)
      | pathLen beta >= len = [((alpha, beta), k)]
      | otherwise =
        let fs = invSource g Map.! pathRange g beta
         in if Set.null fs
              then [((alpha, beta), k)]
              else
                concatMap
                  expand
                  [ ((alpha', beta'), k)
                    | f <- Set.toList fs,
                      Just alpha' <- [concatPaths g alpha (Path (Right [f]))],
                      Just beta' <- [concatPaths g beta (Path (Right [f]))]
                  ]

type LPA k = StructuredTerm Graph k (Leavitt k)

edge :: Num k => Graph -> Edge -> LPA k
edge g e =
  WithStructure g $
    Leavitt
      (Map.singleton (Path (Right [e]), Path (Left (range g Map.! e))) 1)

starEdge :: Num k => Graph -> Edge -> LPA k
starEdge g e =
  WithStructure g $
    Leavitt
      (Map.singleton (Path (Left (range g Map.! e)), Path (Right [e])) 1)

vertex :: Num k => Graph -> Vertex -> LPA k
vertex g v =
  WithStructure g $
    Leavitt
      (Map.singleton (Path (Left v), Path (Left v)) 1)

star :: LPA k -> LPA k
star = fmap (\(Leavitt m) -> Leavitt (Map.mapKeys swap m))
  where
    swap (a, b) = (b, a)

starMap ::
  (Num k, Eq k) =>
  Graph ->
  (Vertex -> LPA k) ->
  (Edge -> LPA k) ->
  LPA k ->
  LPA k
starMap g vertMap edgeMap x = go (interpret g x)
  where
    go (Leavitt m) =
      sum [fromTerm alpha beta k | ((alpha, beta), k) <- Map.toAscList m]

    fromTerm alpha beta k = Pure k * fromPath alpha * star (fromPath beta)

    fromPath (Path (Left v)) = vertMap v
    fromPath (Path (Right (e : es))) = edgeMap e * fromPath (Path (Right es))
    fromPath (Path (Right [])) = Pure 1
