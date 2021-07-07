module Trace where

import Debug.Trace (trace)
import Reduction (FlowEquiv (..), Reducible (..))

newtype Traced a = Traced {traced :: a} deriving (Eq, Show)

instance (Show a, Reducible a) => Reducible (Traced a) where
  size (Traced m) = size m
  Traced m ! (i, j) = m ! (i, j)

  addKTimesRowToRow k p q (Traced m)
    | k == 0 = Traced m
    | otherwise =
      unwords ["addKTimesRowToRow", show k, show p, show q, show m']
        `trace` Traced m'
    where
      m' = addKTimesRowToRow k p q m

  addKTimesColToCol k p q (Traced m)
    | k == 0 = Traced m
    | otherwise =
      unwords ["addKTimesColToCol", show k, show p, show q, show m']
        `trace` Traced m'
    where
      m' = addKTimesColToCol k p q m

instance (Show a, FlowEquiv a) => FlowEquiv (Traced a) where
  splitTopCorner (Traced m) =
    unwords ["splitTopCorner", show m']
      `trace` m'
    where
      m' = Traced (splitTopCorner m)

  deleteSource p (Traced m) =
    unwords ["deleteSource", show p, show m']
      `trace` m'
    where
      m' = Traced (deleteSource p m)
