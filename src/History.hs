module History where

import Reduction

newtype WithHistory m = WithHistory {getHistory :: [(String, m)]}

instance Reducible m => Reducible (WithHistory m) where
  size (WithHistory h) = size m where (_, m) = last h

  (WithHistory h) ! (i, j) = m ! (i, j) where (_, m) = last h

  addKTimesRowToRow k p q wh@(WithHistory h)
    | k == 0 = wh
    | otherwise =
      WithHistory
        ( h
            ++ [ ( unwords ["addKTimesRowToRow", show k, show p, show q],
                   addKTimesRowToRow k p q m
                 )
               ]
        )
    where
      (_, m) = last h

  addKTimesColToCol k p q wh@(WithHistory h)
    | k == 0 = wh
    | otherwise =
      WithHistory
        ( h
            ++ [ ( unwords ["addKTimesColToCol", show k, show p, show q],
                   addKTimesColToCol k p q m
                 )
               ]
        )
    where
      (_, m) = last h

instance FlowEquiv m => FlowEquiv (WithHistory m) where
  splitTopCorner (WithHistory h) =
    WithHistory (h ++ [("splitTopCorner", splitTopCorner m)])
    where
      (_, m) = last h

  deleteSource p (WithHistory h) =
    WithHistory (h ++ [("deleteSource " ++ show p, deleteSource p m)])
    where
      (_, m) = last h

withHistory :: m -> WithHistory m
withHistory m = WithHistory [("original", m)]
