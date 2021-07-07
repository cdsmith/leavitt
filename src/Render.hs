module Render where

class Render a where
    render :: a -> String

instance Render Int where render = show
instance Render Integer where render = show
instance Render Double where render = show
instance Render Float where render = show
