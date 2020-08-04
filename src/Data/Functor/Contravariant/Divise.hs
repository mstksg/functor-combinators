
module Data.Functor.Contravariant.Divise (
    Divise(..)
  , Choice(..)
  , Loss(..)
  ) where

import           Data.Functor.Contravariant
import           Data.Void

class Contravariant f => Divise f where
    divise :: (a -> (b, c)) -> f b -> f c -> f a

class Contravariant f => Choice f where
    choice :: (a -> Either b c) -> f b -> f c -> f a

class Choice f => Loss f where
    loss :: (a -> Void) -> f a
