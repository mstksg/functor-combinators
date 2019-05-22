{-# LANGUAGE DeriveFunctor #-}

module Control.Applicative.ListF (
    ListF(..)
  ) where

import           Data.Functor.Plus
import           Control.Applicative

-- | This is the Free 'Plus'.
newtype ListF f a = ListF { runListF :: [f a] }
  deriving (Show, Eq, Ord, Functor)

instance Applicative f => Applicative (ListF f) where
    pure  = ListF . (:[]) . pure
    ListF fs <*> ListF xs = ListF $ liftA2 (<*>) fs xs

instance Functor f => Alt (ListF f) where
    ListF xs <!> ListF ys = ListF (xs ++ ys)

instance Functor f => Plus (ListF f) where
    zero = ListF []
