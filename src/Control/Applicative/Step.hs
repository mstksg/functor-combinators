{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE FlexibleInstances #-}

module Control.Applicative.Step (
    Step(..)
  , AccumNat(..)
  ) where

import           Numeric.Natural
import           Control.Monad.Writer

data Step f a = Step { stepPos :: Natural, stepVal :: f a }
  deriving (Show, Eq, Ord, Functor)

instance Applicative f => Applicative (Step f) where
    pure = Step 0 . pure
    Step n f <*> Step m x = Step (n + m) (f <*> x)

class Applicative f => AccumNat f where
    stepWith :: Natural -> a -> f a
    stepWith n x = x <$ step n
    step     :: Natural -> f ()
    step = (`stepWith` ())

    {-# MINIMAL stepWith | step #-}

instance Applicative f => AccumNat (Step f) where
    stepWith n x = Step n (pure x)
    step n       = Step n (pure ())

instance Monad m => AccumNat (WriterT (Sum Natural) m) where
    stepWith n x = writer (x, Sum n)
    step         = tell . Sum

