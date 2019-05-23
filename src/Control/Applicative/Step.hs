{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyCase         #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}

module Control.Applicative.Step (
    Step(..)
  , AccumNat(..)
  , VoidT
  , absurdT
  ) where

import           Numeric.Natural
import           Control.Monad.Writer


data Step f a = Step { stepPos :: Natural, stepVal :: f a }
  deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

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

-- | The identity functor of ':+:'.
data VoidT a
  deriving (Show, Eq, Ord, Functor)

-- | We have a natural transformation between 'VoidT' and any other
-- functor @f@ with no constraints.
absurdT :: VoidT a -> f a
absurdT = \case {}

