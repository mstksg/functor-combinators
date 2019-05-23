{-# LANGUAGE DeriveFoldable    #-}
{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE EmptyCase         #-}
{-# LANGUAGE EmptyDataDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE LambdaCase        #-}

module Control.Applicative.Step (
    Step(..)
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

-- | The identity functor of ':+:'.
data VoidT a
  deriving (Show, Eq, Ord, Functor)

-- | We have a natural transformation between 'VoidT' and any other
-- functor @f@ with no constraints.
absurdT :: VoidT a -> f a
absurdT = \case {}

