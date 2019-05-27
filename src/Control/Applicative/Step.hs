{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE EmptyDataDeriving          #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE TemplateHaskell            #-}

module Control.Applicative.Step (
  -- * Fixed Points
    Step(..)
  , Steps(..)
  -- * Void
  , VoidT
  , absurdT
  ) where

import           Data.Deriving
import           Data.Data
import           GHC.Generics
import           Data.Functor.Alt
import           Data.Semigroup.Foldable
import           Data.Semigroup.Traversable
import           Numeric.Natural
import qualified Data.Map.NonEmpty          as NEM

-- | The fixed point of applications of ':+:' (functor sums).
--
-- Intuitively, in an infinite @f ':+:' f ':+:' f ':+:' f ...@, you have
-- exactly one @f@ /somewhere/.  A @'Step' f a@ has that @f@, with
-- a 'Natural' giving you "where" the @f@ is in the long chain.
--
-- 'interpret'ing it requires no constraint on the target context.
data Step f a = Step { stepPos :: Natural, stepVal :: f a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Step
deriveRead1 ''Step
deriveEq1 ''Step
deriveOrd1 ''Step

instance Applicative f => Applicative (Step f) where
    pure = Step 0 . pure
    Step n f <*> Step m x = Step (n + m) (f <*> x)

instance Foldable1 f => Foldable1 (Step f) where
    fold1      = fold1 . stepVal
    foldMap1 f = foldMap1 f . stepVal
    toNonEmpty = toNonEmpty . stepVal

instance Traversable1 f => Traversable1 (Step f) where
    traverse1 f (Step n x) = Step n <$> traverse1 f x
    sequence1 (Step n x) = Step n <$> sequence1 x

-- | The identity functor of ':+:' (and also 'TheseT')
data VoidT a
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''VoidT
deriveRead1 ''VoidT
deriveEq1 ''VoidT
deriveOrd1 ''VoidT

-- | We have a natural transformation between 'VoidT' and any other
-- functor @f@ with no constraints.
absurdT :: VoidT a -> f a
absurdT = \case {}

-- | The fixed point of applications of 'TheseT'.
--
-- Intuitively, in an infinite @f `TheseT` f `TheseT` f `TheseT` f ...@,
-- each of those infinite positions may have an @f@ in them.  However,
-- because of the at-least-one nature of 'TheseT', we know we have at least
-- one f at one position /somewhere/.
--
-- A @'Steps' f a@ has potentially many @f@s, each stored at a different
-- 'Natural' position, with the guaruntee that at least one @f@ exists.
--
-- 'interpret'ing it requires at least an 'Alt' instance in the target
-- context, since we have to handle potentially more than one @f@.
-- However, we don't fully need 'Plus', since we know we always have at
-- least one @f@.
newtype Steps f a = Steps { getSteps :: NEM.NEMap Natural (f a) }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Steps
deriveRead1 ''Steps
deriveEq1 ''Steps
deriveOrd1 ''Steps

instance Foldable1 f => Foldable1 (Steps f) where
    fold1      = foldMap1 fold1 . getSteps
    foldMap1 f = (foldMap1 . foldMap1) f . getSteps
    toNonEmpty = foldMap1 toNonEmpty . getSteps

instance Traversable1 f => Traversable1 (Steps f) where
    traverse1 f = fmap Steps . (traverse1 . traverse1) f . getSteps
    sequence1   = fmap Steps . traverse1 sequence1 . getSteps

instance Functor f => Alt (Steps f) where
    Steps xs <!> Steps ys = Steps $
      let (k, _) = NEM.findMax xs
      in  xs <> NEM.mapKeysMonotonic (+ (k + 1)) ys
