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
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeOperators              #-}

-- |
-- Module      : Control.Applicative.Step
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides functor combinators that are the fixed points of
-- applications of ':+:' and 'Data.Functor.These.TheseT'.  They are useful
-- for their 'Data.Functor.HFunctor.Interpret' instances, along with their
-- relationship to the 'Data.Functor.Tensor.Monoidal' insatnces of ':+:'
-- and 'Data.Functor.These.TheseT'.
module Control.Applicative.Step (
  -- * Fixed Points
    Step(..)
  , Steps(..)
  , stepUp
  , stepDown
  , stepping
  -- * Void
  , absurd1
  , Void2
  , absurd2
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Data
import           Data.Deriving
import           Data.Functor.Alt
import           Data.Functor.Bind
import           Data.Semigroup.Foldable
import           Data.Semigroup.Traversable
import           GHC.Generics
import           GHC.Natural
import qualified Data.Map.NonEmpty          as NEM

-- | An @f a@, along with a 'Natural' index.
--
-- @
-- Step f a ~ ('Natural', f a)
-- Step f   ~ ((,) 'Natural') ':.:' f       -- functor composition
-- @
--
-- It is the fixed point of infinite applications of ':+:' (functor sums).
--
-- Intuitively, in an infinite @f :+: f :+: f :+: f ...@, you have
-- exactly one @f@ /somewhere/.  A @'Step' f a@ has that @f@, with
-- a 'Natural' giving you "where" the @f@ is in the long chain.
--
-- Can be useful for using with the 'Data.Functor.Tensor.Monoidal' instance
-- of ':+:'.
--
-- 'Data.Functor.HFunctor.interpret'ing it requires no constraint on the
-- target context.
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

-- | "Uncons and cons" an @f@ branch before a 'Step'.  This is basically
-- a witness that 'stepDown' and 'stepUp' form an isomorphism.
stepping :: Step f <~> f :+: Step f
stepping = isoF stepDown stepUp

-- | Pop off the first iteem in a 'Step'.  Because a @'Step' f@ is @f :+:
-- f :+: f :+: ...@ forever, this matches on the first branch.
--
-- You can think of it as reassociating
--
-- @
-- f :+: f :+: f :+: f :+: ...
-- @
--
-- into
--
-- @
-- f :+: ( f :+: f :+: f :+: ...)
-- @
--
-- Forms an isomorphism with 'stepUp' (see 'stepping').
stepDown :: Step f ~> f :+: Step f
stepDown (Step n x) = case minusNaturalMaybe n 1 of
    Nothing -> L1 x
    Just m  -> R1 (Step m x)

-- | Unshift an item into a 'Step'.  Because a @'Step' f@ is @f :+: f :+:
-- f :+: f :+: ...@ forever, this basically conses an additional
-- possibility of @f@ to the beginning of it all.
--
-- You can think of it as reassociating
--
-- @
-- f :+: ( f :+: f :+: f :+: ...)
-- @
--
-- into
--
-- @
-- f :+: f :+: f :+: f :+: ...
-- @
--
-- Forms an isomorphism with 'stepDown' (see 'stepping').
stepUp :: f :+: Step f ~> Step f
stepUp = \case
    L1 x          -> Step 0       x
    R1 (Step n y) -> Step (n + 1) y

-- | We have a natural transformation between 'V1' and any other
-- functor @f@ with no constraints.
absurd1 :: V1 a -> f a
absurd1 = \case {}

-- | A non-empty map of 'Natural' to @f a@.  Basically, contains multiple
-- @f a@s, each at a given 'Natural' index.
--
-- @
-- Steps f a ~ 'M.Map' 'Natural' (f a)
-- Steps f   ~ 'M.Map' 'Natural' ':.:' f       -- functor composition
-- @
--
-- It is the fixed point of applications of 'Data.Functor.These.TheseT'.
--
-- Intuitively, in an infinite @f \`TheseT\` f \`TheseT\` f \`TheseT\` f ...@,
-- each of those infinite positions may have an @f@ in them.  However,
-- because of the at-least-one nature of 'Data.Functor.These.TheseT', we know we have at least
-- one f at one position /somewhere/.
--
-- A @'Steps' f a@ has potentially many @f@s, each stored at a different
-- 'Natural' position, with the guaruntee that at least one @f@ exists.
--
-- Can be useful for using with the 'Data.Functor.Tensor.Monoidal' instance
-- of 'Data.Functor.These.TheseT'.
--
-- 'Data.Functor.HFunctor.interpret'ing it requires at least an 'Alt'
-- instance in the target context, since we have to handle potentially more
-- than one @f@.
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

instance Semigroup (Steps f a) where
    Steps xs <> Steps ys = Steps $
      let (k, _) = NEM.findMax xs
      in  xs <> NEM.mapKeysMonotonic (+ (k + 1)) ys

instance Functor f => Alt (Steps f) where
    (<!>) = (<>)

-- | @'Void2' a b@ is uninhabited for all @a@ and @b@.
data Void2 a b
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Void2
deriveRead1 ''Void2
deriveEq1 ''Void2
deriveOrd1 ''Void2

instance Alt (Void2 f) where
    x <!> _ = absurd2 x

instance Bind (Void2 f) where
    x >>- _ = case x of {}

instance Apply (Void2 f) where
    x <.> _ = case x of {}

-- | If you treat a @'Void2' f a@ as a functor combinator, then 'absurd2'
-- lets you convert from a @'Void2' f a@ into a @t f a@ for any functor
-- combinator @t@.
absurd2 :: Void2 f a -> t f a
absurd2 = \case {}
