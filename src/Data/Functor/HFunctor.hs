{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns            #-}

-- |
-- Module      : Data.Functor.HFunctor
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides tools for working with unary functor combinators.
--
-- These are types @f@ that take a functor @f@ and return a new functor @t
-- f@, enhancing @f@ with new structure and abilities.
--
-- The main operations these combinators support are:
--
-- @
-- 'hmap' :: (forall x. f x -> g x) -> t f a -> t g a
-- @
--
-- which lets you "swap out" the functor being transformed,
--
-- @
-- 'inject' :: f a -> t f a
-- @
--
-- which lets you "lift" an @f a@ into its transformed version, and also:
--
-- @
-- 'interpret'
--     :: C t g
--     => (forall x. f a -> g a)
--     -> t f a
--     -> g a
-- @
--
-- that lets you "interpret" a @t f a@ into a context @g a@, essentially
-- "running" the computaiton that it encodes.  The context is required to
-- have a typeclass constraints that reflects what is "required" to be able
-- to run a functor combinator.
--
-- Every single instance provides different tools.  Check out the instance
-- list for a nice list of useful combinators, or also the README for
-- a high-level rundown.
--
-- See "Data.Functor.Tensor" for binary functor combinators that mix
-- together two or more different functors.
module Data.Functor.HFunctor (
    HFunctor(..)
  , overHFunctor
  , HFix(..)
  , HBind(..)
  ) where

import           Control.Applicative.Backwards
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Data.Coerce
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Coyoneda
import           Data.Functor.HFunctor.Internal
import           Data.Functor.HFunctor.IsoF
import           Data.Functor.Reverse
import           Data.Pointed
import           Data.Semigroup.Foldable
import qualified Control.Alternative.Free       as Alt
import qualified Control.Applicative.Free.Fast  as FAF
import qualified Control.Applicative.Free.Final as FA

overHFunctor
    :: HFunctor t
    => AnIsoF' f g
    -> t f <~> t g
overHFunctor (cloneIsoF' -> f) = isoF (hmap (viewF f)) (hmap (reviewF f))

data HFix t f a = HFix { unHFix :: t (HFix t f) a }

instance HFunctor t => HFunctor (HFix t) where
    hmap f (HFix x) = HFix (hmap (hmap f) x)

instance Show1 (t (HFix t f)) => Show1 (HFix t f) where
    liftShowsPrec sp sl d (HFix x) =
        showsUnaryWith (liftShowsPrec sp sl) "HFix" d x

instance (Show1 (t (HFix t f)), Show a) => Show (HFix t f a) where
    showsPrec = liftShowsPrec showsPrec showList

class HFunctor t => HBind t where
    hbind :: (f ~> t g) -> t f ~> t g

instance HBind Coyoneda where
    hbind f (Coyoneda g x) = g <$> f x

instance HBind Ap where
    hbind = runAp

instance HBind ListF where
    hbind f = foldMap f . runListF

instance HBind NonEmptyF where
    hbind f = foldMap1 f . runNonEmptyF

instance HBind MaybeF where
    hbind f = foldMap f . runMaybeF

instance HBind Step where
    hbind f (Step n x) = Step (n + m) y
      where
        Step m y = f x

instance HBind Steps where
    hbind f = foldMap1 f . getSteps

instance HBind Alt.Alt where
    hbind = Alt.runAlt

instance HBind Free where
    hbind = interpretFree

instance HBind Free1 where
    hbind = interpretFree1

instance HBind FA.Ap where
    hbind = FA.runAp

instance HBind FAF.Ap where
    hbind = FAF.runAp

instance HBind IdentityT where
    hbind f = f . runIdentityT

instance HBind Lift where
    hbind = elimLift point

instance HBind MaybeApply where
    hbind f = either f point . runMaybeApply

instance HBind Backwards where
    hbind f = f . forwards

instance HBind WrappedApplicative where
    hbind f = f . unwrapApplicative

instance HBind Reverse where
    hbind f = f . getReverse

instance HBind Void2 where
    hbind _ = coerce

instance HBind t => HBind (HFix t) where
    hbind :: forall f g. (f ~> HFix t g) -> HFix t f ~> HFix t g
    hbind _ = go
      where
        go :: HFix t f ~> HFix t g
        go = HFix . hbind @t (unHFix . go) . unHFix
