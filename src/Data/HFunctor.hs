{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DeriveFunctor           #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE StandaloneDeriving      #-}
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
module Data.HFunctor (
    HFunctor(..)
  , overHFunctor
  , Inject(..)
  , HBind(..)
  , HLift(..)
  , HFree(..)
  ) where

import           Control.Applicative.Backwards
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Monad.Reader
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Data.Coerce
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Coyoneda
import           Data.Functor.Reverse
import           Data.HFunctor.Internal
import           Data.HFunctor.IsoF
import           Data.List.NonEmpty             (NonEmpty(..))
import           Data.Pointed
import           Data.Semigroup.Foldable
import qualified Control.Alternative.Free       as Alt
import qualified Control.Applicative.Free.Fast  as FAF
import qualified Control.Applicative.Free.Final as FA
import qualified Data.Map.NonEmpty              as NEM

overHFunctor
    :: HFunctor t
    => AnIsoF' f g
    -> t f <~> t g
overHFunctor (cloneIsoF' -> f) = isoF (hmap (viewF f)) (hmap (reviewF f))

data HLift t f a = HPure  (f a)
                 | HOther (t f a)
  deriving Functor

instance (Show1 (t f), Show1 f) => Show1 (HLift t f) where
    liftShowsPrec sp sl d = \case
      HPure x -> showsUnaryWith (liftShowsPrec sp sl) "HPure" d x
      HOther x -> showsUnaryWith (liftShowsPrec sp sl) "HOther" d x

instance (Show1 (t f), Show1 f, Show a) => Show (HLift t f a) where
    showsPrec = liftShowsPrec showsPrec showList

instance HFunctor t => HFunctor (HLift t) where
    hmap f = \case
      HPure  x -> HPure  (f x)
      HOther x -> HOther (hmap f x)

data HFree t f a = HReturn (f a)
                 | HJoin   (t (HFree t f) a)

deriving instance (Functor f, Functor (t (HFree t f))) => Functor (HFree t f)

instance (Show1 (t (HFree t f)), Show1 f) => Show1 (HFree t f) where
    liftShowsPrec sp sl d = \case
      HReturn x -> showsUnaryWith (liftShowsPrec sp sl) "HReturn" d x
      HJoin   x -> showsUnaryWith (liftShowsPrec sp sl) "HJoin"   d x

instance (Show1 (t (HFree t f)), Show1 f, Show a) => Show (HFree t f a) where
    showsPrec = liftShowsPrec showsPrec showList

instance HFunctor t => HFunctor (HFree t) where
    hmap :: forall f g. (f ~> g) -> HFree t f ~> HFree t g
    hmap f = go
      where
        go :: HFree t f ~> HFree t g
        go = \case
          HReturn x -> HReturn (f x)
          HJoin   x -> HJoin (hmap go x)

class HFunctor t => Inject t where
    -- | Lift an @f@ into the enhanced @t f@ structure.  Analogous to
    -- 'lift' from 'MonadTrans'.
    inject :: f ~> t f

    {-# MINIMAL inject #-}

class HFunctor t => HBind t where
    hbind :: (f ~> t g) -> t f ~> t g

    {-# MINIMAL hbind #-}

instance Inject Coyoneda where
    inject = liftCoyoneda

instance Inject Ap where
    inject = liftAp

instance Inject ListF where
    inject = ListF . (:[])

instance Inject NonEmptyF where
    inject = NonEmptyF . (:| [])

instance Inject MaybeF where
    inject = MaybeF . Just

instance Inject Step where
    inject = Step 0

instance Inject Steps where
    inject = Steps . NEM.singleton 0

instance Inject Alt.Alt where
    inject = Alt.liftAlt

instance Inject Free where
    inject = liftFree

instance Inject Free1 where
    inject = liftFree1

instance Inject FA.Ap where
    inject = FA.liftAp

instance Inject FAF.Ap where
    inject = FAF.liftAp

instance Inject IdentityT where
    inject = coerce

instance Inject Lift where
    inject = Other

instance Inject MaybeApply where
    inject = MaybeApply . Left

instance Inject Backwards where
    inject = Backwards

instance Inject WrappedApplicative where
    inject = WrapApplicative

instance Inject (ReaderT r) where
    inject = ReaderT . const

instance Inject Reverse where
    inject = Reverse

instance (Inject s, Inject t) => Inject (ComposeT s t) where
    inject = ComposeT . inject . inject

instance HFunctor t => Inject (HLift t) where
    inject = HPure

instance HFunctor t => Inject (HFree t) where
    inject = HReturn

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

instance (HBind t, Inject t) => HBind (HLift t) where
    hbind f = \case
      HPure   x -> f x
      HOther x -> HOther $ (`hbind` x) $ \y -> case f y of
        HPure  z -> inject z
        HOther z -> z
