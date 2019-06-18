{-# LANGUAGE DeriveDataTypeable   #-}
{-# LANGUAGE DeriveFoldable       #-}
{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE DeriveTraversable    #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TemplateHaskell      #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

-- |
-- Module      : Data.HBifunctor
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides an abstraction for "two-argument functor
-- combinators", 'HBifunctor', as well as some useful combinators.
module Data.HBifunctor (
    HBifunctor(..)
  , WrappedHBifunctor(..)
  , overHBifunctor
  -- * Combinators
  , JoinT(..)
  , TannenT(..)
  , BiffT(..)
  , HClown(..)
  , HJoker(..)
  , LeftF(..)
  , RightF(..)
  ) where

import           Control.Natural.IsoF
import           Data.Biapplicative
import           Data.Bifunctor.TH
import           Data.Constraint.Trivial
import           Data.Data
import           Data.Deriving
import           Data.Functor.Classes
import           Data.HFunctor
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
import           Data.Kind
import           GHC.Generics

-- | Lift two isomorphisms on each side of a bifunctor to become an
-- isomorphism between the two bifunctor applications.
--
-- Basically, if @f@ and @f'@ are isomorphic, and @g@ and @g'@ are
-- isomorphic, then @t f g@ is isomorphic to @t f' g'@.
overHBifunctor
    :: HBifunctor t
    => (f <~> f')
    -> (g <~> g')
    -> t f g <~> t f' g'
overHBifunctor f g =
        isoF (hbimap (viewF   f) (viewF   g))
             (hbimap (reviewF f) (reviewF g))

-- | Form an 'HFunctor' by applying the same input twice to an
-- 'HBifunctor'.
newtype JoinT t f a = JoinT { runJoinT :: t f f a }

deriving instance Functor (t f f) => Functor (JoinT t f)

instance HBifunctor t => HFunctor (JoinT t) where
    hmap f (JoinT x) = JoinT $ hbimap f f x

-- | Form an 'HBifunctor' by wrapping another 'HBifunctor' in a 'HFunctor'.
newtype TannenT t p f g a = TannenT { runTannenT :: t (p f g) a }

deriving instance Functor (t (p f g)) => Functor (TannenT t p f g)

instance (HFunctor t, HBifunctor p) => HBifunctor (TannenT t p) where
    hbimap f g (TannenT x) = TannenT (hmap (hbimap f g) x)

deriving via (WrappedHBifunctor (TannenT (t :: (Type -> Type) -> Type -> Type) p) f)
    instance (HFunctor t, HBifunctor p) => HFunctor (TannenT t p f)

-- | Form an 'HBifunctor' over two 'HFunctor's.
newtype BiffT p s t f g a = BiffT { runBiffT :: p (s f) (t g) a }

deriving instance Functor (p (s f) (t g)) => Functor (BiffT p s t f g)

instance (HBifunctor p, HFunctor s, HFunctor t) => HBifunctor (BiffT p s t) where
    hbimap f g (BiffT x) = BiffT (hbimap (hmap f) (hmap g) x)

deriving via (WrappedHBifunctor (BiffT (p :: (Type -> Type) -> (Type -> Type) -> Type -> Type) s t) f)
    instance (HBifunctor p, HFunctor s, HFunctor t) => HFunctor (BiffT p s t f)

-- | Form an 'HBifunctor' over a 'HFunctor' by ignoring the second
-- argument.
newtype HClown t f g a = HClown { runHClown :: t f a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

instance Show1 (t f) => Show1 (HClown t f g) where
    liftShowsPrec sp sl d (HClown x) =
        showsUnaryWith (liftShowsPrec sp sl) "HClown" d x

instance (Read1 (t f)) => Read1 (HClown t f g) where
    liftReadsPrec rp rl = readsData $
            readsUnaryWith (liftReadsPrec rp rl) "HClown" HClown

instance Eq1 (t f) => Eq1 (HClown t f g) where
    liftEq eq (HClown x) (HClown y) = liftEq eq x y

instance Ord1 (t f) => Ord1 (HClown t f g) where
    liftCompare c (HClown x) (HClown y) = liftCompare c x y

instance HFunctor t => HBifunctor (HClown t) where
    hbimap f _ (HClown x) = HClown (hmap f x)

deriving via (WrappedHBifunctor (HClown t) f)
    instance HFunctor t => HFunctor (HClown t f)

-- | Form an 'HBifunctor' over a 'HFunctor' by ignoring the first
-- argument.
newtype HJoker t f g a = HJoker { runHJoker :: t g a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

instance Show1 (t g) => Show1 (HJoker t f g) where
    liftShowsPrec sp sl d (HJoker x) =
        showsUnaryWith (liftShowsPrec sp sl) "HJoker" d x

instance (Read1 (t g)) => Read1 (HJoker t f g) where
    liftReadsPrec rp rl = readsData $
            readsUnaryWith (liftReadsPrec rp rl) "HJoker" HJoker

instance HFunctor t => HBifunctor (HJoker t) where
    hbimap _ g (HJoker x) = HJoker (hmap g x)

deriving via (WrappedHBifunctor (HJoker t) f)
    instance HFunctor t => HFunctor (HJoker t f)

-- | An 'HBifunctor' that ignores its second input.  Like
-- a 'GHC.Generics.:+:' with no 'GHC.Generics.R1'/right branch.
--
-- This is 'Data.Bifunctors.Joker.Joker' from "Data.Bifunctors.Joker", but
-- given a more sensible name for its purpose.
newtype LeftF f g a = LeftF { runLeftF :: f a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''LeftF
deriveRead1 ''LeftF
deriveEq1 ''LeftF
deriveOrd1 ''LeftF
deriveBifunctor ''LeftF
deriveBifoldable ''LeftF
deriveBitraversable ''LeftF

instance Applicative f => Biapplicative (LeftF f) where
    bipure _ y = LeftF (pure y)
    LeftF x <<*>> LeftF y = LeftF (x <*> y)

instance HBifunctor LeftF where
    hbimap f _ (LeftF x) = LeftF (f x)

deriving via (WrappedHBifunctor LeftF f)
    instance HFunctor (LeftF f)

-- | An 'HBifunctor' that ignores its first input.  Like
-- a 'GHC.Generics.:+:' with no 'GHC.Generics.L1'/left branch.
--
-- In its polykinded form (on @f@), it is essentially a higher-order
-- version of 'Tagged'. 
newtype RightF f g a = RightF { runRightF :: g a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''RightF
deriveRead1 ''RightF
deriveEq1 ''RightF
deriveOrd1 ''RightF

instance HBifunctor RightF where
    hbimap _ g (RightF x) = RightF (g x)

deriving via (WrappedHBifunctor RightF f)
    instance HFunctor (RightF f)

instance HFunctor (RightF f) where
    hmap f (RightF x) = RightF (f x)

instance Inject (RightF f) where
    inject = RightF

instance HBind (RightF f) where
    hbind f (RightF x) = f x

instance Interpret (RightF f) where
    type C (RightF f) = Unconstrained
    retract (RightF x) = x
    interpret f (RightF x) = f x
