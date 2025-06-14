{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -Wno-deprecations #-}

-- |
-- Module      : Data.Functor.Contravariant.Divise
-- Copyright   : (c) Justin Le 2025
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- The contravariant counterpart of 'Apply': like 'Divisible', but without
-- 'conquer'.  This is only a part of this library currently for
-- compatibility, until it is (hopefully) merged into /semigroupoids/.
--
-- @since 0.3.0.0
module Data.Functor.Contravariant.Divise (
  Divise (..),
  (<:>),
  dsum1,
  WrappedDivisible (..),
) where

import Control.Applicative
import Control.Applicative.Backwards
import Control.Arrow
import Control.Monad.Trans.Except
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import qualified Control.Monad.Trans.RWS.Lazy as Lazy
import qualified Control.Monad.Trans.RWS.Strict as Strict
import Control.Monad.Trans.Reader
import qualified Control.Monad.Trans.State.Lazy as Lazy
import qualified Control.Monad.Trans.State.Strict as Strict
import qualified Control.Monad.Trans.Writer.Lazy as Lazy
import qualified Control.Monad.Trans.Writer.Strict as Strict
import Data.Deriving
import Data.Functor.Apply
import Data.Functor.Compose
import Data.Functor.Constant
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Divisible
import Data.Functor.Invariant
import Data.Functor.Product
import Data.Functor.Reverse
import qualified Data.Semigroup.Foldable as F1

#if MIN_VERSION_base(4,8,0)
import Data.Monoid (Alt(..))
#else
import Data.Monoid (Monoid(..))
#endif

#if MIN_VERSION_base(4,9,0) && !MIN_VERSION_base(4,12,0)
import Data.Semigroup (Semigroup(..))
#endif

#if MIN_VERSION_base(4,7,0) || defined(MIN_VERSION_tagged)
import Data.Proxy
#endif

#ifdef MIN_VERSION_StateVar
import Data.StateVar
#endif

#if __GLASGOW_HASKELL__ >= 702
#define GHC_GENERICS
import GHC.Generics
#endif

#if !MIN_VERSION_transformers(0,6,0)
import           Control.Monad.Trans.Error
import           Control.Monad.Trans.List
#endif

-- | The contravariant analogue of 'Apply'; it is
-- 'Divisible' without 'conquer'.
--
-- If one thinks of @f a@ as a consumer of @a@s, then 'divise' allows one
-- to handle the consumption of a value by splitting it between two
-- consumers that consume separate parts of @a@.
--
-- 'divise' takes the "splitting" method and the two sub-consumers, and
-- returns the wrapped/combined consumer.
--
-- All instances of 'Divisible' should be instances of 'Divise' with
-- @'divise' = 'divide'@.
--
-- The guarantee that a function polymorphic over of @'Divise' f@ provides
-- that @'Divisible' f@ doesn't that any input consumed will be passed to at
-- least one sub-consumer; it won't potentially disappear into the void, as
-- is possible if 'conquer' is available.
--
-- Mathematically, a functor being an instance of 'Divise' means that it is
-- "semgroupoidal" with respect to the contravariant (tupling) Day
-- convolution.  That is, it is possible to define a function @(f `Day` f)
-- a -> f a@ in a way that is associative.
class Contravariant f => Divise f where
  -- | Takes a "splitting" method and the two sub-consumers, and
  -- returns the wrapped/combined consumer.
  divise :: (a -> (b, c)) -> f b -> f c -> f a
  divise f x y = contramap f (divised x y)

  -- | Combine a consumer of @a@ with a consumer of @b@ to get a consumer
  -- of @(a, b)@.
  divised :: f a -> f b -> f (a, b)
  divised = divise id

  {-# MINIMAL divise | divised #-}

-- | The Contravariant version of '<|>': split the same input over two
-- different consumers.
(<:>) :: Divise f => f a -> f a -> f a
x <:> y = divise (\r -> (r, r)) x y

-- | Convenient helper function to build up a 'Divise' by splitting
-- input across many different @f a@s.  Most useful when used alongside
-- 'contramap':
--
-- @
-- dsum1 $ contramap get1 x
--    :| [ contramap get2 y
--       , contramap get3 z
--       ]
-- @
--
-- @since 0.3.3.0
dsum1 :: (F1.Foldable1 t, Divise f) => t (f a) -> f a
dsum1 = foldr1 (<:>) . F1.toNonEmpty

-- | Wrap a 'Divisible' to be used as a member of 'Divise'
newtype WrappedDivisible f a = WrapDivisible {unwrapDivisible :: f a}
  deriving (Generic, Eq, Show, Ord, Read, Functor, Foldable, Traversable)
  deriving newtype (Divisible, Contravariant)

deriveShow1 ''WrappedDivisible
deriveRead1 ''WrappedDivisible
deriveEq1 ''WrappedDivisible
deriveOrd1 ''WrappedDivisible

instance Contravariant f => Invariant (WrappedDivisible f) where
  invmap _ g (WrapDivisible x) = WrapDivisible (contramap g x)

instance Divisible f => Divise (WrappedDivisible f) where
  divise f (WrapDivisible x) (WrapDivisible y) = WrapDivisible (divide f x y)

#if MIN_VERSION_base(4,9,0)
-- | Unlike 'Divisible', requires only 'Semigroup' on @r@.
instance Semigroup r => Divise (Op r) where
    divise f (Op g) (Op h) = Op $ \a -> case f a of
      (b, c) -> g b <> h c

-- | Unlike 'Divisible', requires only 'Semigroup' on @m@.
instance Semigroup m => Divise (Const m) where
    divise _ (Const a) (Const b) = Const (a <> b)

-- | Unlike 'Divisible', requires only 'Semigroup' on @m@.
instance Semigroup m => Divise (Constant m) where
    divise _ (Constant a) (Constant b) = Constant (a <> b)
#else
instance Monoid r => Divise (Op r) where divise = divide
instance Monoid m => Divise (Const m) where divise = divide
instance Monoid m => Divise (Constant m) where divise = divide
#endif

instance Divise Comparison where divise = divide
instance Divise Equivalence where divise = divide
instance Divise Predicate where divise = divide

#if MIN_VERSION_base(4,7,0) || defined(MIN_VERSION_tagged)
instance Divise Proxy where divise = divide
#endif

#ifdef MIN_VERSION_StateVar
instance Divise SettableStateVar where divise = divide
#endif

#if MIN_VERSION_base(4,8,0)
instance Divise f => Divise (Alt f) where
  divise f (Alt l) (Alt r) = Alt $ divise f l r
#endif

#ifdef GHC_GENERICS
instance Divise U1 where divise = divide
instance Divise V1 where divise _ = \case {}

instance Divise f => Divise (Rec1 f) where
  divise f (Rec1 l) (Rec1 r) = Rec1 $ divise f l r

instance Divise f => Divise (M1 i c f) where
  divise f (M1 l) (M1 r) = M1 $ divise f l r

instance (Divise f, Divise g) => Divise (f :*: g) where
  divise f (l1 :*: r1) (l2 :*: r2) = divise f l1 l2 :*: divise f r1 r2

-- | Unlike 'Divisible', requires only 'Apply' on @f@.
instance (Apply f, Divise g) => Divise (f :.: g) where
  divise f (Comp1 l) (Comp1 r) = Comp1 (liftF2 (divise f) l r)
#endif

instance Divise f => Divise (Backwards f) where
  divise f (Backwards l) (Backwards r) = Backwards $ divise f l r

instance Divise m => Divise (ExceptT e m) where
  divise f (ExceptT l) (ExceptT r) = ExceptT $ divise (funzip . fmap f) l r

instance Divise f => Divise (IdentityT f) where
  divise f (IdentityT l) (IdentityT r) = IdentityT $ divise f l r

#if !MIN_VERSION_transformers(0,6,0)
instance Divise m => Divise (ErrorT e m) where
  divise f (ErrorT l) (ErrorT r) = ErrorT $ divise (funzip . fmap f) l r

instance Divise m => Divise (ListT m) where
  divise f (ListT l) (ListT r) = ListT $ divise (funzip . map f) l r
#endif

instance Divise m => Divise (MaybeT m) where
  divise f (MaybeT l) (MaybeT r) = MaybeT $ divise (funzip . fmap f) l r

instance Divise m => Divise (ReaderT r m) where
  divise abc (ReaderT rmb) (ReaderT rmc) = ReaderT $ \r -> divise abc (rmb r) (rmc r)

instance Divise m => Divise (Lazy.RWST r w s m) where
  divise abc (Lazy.RWST rsmb) (Lazy.RWST rsmc) = Lazy.RWST $ \r s ->
    divise
      ( \ ~(a, s', w) -> case abc a of
          ~(b, c) -> ((b, s', w), (c, s', w))
      )
      (rsmb r s)
      (rsmc r s)

instance Divise m => Divise (Strict.RWST r w s m) where
  divise abc (Strict.RWST rsmb) (Strict.RWST rsmc) = Strict.RWST $ \r s ->
    divise
      ( \(a, s', w) -> case abc a of
          (b, c) -> ((b, s', w), (c, s', w))
      )
      (rsmb r s)
      (rsmc r s)

instance Divise m => Divise (Lazy.StateT s m) where
  divise f (Lazy.StateT l) (Lazy.StateT r) = Lazy.StateT $ \s ->
    divise (lazyFanout f) (l s) (r s)

instance Divise m => Divise (Strict.StateT s m) where
  divise f (Strict.StateT l) (Strict.StateT r) = Strict.StateT $ \s ->
    divise (strictFanout f) (l s) (r s)

instance Divise m => Divise (Lazy.WriterT w m) where
  divise f (Lazy.WriterT l) (Lazy.WriterT r) =
    Lazy.WriterT $
      divise (lazyFanout f) l r

instance Divise m => Divise (Strict.WriterT w m) where
  divise f (Strict.WriterT l) (Strict.WriterT r) =
    Strict.WriterT $
      divise (strictFanout f) l r

-- | Unlike 'Divisible', requires only 'Apply' on @f@.
instance (Apply f, Divise g) => Divise (Compose f g) where
  divise f (Compose l) (Compose r) = Compose (liftF2 (divise f) l r)

instance (Divise f, Divise g) => Divise (Product f g) where
  divise f (Pair l1 r1) (Pair l2 r2) = Pair (divise f l1 l2) (divise f r1 r2)

instance Divise f => Divise (Reverse f) where
  divise f (Reverse l) (Reverse r) = Reverse $ divise f l r

lazyFanout :: (a -> (b, c)) -> (a, s) -> ((b, s), (c, s))
lazyFanout f ~(a, s) = case f a of
  ~(b, c) -> ((b, s), (c, s))

strictFanout :: (a -> (b, c)) -> (a, s) -> ((b, s), (c, s))
strictFanout f (a, s) = case f a of
  (b, c) -> ((b, s), (c, s))

funzip :: Functor f => f (a, b) -> (f a, f b)
funzip = fmap fst &&& fmap snd

-- TODO: WrappedContravariant
