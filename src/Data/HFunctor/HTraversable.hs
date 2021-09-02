-- |
-- Module      : Data.HFunctor.HTraversable
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides a "higher-order" version of 'Traversable' and 'Traversable1',
-- in the same way that 'HFunctor' is a higher-order version of 'Functor'.
--
-- Note that in theory we could have 'HFoldable' as well, in the hierarchy,
-- to represent something that does not have an 'HFunctor' instance.
-- But it is not clear exactly why it would be useful as an abstraction.
-- This may be added in the future if use cases pop up.  For the most part,
-- the things you would want to do with an 'HFoldable', you could do with
-- 'hfoldMap' or 'iget'; it could in theory be useful for things without
-- 'HTraversable' or 'Interpret' instances, but it isn't clear what those
-- instances might be.
--
-- For instances of 'Interpret', there is some overlap with the
-- functionality of 'iget', 'icollect', and 'icollect1'.
--
-- @since 0.3.6.0
module Data.HFunctor.HTraversable (
  -- * 'HTraversable'
    HTraversable(..)
  , hsequence, hfoldMap, htoList, hmapDefault, hfor
  -- * 'HTraversable1'
  , HTraversable1(..)
  , hsequence1, hfoldMap1, htoNonEmpty, hfor1
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Comonad.Trans.Env
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Maybe
import           Control.Natural
import           Data.Bifunctor.Joker
import           Data.Bitraversable
import           Data.Coerce
import           Data.Functor.Apply
import           Data.Functor.Coyoneda
import           Data.Functor.Day                    (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Functor.Reverse
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.HFunctor
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
import           Data.List.NonEmpty                  (NonEmpty)
import           Data.Semigroup                      (Endo(..))
import           Data.Semigroup.Traversable
import           Data.Tagged
import           Data.Vinyl.CoRec
import           Data.Vinyl.Core                     (Rec)
import           Data.Vinyl.Recursive
import           GHC.Generics
import qualified Control.Alternative.Free            as Alt
import qualified Control.Applicative.Free            as Ap
import qualified Control.Applicative.Free.Fast       as FAF
import qualified Control.Applicative.Free.Final      as FA
import qualified Control.Applicative.Lift            as Lift
import qualified Data.Functor.Contravariant.Coyoneda as CCY
import qualified Data.Functor.Invariant.Day          as ID
import qualified Data.Functor.Invariant.Night        as IN
import qualified Data.SOP                            as SOP


-- | A higher-kinded version of 'Traversable1', in the same way that
-- 'HFunctor' is the higher-kinded version of 'Functor'.  Gives you an
-- "effectful" 'hmap', in the same way that 'traverse1' gives you an
-- effectful 'fmap', guaranteeing at least one item.
--
-- The typical analogues of 'Traversable1' laws apply.
--
-- @since 0.3.6.0
class HTraversable t => HTraversable1 t where
    -- | An "effectful" 'hmap', in the same way that 'traverse1' is an
    -- effectful 'fmap', guaranteeing at least one item.
    htraverse1 :: Apply h => (forall x. f x -> h (g x)) -> t f a -> h (t g a)

-- | A wrapper over a common pattern of "inverting" layers of a functor
-- combinator that always contains at least one @f@ item.
--
-- @since 0.3.6.0
hsequence1 :: (HTraversable1 t, Apply h) => t (h :.: f) a -> h (t f a)
hsequence1 = htraverse1 unComp1

-- | Collect all the @f x@s inside a @t f a@ into a semigroupoidal result
-- using a projecting function.
--
-- See 'iget'.
--
-- @since 0.3.6.0
hfoldMap1 :: (HTraversable1 t, Semigroup m) => (forall x. f x -> m) -> t f a -> m
hfoldMap1 f = getConst . htraverse1 (Const . f)

-- | Collect all the @f x@s inside a @t f a@ into a non-empty list, using
-- a projecting function.
--
-- See 'icollect1'.
--
-- @since 0.3.6.0
htoNonEmpty :: HTraversable1 t => (forall x. f x -> b) -> t f a -> NonEmpty b
htoNonEmpty f = fromNDL . hfoldMap1 (ndlSingleton . f)

-- | A flipped version of 'htraverse1'.
--
-- @since 0.4.0.0
hfor1 :: (HTraversable1 t, Apply h) => t f a -> (forall x. f x -> h (g x)) -> h (t g a)
hfor1 x f = htraverse1 f x

-- | A higher-kinded version of 'Traversable', in the same way that
-- 'HFunctor' is the higher-kinded version of 'Functor'.  Gives you an
-- "effectful" 'hmap', in the same way that 'traverse' gives you an
-- effectful 'fmap'.
--
-- The typical analogues of 'Traversable' laws apply.
--
-- @since 0.3.6.0
class HFunctor t => HTraversable t where
    -- | An "effectful" 'hmap', in the same way that 'traverse' is an
    -- effectful 'fmap'.
    htraverse :: Applicative h => (forall x. f x -> h (g x)) -> t f a -> h (t g a)

-- | A wrapper over a common pattern of "inverting" layers of a functor
-- combinator.
--
-- @since 0.3.6.0
hsequence :: (HTraversable t, Applicative h) => t (h :.: f) a -> h (t f a)
hsequence = htraverse unComp1

-- | Collect all the @f x@s inside a @t f a@ into a monoidal result using
-- a projecting function.
--
-- See 'iget'.
--
-- @since 0.3.6.0
hfoldMap :: (HTraversable t, Monoid m) => (forall x. f x -> m) -> t f a -> m
hfoldMap f = getConst . htraverse (Const . f)

-- | Collect all the @f x@s inside a @t f a@ into a list, using
-- a projecting function.
--
-- See 'icollect'.
--
-- @since 0.3.6.0
htoList :: HTraversable t => (forall x. f x -> b) -> t f a -> [b]
htoList f = flip appEndo [] . hfoldMap (Endo . (:) . f)

-- | A flipped version of 'htraverse'.
--
-- @since 0.4.0.0
hfor :: (HTraversable t, Applicative h) => t f a -> (forall x. f x -> h (g x)) -> h (t g a)
hfor x f = htraverse f x

-- | An implementation of 'hmap' defined using 'htraverse'.
--
-- @since 0.3.6.0
hmapDefault :: HTraversable t => (f ~> g) -> t f ~> t g
hmapDefault f = runIdentity . htraverse (Identity . f)

instance HTraversable Coyoneda where
    htraverse f (Coyoneda g x) = Coyoneda g <$> f x

instance HTraversable1 Coyoneda where
    htraverse1 f (Coyoneda g x) = Coyoneda g <$> f x

instance HTraversable CCY.Coyoneda where
    htraverse f (CCY.Coyoneda g x) = CCY.Coyoneda g <$> f x

instance HTraversable1 CCY.Coyoneda where
    htraverse1 f (CCY.Coyoneda g x) = CCY.Coyoneda g <$> f x

instance HTraversable Ap where
    htraverse :: forall f g h a. Applicative h => (forall x. f x -> h (g x)) -> Ap f a -> h (Ap g a)
    htraverse f = go
      where
        go :: Ap f b -> h (Ap g b)
        go = \case
          Ap.Pure x  -> pure (Ap.Pure x)
          Ap.Ap x xs -> Ap.Ap <$> f x <*> go xs

instance HTraversable ListF where
    htraverse f (ListF xs) = ListF <$> traverse f xs

instance HTraversable NonEmptyF where
    htraverse f (NonEmptyF xs) = NonEmptyF <$> traverse f xs

instance HTraversable1 NonEmptyF where
    htraverse1 f (NonEmptyF xs) = NonEmptyF <$> traverse1 f xs

instance HTraversable MaybeF where
    htraverse f (MaybeF xs) = MaybeF <$> traverse f xs

instance HTraversable (MapF k) where
    htraverse f (MapF xs) = MapF <$> traverse f xs

instance HTraversable (NEMapF k) where
    htraverse f (NEMapF xs) = NEMapF <$> traverse f xs

instance HTraversable1 (NEMapF k) where
    htraverse1 f (NEMapF xs) = NEMapF <$> traverse1 f xs

instance HTraversable Alt.Alt where
    htraverse f (Alt.Alt xs) = Alt.Alt <$> traverse (htraverse f) xs

instance HTraversable Alt.AltF where
    htraverse f = \case
      Alt.Ap x xs -> Alt.Ap <$> f x <*> htraverse f xs
      Alt.Pure x  -> pure (Alt.Pure x)

instance HTraversable Step where
    htraverse f (Step n x) = Step n <$> f x

instance HTraversable1 Step where
    htraverse1 f (Step n x) = Step n <$> f x

instance HTraversable Steps where
    htraverse f (Steps x) = Steps <$> traverse f x

instance HTraversable1 Steps where
    htraverse1 f (Steps x) = Steps <$> traverse1 f x

instance HTraversable Flagged where
    htraverse f (Flagged b x) = Flagged b <$> f x

instance HTraversable1 Flagged where
    htraverse1 f (Flagged b x) = Flagged b <$> f x

instance HTraversable MaybeT where
    htraverse f (MaybeT x) = MaybeT <$> f x

instance HTraversable1 MaybeT where
    htraverse1 f (MaybeT x) = MaybeT <$> f x

instance HTraversable FAF.Ap where
    htraverse = itraverse

instance HTraversable FA.Ap where
    htraverse = itraverse

instance HTraversable IdentityT where
    htraverse f (IdentityT x) = IdentityT <$> f x

instance HTraversable1 IdentityT where
    htraverse1 f (IdentityT x) = IdentityT <$> f x

instance HTraversable Lift where
    htraverse f = \case
      Lift.Pure  x -> pure (Lift.Pure x)
      Lift.Other y -> Lift.Other <$> f y

instance HTraversable MaybeApply where
    htraverse f (MaybeApply x) = MaybeApply <$> bitraverse f pure x

instance HTraversable Backwards where
    htraverse f (Backwards x) = Backwards <$> f x

instance HTraversable WrappedApplicative where
    htraverse f (WrapApplicative x) = WrapApplicative <$> f x

instance HTraversable Tagged where
    htraverse _ = pure . coerce

instance HTraversable Reverse where
    htraverse f (Reverse x) = Reverse <$> f x

instance HTraversable1 Reverse where
    htraverse1 f (Reverse x) = Reverse <$> f x

instance (HTraversable s, HTraversable t) => HTraversable (ComposeT s t) where
    htraverse f (ComposeT x) = ComposeT <$> htraverse (htraverse f) x

instance Traversable f => HTraversable ((:.:) f) where
    htraverse f (Comp1 x) = Comp1 <$> traverse f x

instance Traversable1 f => HTraversable1 ((:.:) f) where
    htraverse1 f (Comp1 x) = Comp1 <$> traverse1 f x

instance HTraversable (M1 i c) where
    htraverse f (M1 x) = M1 <$> f x

instance HTraversable1 (M1 i c) where
    htraverse1 f (M1 x) = M1 <$> f x

instance HTraversable Void2 where
    htraverse _ = \case {}

instance HTraversable1 Void2 where
    htraverse1 _ = \case {}

instance HTraversable (EnvT e) where
    htraverse f (EnvT e x) = EnvT e <$> f x

instance HTraversable1 (EnvT e) where
    htraverse1 f (EnvT e x) = EnvT e <$> f x

instance HTraversable Rec where
    htraverse = rtraverse

instance HTraversable CoRec where
    htraverse f (CoRec x) = CoRec <$> f x

instance HTraversable SOP.NP where
    htraverse :: forall f g h a. Applicative h => (forall x. f x -> h (g x)) -> SOP.NP f a -> h (SOP.NP g a)
    htraverse f = go
      where
        go :: SOP.NP f b -> h (SOP.NP g b)
        go = \case
          SOP.Nil     -> pure SOP.Nil
          x SOP.:* xs -> (SOP.:*) <$> f x <*> go xs

instance HTraversable SOP.NS where
    htraverse :: forall f g h a. Applicative h => (forall x. f x -> h (g x)) -> SOP.NS f a -> h (SOP.NS g a)
    htraverse f = go
      where
        go :: SOP.NS f b -> h (SOP.NS g b)
        go = \case
          SOP.Z x  -> SOP.Z <$> f x
          SOP.S xs -> SOP.S <$> go xs

instance HTraversable1 SOP.NS where
    htraverse1
        :: forall f g h a. Apply h
        => (forall x. f x -> h (g x))
        -> SOP.NS f a
        -> h (SOP.NS g a)
    htraverse1 f = go
      where
        go :: SOP.NS f b -> h (SOP.NS g b)
        go = \case
          SOP.Z x  -> SOP.Z <$> f x
          SOP.S xs -> SOP.S <$> go xs

instance HTraversable (Day f) where
    htraverse f (Day x y g) = (\y' -> Day x y' g) <$> f y

instance HTraversable1 (Day f) where
    htraverse1 f (Day x y g) = (\y' -> Day x y' g) <$> f y

instance HTraversable (ID.Day f) where
    htraverse f (ID.Day x y g h) = (\y' -> ID.Day x y' g h) <$> f y

instance HTraversable1 (ID.Day f) where
    htraverse1 f (ID.Day x y g h) = (\y' -> ID.Day x y' g h) <$> f y

instance HTraversable (IN.Night f) where
    htraverse f (IN.Night x y g h j) = (\y' -> IN.Night x y' g h j) <$> f y

instance HTraversable1 (IN.Night f) where
    htraverse1 f (IN.Night x y g h j) = (\y' -> IN.Night x y' g h j) <$> f y

instance HTraversable ((:*:) f) where
    htraverse f (x :*: y) = (x :*:) <$> f y

instance HTraversable1 ((:*:) f) where
    htraverse1 f (x :*: y) = (x :*:) <$> f y

instance HTraversable ((:+:) f) where
    htraverse f = \case
      L1 x -> pure (L1 x)
      R1 y -> R1 <$> f y

instance HTraversable (Product f) where
    htraverse f (Pair x y) = Pair x <$> f y

instance HTraversable1 (Product f) where
    htraverse1 f (Pair x y) = Pair x <$> f y

instance HTraversable (Sum f) where
    htraverse f = \case
      InL x -> pure (InL x)
      InR y -> InR <$> f y

instance HTraversable (Joker f) where
    htraverse _ = pure . coerce

instance HTraversable (These1 f) where
    htraverse f = \case
      This1  x   -> pure $ This1 x
      That1    y -> That1 <$> f y
      These1 x y -> These1 x <$> f y

instance HTraversable (Void3 f) where
    htraverse _ = \case {}

instance HTraversable ProxyF where
    htraverse _ = pure . coerce

instance HTraversable (ConstF e) where
    htraverse _ = pure . coerce

instance HTraversable t => HTraversable (HLift t) where
    htraverse f = \case
      HPure  x -> HPure  <$> f x
      HOther x -> HOther <$> htraverse f x

instance HTraversable1 t => HTraversable1 (HLift t) where
    htraverse1 f = \case
      HPure  x -> HPure  <$> f x
      HOther x -> HOther <$> htraverse1 f x

instance HTraversable t => HTraversable (HFree t) where
    htraverse :: forall f g h a. Applicative h => (forall x. f x -> h (g x)) -> HFree t f a -> h (HFree t g a)
    htraverse f = go
      where
        go :: HFree t f b -> h (HFree t g b)
        go = \case
          HReturn x -> HReturn <$> f x
          HJoin   x -> HJoin   <$> htraverse go x

instance HTraversable1 t => HTraversable1 (HFree t) where
    htraverse1 :: forall f g h a. Apply h => (forall x. f x -> h (g x)) -> HFree t f a -> h (HFree t g a)
    htraverse1 f = go
      where
        go :: HFree t f b -> h (HFree t g b)
        go = \case
          HReturn x -> HReturn <$> f x
          HJoin   x -> HJoin   <$> htraverse1 go x

