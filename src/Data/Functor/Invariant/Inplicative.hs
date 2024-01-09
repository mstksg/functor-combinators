{-# LANGUAGE CPP                       #-}
{-# LANGUAGE DerivingVia               #-}
{-# OPTIONS_GHC -fno-warn-deprecations #-}

-- |
-- Module      : Data.Functor.Invariant.Inplicative
-- Copyright   : (c) Justin Le 2021
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Contains the classes 'Inply' and 'Inplicative', the invariant
-- counterparts to 'Apply'/'Divise' and 'Applicative'/'Divisible'.
--
-- @since 0.4.0.0
module Data.Functor.Invariant.Inplicative (
  -- * Typeclass
    Inply(..)
  , Inplicative(..)
  -- * Deriving
  , WrappedApplicativeOnly(..)
  , WrappedDivisibleOnly(..)
  -- * Invariant 'Day'
  , runDay
  , dather
  , runDayApply
  , runDayDivise
  -- * Assembling Helpers
  , gatheredN
  , gatheredNMap
  , gatheredN1
  , gatheredN1Map
  , gatheredNRec
  , gatheredNMapRec
  , gatheredN1Rec
  , gatheredN1MapRec
  , gatherN
  , gatherN1
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards               (Backwards(..))
import           Control.Applicative.Lift                    (Lift(Pure, Other))
import           Control.Arrow                               (Arrow)
import           Control.Monad.Trans.Cont                    (ContT)
import           Control.Monad.Trans.Except                  (ExceptT(..))
import           Control.Monad.Trans.Identity                (IdentityT(..))
import           Control.Monad.Trans.Maybe                   (MaybeT(..))
import           Control.Monad.Trans.RWS                     (RWST(..))
import           Control.Monad.Trans.Reader                  (ReaderT(..))
import           Control.Monad.Trans.State                   (StateT)
import           Control.Monad.Trans.Writer                  (WriterT(..))
import           Control.Natural
import           Data.Complex                                (Complex)
import           Data.Deriving
import           Data.Functor.Apply
import           Data.Functor.Bind.Class                     (Bind)
import           Data.Functor.Constant                       (Constant)
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Day
import           Data.Functor.Product                        (Product(..))
import           Data.Functor.Reverse                        (Reverse(..))
import           Data.Hashable                               (Hashable)
import           Data.Kind
import           Data.List.NonEmpty                          (NonEmpty)
import           Data.SOP hiding                             (hmap)
import           Data.Sequence                               (Seq)
import           Data.StateVar                               (SettableStateVar)
import           Data.Tagged                                 (Tagged)
import           Data.Tree                                   (Tree)
import           GHC.Generics                                (Generic)
import qualified Control.Monad.Trans.RWS.Strict as Strict    (RWST(..))
import qualified Control.Monad.Trans.State.Strict as Strict  (StateT)
import qualified Control.Monad.Trans.Writer.Strict as Strict (WriterT(..))
import qualified Data.HashMap.Lazy                           as HM
import qualified Data.IntMap                                 as IM
import qualified Data.Map                                    as M
import qualified Data.Monoid                                 as Monoid
import qualified Data.Semigroup                              as Semigroup
import qualified Data.Sequence.NonEmpty                      as NESeq
import qualified Data.Vinyl                                  as V
import qualified Data.Vinyl.Curry                            as V
import qualified Data.Vinyl.Functor                          as V
import qualified GHC.Generics                                as Generics

#if !MIN_VERSION_transformers(0,6,0)
import           Control.Monad.Trans.Error
import           Control.Monad.Trans.List
#endif

-- | The invariant counterpart of 'Apply' and 'Divise'.
--
-- Conceptually you can think of 'Apply' as, given a way to "combine" @a@ and
-- @b@ to @c@, lets you merge @f a@ (producer of @a@) and @f b@ (producer
-- of @b@) into a @f c@ (producer of @c@).  'Divise' can be thought of as,
-- given a way to "split" a @c@ into an @a@ and a @b@, lets you merge @f
-- a@ (consumer of @a@) and @f b@ (consumder of @b@) into a @f c@ (consumer
-- of @c@).
--
-- 'Inply', for 'gather', requires both a combining function and
-- a splitting function in order to merge @f b@ (producer and consumer of
-- @b@) and @f c@ (producer and consumer of @c@) into a @f a@.  You can
-- think of it as, for the @f a@, it "splits" the a into @b@ and @c@ with
-- the @a -> (b, c)@, feeds it to the original @f b@ and @f c@, and then
-- re-combines the output back into a @a@ with the @b -> c -> a@.
--
-- @since 0.4.0.0
class Invariant f => Inply f where
    -- | Like '<.>', '<*>', 'divise', or 'divide', but requires both
    -- a splitting and a recombining function.  '<.>' and '<*>' require
    -- only a combining function, and 'divise' and 'divide' require only
    -- a splitting function.
    --
    -- It is used to merge @f b@ (producer and consumer of @b@) and @f c@
    -- (producer and consumer of @c@) into a @f a@.  You can think of it
    -- as, for the @f a@, it "splits" the a into @b@ and @c@ with the @a ->
    -- (b, c)@, feeds it to the original @f b@ and @f c@, and then
    -- re-combines the output back into a @a@ with the @b -> c -> a@.
    --
    -- An important property is that it will always use @both@ of the
    -- ccomponents given in order to fulfil its job.  If you gather an @f
    -- a@ and an @f b@ into an @f c@, in order to consume/produdce the @c@,
    -- it will always use both the @f a@ or the @f b@ -- exactly one of
    -- them.
    --
    -- @since 0.4.0.0
    gather
        :: (b -> c -> a)
        -> (a -> (b, c))
        -> f b
        -> f c
        -> f a
    gather f g x y = invmap (uncurry f) g (gathered x y)
    -- | A simplified version of 'gather' that combines into a tuple.  You
    -- can then use 'invmap' to reshape it into the proper shape.
    --
    -- @since 0.4.0.0
    gathered
        :: f a
        -> f b
        -> f (a, b)
    gathered = gather (,) id
    {-# MINIMAL gather | gathered #-}

-- | The invariant counterpart of 'Applicative' and 'Divisible'.
--
-- The main important action is described in 'Inply', but this adds 'knot',
-- which is the counterpart to 'pure' and 'conquer'.  It's the identity to
-- 'gather'; if combine two @f a@s with 'gather', and one of them is
-- 'knot', it will leave the structure unchanged.
--
-- Conceptually, if you think of 'gather' as "splitting and re-combining"
-- along multiple forks, then 'knot' introduces a fork that is never taken.
--
-- @since 0.4.0.0
class Inply f => Inplicative f where
    knot :: a -> f a

-- | Interpret out of a contravariant 'Day' into any instance of 'Inply' by
-- providing two interpreting functions.
--
-- This should go in "Data.Functor.Invariant.Day", but that module is in
-- a different package.
--
-- @since 0.4.0.0
runDay
    :: Inply h
    => (f ~> h)
    -> (g ~> h)
    -> Day f g ~> h
runDay f g (Day x y a b) = gather a b (f x) (g y)

-- | Squash the two items in a 'Day' using their natural 'Inply'
-- instances.
--
-- This should go in "Data.Functor.Invariant.Day", but that module is in
-- a different package.
--
-- @since 0.4.0.0
dather
    :: Inply f
    => Day f f ~> f
dather (Day x y a b) = gather a b x y

-- | Ignores the contravariant part of 'gather'
instance Apply f => Inply (WrappedFunctor f) where
    gather f _ (WrapFunctor x) (WrapFunctor y) = WrapFunctor (liftF2 f x y)
    gathered (WrapFunctor x) (WrapFunctor y) = WrapFunctor (liftF2 (,) x y)
-- | @'knot' = 'pure'@
instance (Applicative f, Apply f) => Inplicative (WrappedFunctor f) where
    knot = pure

-- | Ignores the covariant part of 'gather'
instance Divise f => Inply (WrappedContravariant f) where
    gather _ g (WrapContravariant x) (WrapContravariant y) = WrapContravariant (divise g x y)
    gathered (WrapContravariant x) (WrapContravariant y) = WrapContravariant (divised x y)
-- | @'knot' _ = 'conquer'@
instance (Divisible f, Divise f) => Inplicative (WrappedContravariant f) where
    knot _ = conquer

-- | Ignores the covariant part of 'gather'
instance Divise f => Inply (WrappedDivisible f) where
    gather _ g (WrapDivisible x) (WrapDivisible y) = WrapDivisible (divise g x y)
    gathered (WrapDivisible x) (WrapDivisible y) = WrapDivisible (divised x y)
-- | @'knot' _ = 'conquer'@
instance (Divisible f, Divise f) => Inplicative (WrappedDivisible f) where
    knot _ = conquer

-- | Wrap an 'Applicative' that is not necessarily an 'Apply'.
newtype WrappedApplicativeOnly f a =
    WrapApplicativeOnly { unwrapApplicativeOnly :: f a }
  deriving (Generic, Eq, Show, Ord, Read, Functor, Foldable, Traversable)
  deriving newtype (Applicative, Monad)

deriveShow1 ''WrappedApplicativeOnly
deriveRead1 ''WrappedApplicativeOnly
deriveEq1 ''WrappedApplicativeOnly
deriveOrd1 ''WrappedApplicativeOnly

instance Invariant f => Invariant (WrappedApplicativeOnly f) where
    invmap f g (WrapApplicativeOnly x) = WrapApplicativeOnly (invmap f g x)
instance (Applicative f, Invariant f) => Apply (WrappedApplicativeOnly f) where
    x <.> y = x <*> y
-- | Ignores the contravariant part of 'gather'
instance (Applicative f, Invariant f) => Inply (WrappedApplicativeOnly f) where
    gather f _ (WrapApplicativeOnly x) (WrapApplicativeOnly y) = WrapApplicativeOnly (liftA2 f x y)
    gathered (WrapApplicativeOnly x) (WrapApplicativeOnly y) = WrapApplicativeOnly (liftA2 (,) x y)
-- | @'knot' = 'pure'@
instance (Applicative f, Invariant f) => Inplicative (WrappedApplicativeOnly f) where
    knot = pure

-- | Wrap an 'Divisible' that is not necessarily a 'Divise'.
newtype WrappedDivisibleOnly f a =
    WrapDivisibleOnly { unwrapDivisibleOnly :: f a }
  deriving (Generic, Eq, Show, Ord, Read, Functor, Foldable, Traversable)
  deriving newtype (Divisible, Contravariant)

deriveShow1 ''WrappedDivisibleOnly
deriveRead1 ''WrappedDivisibleOnly
deriveEq1 ''WrappedDivisibleOnly
deriveOrd1 ''WrappedDivisibleOnly

instance Invariant f => Invariant (WrappedDivisibleOnly f) where
    invmap f g (WrapDivisibleOnly x) = WrapDivisibleOnly (invmap f g x)
instance (Divisible f, Invariant f) => Divise (WrappedDivisibleOnly f) where
    divise g (WrapDivisibleOnly x) (WrapDivisibleOnly y) = WrapDivisibleOnly (divide g x y)
-- | Ignores the covariant part of 'gather'
instance (Divisible f, Invariant f) => Inply (WrappedDivisibleOnly f) where
    gather _ g (WrapDivisibleOnly x) (WrapDivisibleOnly y) = WrapDivisibleOnly (divide g x y)
    gathered (WrapDivisibleOnly x) (WrapDivisibleOnly y) = WrapDivisibleOnly (divided x y)
-- | @'knot' _ = 'conquer'@
instance (Divisible f, Invariant f) => Inplicative (WrappedDivisibleOnly f) where
    knot _ = conquer

funzip :: Functor f => f (a, b) -> (f a, f b)
funzip x = (fmap fst x, fmap snd x)

-- | @since 0.4.1.0
instance Inply f => Inply (MaybeT f) where
    gather f g (MaybeT x) (MaybeT y) = MaybeT $
      gather (liftA2 f) (funzip . fmap g) x y
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (MaybeT f) where
    knot x = MaybeT (knot (Just x))

-- | @since 0.4.1.0
instance (Inply f, Semigroup w) => Inply (WriterT w f) where
    gather f g (WriterT x) (WriterT y) = WriterT $
      gather (\case (a, q) -> \case (b, r) -> (f a b, q <> r))
             (\case (a, s) -> case g a of (b, c) -> ((b, s), (c, s)))
             x y
-- | @since 0.4.1.0
instance (Inplicative f, Monoid w) => Inplicative (WriterT w f) where
    knot x = WriterT (knot (x, mempty))

-- | @since 0.4.1.0
instance (Inply f, Semigroup w) => Inply (Strict.WriterT w f) where
    gather f g (Strict.WriterT x) (Strict.WriterT y) = Strict.WriterT $
      gather (\(~(a, q)) (~(b, r)) -> (f a b, q <> r))
             (\(~(a, s)) -> let ~(b, c) = g a in ((b, s), (c, s)))
             x y
-- | @since 0.4.1.0
instance (Inplicative f, Monoid w) => Inplicative (Strict.WriterT w f) where
    knot x = Strict.WriterT (knot (x, mempty))

-- | @since 0.4.1.0
instance Inply f => Inply (ReaderT r f) where
    gather f g (ReaderT x) (ReaderT y) = ReaderT $ \r ->
      gather f g (x r) (y r)
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (ReaderT r f) where
    knot x = ReaderT (\_ -> knot x)

-- | @since 0.4.1.0
instance Inply f => Inply (ExceptT e f) where
    gather f g (ExceptT x) (ExceptT y) = ExceptT $
      gather (liftA2 f) (funzip . fmap g) x y
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (ExceptT e f) where
    knot x = ExceptT (knot (Right x))

#if !MIN_VERSION_transformers(0,6,0)
-- | @since 0.4.1.0
instance Inply f => Inply (ErrorT e f) where
    gather f g (ErrorT x) (ErrorT y) = ErrorT $
      gather (liftA2 f) (funzip . fmap g) x y
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (ErrorT e f) where
    knot x = ErrorT (knot (Right x))

-- | @since 0.4.1.0
instance Inply f => Inply (ListT f) where
    gather f g (ListT x) (ListT y) = ListT $
      gather (liftA2 f) (funzip . fmap g) x y
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (ListT f) where
    knot x = ListT (knot [x])
#endif

-- | @since 0.4.1.0
deriving via WrappedFunctor (RWST r w s m) instance (Bind m, Invariant m, Semigroup w) => Inply (RWST r w s m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (RWST r w s m) instance (Monad m, Bind m, Invariant m, Monoid w) => Inplicative (RWST r w s m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Strict.RWST r w s m) instance (Bind m, Invariant m, Semigroup w) => Inply (Strict.RWST r w s m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Strict.RWST r w s m) instance (Monad m, Bind m, Invariant m, Monoid w) => Inplicative (Strict.RWST r w s m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (StateT s m) instance (Bind m, Invariant m) => Inply (StateT s m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (StateT s m) instance (Monad m, Bind m, Invariant m) => Inplicative (StateT s m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Strict.StateT s m) instance (Bind m, Invariant m) => Inply (Strict.StateT s m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Strict.StateT s m) instance (Monad m, Bind m, Invariant m) => Inplicative (Strict.StateT s m)

-- | @since 0.4.1.0
instance Inply f => Inply (Generics.M1 i t f :: Type -> Type) where
    gather f g (Generics.M1 x) (Generics.M1 y) = Generics.M1 (gather f g x y)
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (Generics.M1 i t f :: Type -> Type) where
    knot = Generics.M1 . knot
-- | @since 0.4.1.0
instance (Inply f, Inply g) => Inply (f Generics.:*: g) where
    gather f g (x1 Generics.:*: y1) (x2 Generics.:*: y2) =
        gather f g x1 x2 Generics.:*: gather f g y1 y2
-- | @since 0.4.1.0
instance (Inplicative f, Inplicative g) => Inplicative (f Generics.:*: g) where
    knot x = knot x Generics.:*: knot x
-- | @since 0.4.1.0
instance (Inply f, Inply g) => Inply (Product f g) where
    gather f g (Pair x1 y1) (Pair x2 y2) =
      gather f g x1 x2 `Pair` gather f g y1 y2
-- | @since 0.4.1.0
instance (Inplicative f, Inplicative g) => Inplicative (Product f g) where
    knot x = knot x `Pair` knot x
-- | @since 0.4.1.0
instance Inply f => Inply (Generics.Rec1 f :: Type -> Type) where
    gather f g (Generics.Rec1 x) (Generics.Rec1 y) = Generics.Rec1 (gather f g x y)
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (Generics.Rec1 f :: Type -> Type) where
    knot = Generics.Rec1 . knot
-- | @since 0.4.1.0
instance Inply f => Inply (Monoid.Alt f) where
    gather f g (Monoid.Alt x) (Monoid.Alt y) = Monoid.Alt (gather f g x y)
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (Monoid.Alt f) where
    knot = Monoid.Alt . knot
-- | @since 0.4.1.0
instance Inply f => Inply (IdentityT f :: Type -> Type) where
    gather f g (IdentityT x) (IdentityT y) = IdentityT (gather f g x y)
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (IdentityT f :: Type -> Type) where
    knot = IdentityT . knot
-- | @since 0.4.1.0
instance Inply f => Inply (Reverse f :: Type -> Type) where
    gather f g (Reverse x) (Reverse y) = Reverse (gather f g x y)
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (Reverse f :: Type -> Type) where
    knot = Reverse . knot
-- | @since 0.4.1.0
instance Inply f => Inply (Backwards f :: Type -> Type) where
    gather f g (Backwards x) (Backwards y) = Backwards (gather f g x y)
-- | @since 0.4.1.0
instance Inplicative f => Inplicative (Backwards f :: Type -> Type) where
    knot = Backwards . knot
-- | @since 0.4.1.0
instance Inply f => Inply (Lift f) where
    gather f g = \case
      Pure  x -> \case
        Pure  y -> Pure (f x y)
        Other y -> Other (invmap (f x) (snd . g) y)
      Other x -> \case
        Pure  y -> Other (invmap (`f` y) (fst . g) x)
        Other y -> Other (gather f g x y)
-- | @since 0.4.1.0
instance Inply f => Inplicative (Lift f) where
    knot = Pure

-- | @since 0.4.1.0
deriving via WrappedApplicativeOnly (Tagged a) instance Inply (Tagged a)
-- | @since 0.4.1.0
deriving via WrappedApplicativeOnly (Tagged a) instance Inplicative (Tagged a)

-- | @since 0.4.1.0
deriving via WrappedFunctor Identity instance Inply Identity
-- | @since 0.4.1.0
deriving via WrappedFunctor Identity instance Inplicative Identity
-- | @since 0.4.1.0
deriving via WrappedFunctor (Proxy :: Type -> Type) instance Inply Proxy
-- | @since 0.4.1.0
deriving via WrappedFunctor (Proxy :: Type -> Type) instance Inplicative Proxy
-- | @since 0.4.1.0
deriving via WrappedFunctor [] instance Inply []
-- | @since 0.4.1.0
deriving via WrappedFunctor [] instance Inplicative []
-- | @since 0.4.1.0
deriving via WrappedFunctor ((->) r) instance Inply ((->) r)
-- | @since 0.4.1.0
deriving via WrappedFunctor ((->) r) instance Inplicative ((->) r)
-- | @since 0.4.1.0
deriving via WrappedFunctor Maybe instance Inply Maybe
-- | @since 0.4.1.0
deriving via WrappedFunctor Maybe instance Inplicative Maybe
-- | @since 0.4.1.0
deriving via WrappedFunctor (Either e) instance Inply (Either e)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Either e) instance Inplicative (Either e)
-- | @since 0.4.1.0
deriving via WrappedFunctor IO instance Inply IO
-- | @since 0.4.1.0
deriving via WrappedFunctor IO instance Inplicative IO
-- | @since 0.4.1.0
deriving via WrappedFunctor Generics.Par1 instance Inply Generics.Par1
-- | @since 0.4.1.0
deriving via WrappedFunctor Generics.Par1 instance Inplicative Generics.Par1
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.U1 :: Type -> Type) instance Inply Generics.U1
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.U1 :: Type -> Type) instance Inplicative Generics.U1
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.K1 i c :: Type -> Type) instance Semigroup c => Inply (Generics.K1 i c)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.K1 i c :: Type -> Type) instance Monoid c => Inplicative (Generics.K1 i c)
-- | @since 0.4.1.0
deriving via WrappedFunctor Complex instance Inply Complex
-- | @since 0.4.1.0
deriving via WrappedFunctor Complex instance Inplicative Complex
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Min instance Inply Semigroup.Min
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Min instance Inplicative Semigroup.Min
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Max instance Inply Semigroup.Max
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Max instance Inplicative Semigroup.Max
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.First instance Inply Semigroup.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.First instance Inplicative Semigroup.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Last instance Inply Semigroup.Last
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Last instance Inplicative Semigroup.Last

#if !MIN_VERSION_base(4,16,0)
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Option instance Inply Semigroup.Option
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Option instance Inplicative Semigroup.Option
#endif

-- | @since 0.4.1.0
deriving via WrappedFunctor ZipList instance Inply ZipList
-- | @since 0.4.1.0
deriving via WrappedFunctor ZipList instance Inplicative ZipList
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.First instance Inply Monoid.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.First instance Inplicative Monoid.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Last instance Inply Monoid.Last
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Last instance Inplicative Monoid.Last
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Dual instance Inply Monoid.Dual
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Dual instance Inplicative Monoid.Dual
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Sum instance Inply Monoid.Sum
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Sum instance Inplicative Monoid.Sum
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Product instance Inply Monoid.Product
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Product instance Inplicative Monoid.Product
-- | @since 0.4.1.0
deriving via WrappedFunctor NonEmpty instance Inply NonEmpty
-- | @since 0.4.1.0
deriving via WrappedFunctor NonEmpty instance Inplicative NonEmpty
-- | @since 0.4.1.0
deriving via WrappedFunctor Tree instance Inply Tree
-- | @since 0.4.1.0
deriving via WrappedFunctor Tree instance Inplicative Tree
-- | @since 0.4.1.0
deriving via WrappedFunctor Seq instance Inply Seq
-- | @since 0.4.1.0
deriving via WrappedFunctor Seq instance Inplicative Seq
-- | @since 0.4.1.0
deriving via WrappedFunctor NESeq.NESeq instance Inply NESeq.NESeq
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedArrow a b) instance Arrow a => Inply (WrappedArrow a b)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedArrow a b) instance Arrow a => Inplicative (WrappedArrow a b)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.V1 :: Type -> Type) instance Inply Generics.V1
-- | @since 0.4.1.0
deriving via WrappedFunctor IM.IntMap instance Inply IM.IntMap
-- | @since 0.4.1.0
deriving via WrappedFunctor (M.Map k) instance Ord k => Inply (M.Map k)

#if MIN_VERSION_base(4,16,0)
-- | Does not require Eq k since base-4.16
--
-- @since 0.4.1.0
deriving via WrappedFunctor (HM.HashMap k) instance Hashable k => Inply (HM.HashMap k)
#else
-- | @since 0.4.1.0
deriving via WrappedFunctor (HM.HashMap k) instance (Hashable k, Eq k) => Inply (HM.HashMap k)
#endif

-- | @since 0.4.1.0
deriving via WrappedFunctor (Const w :: Type -> Type) instance Semigroup w => Inply (Const w)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Const w :: Type -> Type) instance Monoid w => Inplicative (Const w)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Constant w :: Type -> Type) instance Semigroup w => Inply (Constant w)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Constant w :: Type -> Type) instance Monoid w => Inplicative (Constant w)
-- | @since 0.4.1.0
deriving via WrappedFunctor (ContT r (m :: Type -> Type)) instance Inply (ContT r m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (ContT r (m :: Type -> Type)) instance Inplicative (ContT r m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedMonad m) instance Monad m => Inply (WrappedMonad m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedMonad m) instance Monad m => Inplicative (WrappedMonad m)
-- | @since 0.4.1.0
deriving via WrappedFunctor ((,) w :: Type -> Type) instance Semigroup w => Inply ((,) w)
-- | @since 0.4.1.0
deriving via WrappedFunctor ((,) w :: Type -> Type) instance Monoid w => Inplicative ((,) w)

-- | @since 0.4.1.0
deriving via WrappedDivisible SettableStateVar instance Inply SettableStateVar
-- | @since 0.4.1.0
deriving via WrappedDivisible SettableStateVar instance Inplicative SettableStateVar
-- | @since 0.4.1.0
deriving via WrappedDivisible Predicate instance Inply Predicate
-- | @since 0.4.1.0
deriving via WrappedDivisible Predicate instance Inplicative Predicate
-- | @since 0.4.1.0
deriving via WrappedDivisible Comparison instance Inply Comparison
-- | @since 0.4.1.0
deriving via WrappedDivisible Comparison instance Inplicative Comparison
-- | @since 0.4.1.0
deriving via WrappedDivisible Equivalence instance Inply Equivalence
-- | @since 0.4.1.0
deriving via WrappedDivisible Equivalence instance Inplicative Equivalence
-- | @since 0.4.1.0
deriving via WrappedDivisible (Op r) instance Semigroup r => Inply (Op r)
-- | @since 0.4.1.0
deriving via WrappedDivisible (Op r) instance Monoid r => Inplicative (Op r)




-- | Convenient wrapper to build up an 'Inplicative' instance by providing
-- each component of it.  This makes it much easier to build up longer
-- chains because you would only need to write the splitting/joining
-- functions in one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MT Int Bool String
-- @
--
-- and an invariant functor and 'Inplicative' instance @Prim@
-- (representing, say, a bidirectional parser, where @Prim Int@ is
-- a bidirectional parser for an 'Int'@), then you could assemble
-- a bidirectional parser for a @MyType@ using:
--
-- @
-- invmap (\(MyType x y z) -> I x :* I y :* I z :* Nil)
--        (\(I x :* I y :* I z :* Nil) -> MyType x y z) $
--   gatheredN $ intPrim
--                    :* boolPrim
--                    :* stringPrim
--                    :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'knot' directly.
-- *    If you have 1 component, you don't need anything.
-- *    If you have 2 components, use 'gather' directly.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off tuples one-by-one.
--
-- @since 0.4.1.0
gatheredN
    :: Inplicative f
    => NP f as
    -> f (NP I as)
gatheredN = \case
    Nil     -> knot Nil
    x :* xs -> gather
      (\y ys -> I y :* ys)
      (\case I y :* ys -> (y, ys))
      x
      (gatheredN xs)

-- | Given a function to "break out" a data type into a 'NP' (tuple) and one to
-- put it back together from the tuple, 'gather' all of the components
-- together.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MT Int Bool String
-- @
--
-- and an invariant functor and 'Inplicative' instance @Prim@
-- (representing, say, a bidirectional parser, where @Prim Int@ is
-- a bidirectional parser for an 'Int'@), then you could assemble
-- a bidirectional parser for a @MyType@ using:
--
-- @
--   concaMapInplicative
--      (\(MyType x y z) -> I x :* I y :* I z :* Nil)
--      (\(I x :* I y :* I z :* Nil) -> MyType x y z)
--      $ intPrim
--     :* boolPrim
--     :* stringPrim
--     :* Nil
-- @
--
-- See notes on 'gatheredNMap' for more details and caveats.
--
-- @since 0.4.1.0
gatheredNMap
    :: Inplicative f
    => (NP I as -> b)
    -> (b -> NP I as)
    -> NP f as
    -> f b
gatheredNMap f g = invmap f g . gatheredN

-- | A version of 'gatheredN' for non-empty 'NP', but only
-- requiring an 'Inply' instance.
--
-- @since 0.4.1.0
gatheredN1
    :: Inply f
    => NP f (a ': as)
    -> f (NP I (a ': as))
gatheredN1 (x :* xs) = case xs of
    Nil    -> invmap ((:* Nil) . I) (\case I y :* _ -> y) x
    _ :* _ -> gather
      (\y ys -> I y :* ys)
      (\case I y :* ys -> (y, ys))
      x
      (gatheredN1 xs)

-- | A version of 'gatheredNMap' for non-empty 'NP', but only
-- requiring an 'Inply' instance.
--
-- @since 0.4.1.0
gatheredN1Map
    :: Inplicative f
    => (NP I (a ': as) -> b)
    -> (b -> NP I (a ': as))
    -> NP f (a ': as)
    -> f b
gatheredN1Map f g = invmap f g . gatheredN1

-- | A version of 'gatheredN' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of tuple components.
--
-- @since 0.4.1.0
gatheredNRec
    :: Inplicative f
    => V.Rec f as
    -> f (V.XRec V.Identity as)
gatheredNRec = \case
    V.RNil    -> knot V.RNil
    x V.:& xs -> gather
      (V.::&)
      (\case y V.::& ys -> (y, ys))
      x
      (gatheredNRec xs)

-- | A version of 'gatheredNMap' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of tuple components.
--
-- @since 0.4.1.0
gatheredNMapRec
    :: Inplicative f
    => (V.XRec V.Identity as -> b)
    -> (b -> V.XRec V.Identity as)
    -> V.Rec f as
    -> f b
gatheredNMapRec f g = invmap f g . gatheredNRec

-- | Convenient wrapper to 'gather' over multiple arguments using tine
-- vinyl library's multi-arity uncurrying facilities.  Makes it a lot more
-- convenient than using 'gather' multiple times and needing to accumulate
-- intermediate types.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MT Int Bool String
-- @
--
-- and an invariant functor and 'Inplicative' instance @Prim@
-- (representing, say, a bidirectional parser, where @Prim Int@ is
-- a bidirectional parser for an 'Int'@), then you could assemble
-- a bidirectional parser for a @MyType@ using:
--
-- @
-- 'gatherN'
--   MT                                         -- ^ curried assembling function
--   (\(MT x y z) -> x ::& y ::& z ::& XRNil)   -- ^ disassembling function
--   (intPrim :: Prim Int)
--   (boolPrim :: Prim Bool)
--   (stringPrim :: Prim String)
-- @
--
-- Really only useful with 3 or more arguments, since with two arguments
-- this is just 'gather' (and with zero arguments, you can just use
-- 'knot').
--
-- The generic type is a bit tricky to understand, but it's easier to
-- understand what's going on if you instantiate with concrete types:
--
-- @
-- ghci> :t gatherN @MyInplicative @'[Int, Bool, String]
--      (Int -> Bool -> String -> b)
--   -> (b -> XRec Identity '[Int, Bool, String])
--   -> MyInplicative Int
--   -> MyInplicative Bool
--   -> MyInplicative String
--   -> MyInplicative b
-- @
--
-- @since 0.4.1.0
gatherN
    :: forall f as b. (Inplicative f, V.IsoXRec V.Identity as, V.RecordCurry as)
    => V.Curried as b
    -> (b -> V.XRec V.Identity as)
    -> V.CurriedF f as (f b)
gatherN f g = V.rcurry @as @f $
    invmap (V.runcurry' f . V.fromXRec) g
  . gatheredNRec

-- | A version of 'gatheredN1' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @since 0.4.1.0
gatheredN1Rec
    :: Inply f
    => V.Rec f (a ': as)
    -> f (V.XRec V.Identity (a ': as))
gatheredN1Rec (x V.:& xs) = case xs of
    V.RNil   -> invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
    _ V.:& _ -> gather
      (V.::&)
      (\case y V.::& ys -> (y, ys))
      x
      (gatheredN1Rec xs)

-- | A version of 'gatheredNMap' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of tuple components.
--
-- @since 0.4.1.0
gatheredN1MapRec
    :: Inplicative f
    => (V.XRec V.Identity (a ': as) -> b)
    -> (b -> V.XRec V.Identity (a ': as))
    -> V.Rec f (a ': as)
    -> f b
gatheredN1MapRec f g = invmap f g . gatheredN1Rec

-- | 'gatherN' but with at least one argument, so can be used with any
-- 'Inply'.
--
-- @since 0.4.1.0
gatherN1
    :: forall f a as b. (Inply f, V.IsoXRec V.Identity as, V.RecordCurry as)
    => V.Curried (a ': as) b
    -> (b -> V.XRec V.Identity (a ': as))
    -> V.CurriedF f (a ': as) (f b)
gatherN1 f g = V.rcurry @(a ': as) @f $
    invmap (V.runcurry' f . V.fromXRec) g
  . gatheredN1Rec

-- | Interpret out of a contravariant 'Day' into any instance of 'Apply' by
-- providing two interpreting functions.
--
-- In theory, this should not need to exist, since you should always be
-- able to use 'runDay' because every instance of 'Apply' is also an
-- instance of 'Inply'.  However, this can be handy if you are using an
-- instance of 'Apply' that has no 'Inply' instance.  Consider also
-- 'unsafeInplyCo' if you are using a specific, concrete type for @h@.
runDayApply
    :: forall f g h. Apply h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayApply f g (Day x y j _) = liftF2 j (f x) (g y)

-- | Interpret out of a contravariant 'Day' into any instance of 'Divise'
-- by providing two interpreting functions.
--
-- In theory, this should not need to exist, since you should always be
-- able to use 'runDay' because every instance of 'Divise' is also an
-- instance of 'Inply'.  However, this can be handy if you are using an
-- instance of 'Divise' that has no 'Inply' instance.  Consider also
-- 'unsafeInplyContra' if you are using a specific, concrete type for @h@.
runDayDivise
    :: forall f g h. Divise h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayDivise f g (Day x y _ h) = divise h (f x) (g y)

