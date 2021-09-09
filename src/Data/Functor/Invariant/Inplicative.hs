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
  -- * Assembling Helpers
  , concatInplicative
  , concatInply
  , concatInplicativeRec
  , concatInplyRec
  , swerveN
  , swerveN1
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards        (Backwards)
import           Control.Applicative.Lift             (Lift(Pure))
import           Control.Arrow                        (Arrow)
import           Control.Comonad                      (Cokleisli)
import           Control.Monad.Trans.Cont             (ContT)
import           Control.Monad.Trans.Error            (ErrorT)
import           Control.Monad.Trans.Except           (ExceptT)
import           Control.Monad.Trans.Identity         (IdentityT)
import           Control.Monad.Trans.List             (ListT)
import           Control.Monad.Trans.Maybe            (MaybeT)
import           Control.Monad.Trans.RWS              (RWST)
import           Control.Monad.Trans.Reader           (ReaderT)
import           Control.Monad.Trans.Writer           (WriterT)
import           Control.Natural
import           Data.Biapplicative                   (Biapplicative)
import           Data.Complex                         (Complex)
import           Data.Deriving
import           Data.Functor.Apply
import           Data.Functor.Bind.Class              (Biapply, Bind)
import           Data.Functor.Compose                 (Compose)
import           Data.Functor.Constant                (Constant)
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Day
import           Data.Functor.Product                 (Product)
import           Data.Functor.Reverse                 (Reverse)
import           Data.Hashable                        (Hashable)
import           Data.Kind
import           Data.List.NonEmpty                   (NonEmpty)
import           Data.SOP hiding                      (hmap, Compose)
import           Data.Semigroupoid.Static             (Static)
import           Data.Sequence                        (Seq)
import           Data.Tagged                          (Tagged)
import           Data.Tree                            (Tree)
import           GHC.Generics                         (Generic)
import qualified Data.Bifunctor.Join                  as BFJ
import qualified Data.HashMap.Lazy                    as HM
import qualified Data.IntMap                          as IM
import qualified Data.Map                             as M
import qualified Data.Monoid                          as Monoid
import qualified Data.Semigroup                       as Semigroup
import qualified Data.Vinyl                           as V
import qualified Data.Vinyl.Curry                     as V
import qualified Data.Vinyl.Functor                   as V
import qualified Data.Vinyl.XRec                      as V
import qualified GHC.Generics                         as Generics

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

instance Apply f => Inply (WrappedFunctor f) where
    gather f _ (WrapFunctor x) (WrapFunctor y) = WrapFunctor (liftF2 f x y)
    gathered (WrapFunctor x) (WrapFunctor y) = WrapFunctor (liftF2 (,) x y)
instance (Applicative f, Apply f) => Inplicative (WrappedFunctor f) where
    knot = pure

instance Divise f => Inply (WrappedContravariant f) where
    gather _ g (WrapContravariant x) (WrapContravariant y) = WrapContravariant (divise g x y)
    gathered (WrapContravariant x) (WrapContravariant y) = WrapContravariant (divised x y)
instance (Divisible f, Divise f) => Inplicative (WrappedContravariant f) where
    knot _ = conquer

instance Divisible f => Inply (WrappedDivisible f) where
    gather _ g (WrapDivisible x) (WrapDivisible y) = WrapDivisible (divide g x y)
    gathered (WrapDivisible x) (WrapDivisible y) = WrapDivisible (divided x y)
instance Divisible f => Inplicative (WrappedDivisible f) where
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
instance (Applicative f, Invariant f) => Inply (WrappedApplicativeOnly f) where
    gather f _ (WrapApplicativeOnly x) (WrapApplicativeOnly y) = WrapApplicativeOnly (liftA2 f x y)
    gathered (WrapApplicativeOnly x) (WrapApplicativeOnly y) = WrapApplicativeOnly (liftA2 (,) x y)
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
instance (Divisible f, Invariant f) => Inply (WrappedDivisibleOnly f) where
    gather _ g (WrapDivisibleOnly x) (WrapDivisibleOnly y) = WrapDivisibleOnly (divide g x y)
    gathered (WrapDivisibleOnly x) (WrapDivisibleOnly y) = WrapDivisibleOnly (divided x y)
instance (Divisible f, Invariant f) => Inplicative (WrappedDivisibleOnly f) where
    knot _ = conquer

deriving via WrappedApplicativeOnly (MaybeT m) instance (Monad m, Invariant m) => Inply (MaybeT m)
deriving via WrappedApplicativeOnly (MaybeT m) instance (Monad m, Invariant m) => Inplicative (MaybeT m)
deriving via WrappedApplicativeOnly (ListT m) instance (Monad m, Invariant m) => Inply (ListT m)
deriving via WrappedApplicativeOnly (ListT m) instance (Monad m, Invariant m) => Inplicative (ListT m)
deriving via WrappedApplicativeOnly (Tagged a) instance Inply (Tagged a)
deriving via WrappedApplicativeOnly (Tagged a) instance Inplicative (Tagged a)

deriving via WrappedFunctor Identity instance Inply Identity
deriving via WrappedFunctor Identity instance Inplicative Identity
deriving via WrappedFunctor (Proxy :: Type -> Type) instance Inply Proxy
deriving via WrappedFunctor (Proxy :: Type -> Type) instance Inplicative Proxy
deriving via WrappedFunctor [] instance Inply []
deriving via WrappedFunctor [] instance Inplicative []
deriving via WrappedFunctor ((->) r) instance Inply ((->) r)
deriving via WrappedFunctor ((->) r) instance Inplicative ((->) r)
deriving via WrappedFunctor Maybe instance Inply Maybe
deriving via WrappedFunctor Maybe instance Inplicative Maybe
deriving via WrappedFunctor (Either e) instance Inply (Either e)
deriving via WrappedFunctor (Either e) instance Inplicative (Either e)
deriving via WrappedFunctor IO instance Inply IO
deriving via WrappedFunctor IO instance Inplicative IO
deriving via WrappedFunctor Generics.Par1 instance Inply Generics.Par1
deriving via WrappedFunctor Generics.Par1 instance Inplicative Generics.Par1
deriving via WrappedFunctor (Generics.U1 :: Type -> Type) instance Inply Generics.U1
deriving via WrappedFunctor (Generics.U1 :: Type -> Type) instance Inplicative Generics.U1
deriving via WrappedFunctor (Generics.K1 i c :: Type -> Type) instance Semigroup c => Inply (Generics.K1 i c)
deriving via WrappedFunctor (Generics.K1 i c :: Type -> Type) instance Monoid c => Inplicative (Generics.K1 i c)
deriving via WrappedFunctor (Generics.M1 i t f :: Type -> Type) instance (Apply f, Invariant f) => Inply (Generics.M1 i t f)
deriving via WrappedFunctor (Generics.M1 i t f :: Type -> Type) instance (Applicative f, Apply f, Invariant f) => Inplicative (Generics.M1 i t f)
deriving via WrappedFunctor ((f Generics.:*: g) :: Type -> Type) instance (Apply f, Apply g, Invariant f, Invariant g) => Inply (f Generics.:*: g)
deriving via WrappedFunctor ((f Generics.:*: g) :: Type -> Type) instance (Applicative f, Applicative g, Apply f, Apply g, Invariant f, Invariant g) => Inplicative (f Generics.:*: g)
deriving via WrappedFunctor (Product f g :: Type -> Type) instance (Apply f, Apply g, Invariant f, Invariant g) => Inply (Product f g)
deriving via WrappedFunctor (Product f g :: Type -> Type) instance (Applicative f, Applicative g, Apply f, Apply g, Invariant f, Invariant g) => Inplicative (Product f g)
deriving via WrappedFunctor (((f :: Type -> Type) Generics.:.: g) :: Type -> Type) instance (Apply f, Apply g, Invariant f, Invariant g) => Inply (f Generics.:.: g)
deriving via WrappedFunctor (((f :: Type -> Type) Generics.:.: g) :: Type -> Type) instance (Applicative f, Applicative g, Apply f, Apply g, Invariant f, Invariant g) => Inplicative (f Generics.:.: g)
deriving via WrappedFunctor (Compose (f :: Type -> Type) g :: Type -> Type) instance (Apply f, Apply g, Invariant f, Invariant g) => Inply (Compose f g)
deriving via WrappedFunctor (Compose (f :: Type -> Type) g :: Type -> Type) instance (Applicative f, Applicative g, Apply f, Apply g, Invariant f, Invariant g) => Inplicative (Compose f g)
deriving via WrappedFunctor Complex instance Inply Complex
deriving via WrappedFunctor Complex instance Inplicative Complex
deriving via WrappedFunctor Semigroup.Min instance Inply Semigroup.Min
deriving via WrappedFunctor Semigroup.Min instance Inplicative Semigroup.Min
deriving via WrappedFunctor Semigroup.Max instance Inply Semigroup.Max
deriving via WrappedFunctor Semigroup.Max instance Inplicative Semigroup.Max
deriving via WrappedFunctor Semigroup.First instance Inply Semigroup.First
deriving via WrappedFunctor Semigroup.First instance Inplicative Semigroup.First
deriving via WrappedFunctor Semigroup.Last instance Inply Semigroup.Last
deriving via WrappedFunctor Semigroup.Last instance Inplicative Semigroup.Last
deriving via WrappedFunctor Semigroup.Option instance Inply Semigroup.Option
deriving via WrappedFunctor Semigroup.Option instance Inplicative Semigroup.Option
deriving via WrappedFunctor ZipList instance Inply ZipList
deriving via WrappedFunctor ZipList instance Inplicative ZipList
deriving via WrappedFunctor Monoid.First instance Inply Monoid.First
deriving via WrappedFunctor Monoid.First instance Inplicative Monoid.First
deriving via WrappedFunctor Monoid.Last instance Inply Monoid.Last
deriving via WrappedFunctor Monoid.Last instance Inplicative Monoid.Last
deriving via WrappedFunctor Monoid.Dual instance Inply Monoid.Dual
deriving via WrappedFunctor Monoid.Dual instance Inplicative Monoid.Dual
deriving via WrappedFunctor Monoid.Sum instance Inply Monoid.Sum
deriving via WrappedFunctor Monoid.Sum instance Inplicative Monoid.Sum
deriving via WrappedFunctor Monoid.Product instance Inply Monoid.Product
deriving via WrappedFunctor Monoid.Product instance Inplicative Monoid.Product
deriving via WrappedFunctor NonEmpty instance Inply NonEmpty
deriving via WrappedFunctor NonEmpty instance Inplicative NonEmpty
deriving via WrappedFunctor Tree instance Inply Tree
deriving via WrappedFunctor Tree instance Inplicative Tree
deriving via WrappedFunctor Seq instance Inply Seq
deriving via WrappedFunctor Seq instance Inplicative Seq
deriving via WrappedFunctor (ExceptT e m) instance (Monad m, Invariant m) => Inply (ExceptT e m)
deriving via WrappedFunctor (ExceptT e m) instance (Monad m, Invariant m) => Inplicative (ExceptT e m)
deriving via WrappedFunctor (ErrorT e m) instance (Monad m, Invariant m) => Inply (ErrorT e m)
deriving via WrappedFunctor (ErrorT e m) instance (Monad m, Invariant m) => Inplicative (ErrorT e m)
deriving via WrappedFunctor (RWST r w s m) instance (Monad m, Bind m, Invariant m, Semigroup w) => Inply (RWST r w s m)
deriving via WrappedFunctor (RWST r w s m) instance (Monad m, Bind m, Invariant m, Monoid w) => Inplicative (RWST r w s m)
deriving via WrappedFunctor (WrappedArrow a b) instance Arrow a => Inply (WrappedArrow a b)
deriving via WrappedFunctor (WrappedArrow a b) instance Arrow a => Inplicative (WrappedArrow a b)
deriving via WrappedFunctor (Generics.V1 :: Type -> Type) instance Inply Generics.V1
deriving via WrappedFunctor IM.IntMap instance Inply IM.IntMap
deriving via WrappedFunctor (M.Map k) instance Ord k => Inply (M.Map k)
deriving via WrappedFunctor (HM.HashMap k) instance (Hashable k, Eq k) => Inply (HM.HashMap k)
deriving via WrappedFunctor (Const w :: Type -> Type) instance Semigroup w => Inply (Const w)
deriving via WrappedFunctor (Const w :: Type -> Type) instance Monoid w => Inplicative (Const w)
deriving via WrappedFunctor (Constant w :: Type -> Type) instance Semigroup w => Inply (Constant w)
deriving via WrappedFunctor (Constant w :: Type -> Type) instance Monoid w => Inplicative (Constant w)
deriving via WrappedFunctor ((,) w :: Type -> Type) instance Semigroup w => Inply ((,) w)
deriving via WrappedFunctor ((,) w :: Type -> Type) instance Monoid w => Inplicative ((,) w)
deriving via WrappedFunctor (WriterT w m) instance (Apply m, Invariant m, Semigroup w) => Inply (WriterT w m)
deriving via WrappedFunctor (WriterT w m) instance (Applicative m, Apply m, Invariant m, Monoid w) => Inplicative (WriterT w m)
deriving via WrappedFunctor (ReaderT r m) instance (Apply m, Invariant m) => Inply (ReaderT r m)
deriving via WrappedFunctor (ReaderT r m) instance (Applicative m, Apply m, Invariant m) => Inplicative (ReaderT r m)
deriving via WrappedFunctor (ContT r (m :: Type -> Type)) instance Inply (ContT r m)
deriving via WrappedFunctor (ContT r (m :: Type -> Type)) instance Inplicative (ContT r m)
deriving via WrappedFunctor (WrappedMonad m) instance Monad m => Inply (WrappedMonad m)
deriving via WrappedFunctor (WrappedMonad m) instance Monad m => Inplicative (WrappedMonad m)
deriving via WrappedFunctor (Generics.Rec1 f :: Type -> Type) instance (Apply f, Invariant f) => Inply (Generics.Rec1 f)
deriving via WrappedFunctor (Generics.Rec1 f :: Type -> Type) instance (Applicative f, Apply f, Invariant f) => Inplicative (Generics.Rec1 f)
deriving via WrappedFunctor (Monoid.Alt f :: Type -> Type) instance (Apply f, Invariant f) => Inply (Monoid.Alt f)
deriving via WrappedFunctor (Monoid.Alt f :: Type -> Type) instance (Applicative f, Apply f, Invariant f) => Inplicative (Monoid.Alt f)
deriving via WrappedFunctor (BFJ.Join p :: Type -> Type) instance (Biapply p, Invariant2 p) => Inply (BFJ.Join p)
deriving via WrappedFunctor (BFJ.Join p :: Type -> Type) instance (Biapplicative p, Biapply p, Invariant2 p) => Inplicative (BFJ.Join p)
deriving via WrappedFunctor (IdentityT f :: Type -> Type) instance (Apply f, Invariant f) => Inply (IdentityT f)
deriving via WrappedFunctor (IdentityT f :: Type -> Type) instance (Applicative f, Apply f, Invariant f) => Inplicative (IdentityT f)
deriving via WrappedFunctor (Reverse f :: Type -> Type) instance (Apply f, Invariant f) => Inply (Reverse f)
deriving via WrappedFunctor (Reverse f :: Type -> Type) instance (Applicative f, Apply f, Invariant f) => Inplicative (Reverse f)
deriving via WrappedFunctor (Backwards f :: Type -> Type) instance (Apply f, Invariant f) => Inply (Backwards f)
deriving via WrappedFunctor (Backwards f :: Type -> Type) instance (Applicative f, Apply f, Invariant f) => Inplicative (Backwards f)

deriving via WrappedFunctor (Lift f) instance (Invariant f, Apply f) => Inply (Lift f)
instance (Invariant f, Apply f) => Inplicative (Lift f) where knot x = Pure x


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
--   concatInplicative $ intPrim
--                    :* boolPrim
--                    :* stringPrim
--                    :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'knot' directly.
-- *    If you have 1 component, use 'inject' directly.
-- *    If you have 2 components, use 'gather' directly.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off tuples one-by-one.
--
-- @since 0.4.0.0
concatInplicative
    :: Inplicative f
    => NP f as
    -> f (NP I as)
concatInplicative = \case
    Nil     -> knot Nil
    x :* xs -> gather
      (\y ys -> I y :* ys)
      (\case I y :* ys -> (y, ys))
      x
      (concatInplicative xs)

concatMapInplicative
    :: Inplicative f
    => (NP I as -> b)
    -> (b -> NP I as)
    -> NP f as
    -> f b
concatMapInplicative f g = invmap f g . concatInplicative

-- | A version of 'concatInplicative' for non-empty 'NP', but only
-- requiring an 'Inply' instance.
--
-- @since 0.4.0.0
concatInply
    :: Inply f
    => NP f (a ': as)
    -> f (NP I (a ': as))
concatInply (x :* xs) = case xs of
    Nil    -> invmap ((:* Nil) . I) (\case I y :* _ -> y) x
    _ :* _ -> gather
      (\y ys -> I y :* ys)
      (\case I y :* ys -> (y, ys))
      x
      (concatInply xs)

concatMapInply
    :: Inplicative f
    => (NP I (a ': as) -> b)
    -> (b -> NP I (a ': as))
    -> NP f (a ': as)
    -> f b
concatMapInply f g = invmap f g . concatInply

-- | A version of 'concatInplicative' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @since 0.4.0.0
concatInplicativeRec
    :: Inplicative f
    => V.Rec f as
    -> f (V.XRec V.Identity as)
concatInplicativeRec = \case
    V.RNil    -> knot V.RNil
    x V.:& xs -> gather
      (V.::&)
      (\case y V.::& ys -> (y, ys))
      x
      (concatInplicativeRec xs)

concatMapInplicativeRec
    :: Inplicative f
    => (V.XRec V.Identity as -> b)
    -> (b -> V.XRec V.Identity as)
    -> V.Rec f as
    -> f b
concatMapInplicativeRec f g = invmap f g . concatInplicativeRec

-- | Convenient wrapper to 'swerve' over multiple arguments using tine
-- vinyl library's multi-arity uncurrying facilities.  Makes it a lot more
-- convenient than using 'swerve' multiple times and needing to accumulate
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
-- 'swerveN'
--   MT                                         -- ^ curried assembling function
--   (\(MT x y z) -> x ::& y ::& z ::& XRNil)   -- ^ disassembling function
--   (intPrim :: Prim Int)
--   (boolPrim :: Prim Bool)
--   (stringPrim :: Prim String)
-- @
--
-- Really only useful with 3 or more arguments, since with two arguments
-- this is just 'swerve' (and with zero arguments, you can just use
-- 'knot').
--
-- The generic type is a bit tricky to understand, but it's easier to
-- understand what's going on if you instantiate with concrete types:
--
-- @
-- ghci> :t swerveN @MyInplicative @'[Int, Bool, String]
--      (Int -> Bool -> String -> b)
--   -> (b -> XRec Identity '[Int, Bool, String])
--   -> MyInplicative Int
--   -> MyInplicative Bool
--   -> MyInplicative String
--   -> MyInplicative b
-- @
--
-- @since 0.4.1.0
swerveN
    :: forall f as b. (Inplicative f, V.IsoXRec V.Identity as, V.RecordCurry as)
    => V.Curried as b
    -> (b -> V.XRec V.Identity as)
    -> V.CurriedF f as (f b)
swerveN f g = V.rcurry @as @f $
    invmap (V.runcurry' f . V.fromXRec) g
  . concatInplicativeRec

-- | A version of 'concatInply' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @since 0.4.0.0
concatInplyRec
    :: Inply f
    => V.Rec f (a ': as)
    -> f (V.XRec V.Identity (a ': as))
concatInplyRec (x V.:& xs) = case xs of
    V.RNil   -> invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
    _ V.:& _ -> gather
      (V.::&)
      (\case y V.::& ys -> (y, ys))
      x
      (concatInplyRec xs)

-- | 'swerveN' but with at least one argument, so can be used with any
-- 'Inply'.
--
-- @since 0.4.1.0
swerveN1
    :: forall f a as b. (Inply f, V.IsoXRec V.Identity as, V.RecordCurry as)
    => V.Curried (a ': as) b
    -> (b -> V.XRec V.Identity (a ': as))
    -> V.CurriedF f (a ': as) (f b)
swerveN1 f g = V.rcurry @(a ': as) @f $
    invmap (V.runcurry' f . V.fromXRec) g
  . concatInplyRec

