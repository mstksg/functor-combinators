{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE DerivingVia         #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}

module Data.HFunctor.Internal (
    HFunctor(..)
  , HBifunctor(..)
  , WrappedHBifunctor(..)
  , sumSum, prodProd
  , generalize, absorb
  , unsafePlus, unsafeApply, unsafeBind, unsafePointed
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Comonad.Trans.Env
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Reader
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Bifunctor.Joker
import           Data.Coerce
import           Data.Constraint
import           Data.Constraint.Unsafe
import           Data.Functor.Bind
import           Data.Functor.Coyoneda
import           Data.Functor.Day               (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Reverse
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.Functor.Yoneda
import           Data.Kind
import           Data.Proxy
import           Data.Tagged
import           Data.Pointed
import           GHC.Generics hiding            (C)
import qualified Control.Alternative.Free       as Alt
import qualified Control.Applicative.Free.Fast  as FAF
import qualified Control.Applicative.Free.Final as FA
import qualified Control.Monad.Free.Church      as MC
import qualified Data.Functor.Day               as D

-- | An 'HFunctor' can be thought of a unary "functor transformer" ---
-- a basic functor combinator.  It takes a functor as input and returns
-- a functor as output.
--
-- It "enhances" a functor with extra structure (sort of like how a monad
-- transformer enhances a 'Monad' with extra structure).
--
-- As a uniform inteface, we can "swap the underlying functor" (also
-- sometimes called "hoisting").  This is what 'hmap' does: it lets us swap
-- out the @f@ in a @t f@ for a @t g@.
--
-- For example, the free monad 'Free' takes a 'Functor' and returns a new
-- 'Functor'.  In the process, it provides a monadic structure over @f@.
-- 'hmap' lets us turn a @'Free' f@ into a @'Free' g@: a monad built over
-- @f@ can be turned into a monad built over @g@.
--
-- For the ability to move in and out of the enhanced functor, see
-- 'Data.HFunctor.Inject' and 'Data.HFunctor.Interpret.Interpret'.
class HFunctor t where
    -- | If we can turn an @f@ into a @g@, then we can turn a @t f@ into
    -- a @t g@.
    --
    -- It must be the case that
    --
    -- @
    -- 'hmap' 'id' == id
    -- @
    --
    -- Essentially, @t f@ adds some "extra structure" to @f@.  'hmap'
    -- must swap out the functor, /without affecting the added structure/.
    --
    -- For example, @'ListF' f a@ is essentially a list of @f a@s.  If we
    -- 'hmap' to swap out the @f a@s for @g a@s, then we must ensure that
    -- the "added structure" (here, the number of items in the list, and
    -- the ordering of those items) remains the same.  So, 'hmap' must
    -- preserve the number of items in the list, and must maintain the
    -- ordering.
    --
    -- The law @'hmap' 'id' == id@ is a way of formalizing this property.
    hmap :: f ~> g -> t f ~> t g

    {-# MINIMAL hmap #-}

-- | A 'HBifunctor' is like an 'HFunctor', but it enhances /two/ different
-- functors instead of just one.
--
-- Usually, it enhaces them "together" in some sort of combining way.
--
-- This typeclass provides a uniform instance for "swapping out" or
-- "hoisting" the enhanced functors.   We can hoist the first one with
-- 'hleft', the second one with 'hright', or both at the same time with
-- 'hbimap'.
--
-- For example, the @f :*: g@ type gives us "both @f@ and @g@":
--
-- @
-- data (f ':*:' g) a = f a :*: g a
-- @
--
-- It combines both @f@ and @g@ into a unified structure --- here, it does
-- it by providing both @f@ and @g@.
--
-- The single law is:
--
-- @
-- 'hbimap' 'id' id == id
-- @
--
-- This ensures that 'hleft', 'hright', and 'hbimap' do not affect the
-- structure that @t@ adds on top of the underlying functors.
class HBifunctor t where
    -- | Swap out the first transformed functor.
    hleft  :: f ~> j -> t f g ~> t j g
    hleft = (`hbimap` id)

    -- | Swap out the second transformed functor.
    hright :: g ~> k -> t f g ~> t f k
    hright = hbimap id

    -- | Swap out both transformed functors at the same time.
    hbimap :: f ~> j -> g ~> k -> t f g ~> t j k
    hbimap f g = hleft f . hright g

    {-# MINIMAL hleft, hright | hbimap #-}

-- | Useful newtype to allow us to derive an 'HFunctor' instance from any
-- instance of 'HBifunctor', using -XDerivingVia.
--
-- For example, because we have @instance 'HBifunctor' 'Day'@, we can
-- write:
--
-- @
-- deriving via ('WrappedHBifunctor' 'Day' f) instance 'HFunctor' ('Day' f)
-- @
--
-- to give us an automatic 'HFunctor' instance and save us some work.
newtype WrappedHBifunctor t (f :: Type -> Type) (g :: Type -> Type) a
    = WrapHBifunctor { unwrapHBifunctor :: t f g a }
  deriving Functor

-- | Isomorphism between different varieities of ':+:'.
sumSum :: (f :+: g) <~> Sum f g
sumSum = isoF to_ from_
  where
    to_   (L1 x)  = InL x
    to_   (R1 y)  = InR y
    from_ (InL x) = L1 x
    from_ (InR y) = R1 y

-- | Isomorphism between different varieities of ':*:'.
prodProd :: (f :*: g) <~> Product f g
prodProd = isoF to_ from_
  where
    to_   (x :*: y)  = Pair x y
    from_ (Pair x y) = x :*: y

-- | For any @'Alternative' f@, produce a value that would require @'Plus'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Plus' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafePlus :: forall f proxy r. Alternative f => proxy f -> (Plus f => r) -> r
unsafePlus _ x = case unsafeCoerceConstraint @(Plus (WrappedApplicative f)) @(Plus f) of
    Sub Dict -> x

-- | For any @'Applicative' f@, produce a value that would require @'Apply'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Apply' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafeApply :: forall f proxy r. Applicative f => proxy f -> (Apply f => r) -> r
unsafeApply _ x = case unsafeCoerceConstraint @(Apply (WrappedApplicative f)) @(Apply f) of
    Sub Dict -> x

-- | For any @'Monad' f@, produce a value that would require @'Bind'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Bind' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafeBind :: forall f proxy r. Monad f => proxy f -> (Bind f => r) -> r
unsafeBind _ x = case unsafeCoerceConstraint @(Bind (WrappedMonad f)) @(Bind f) of
    Sub Dict -> x

newtype PointMe f a = PointMe (f a)

instance Applicative f => Pointed (PointMe f) where
    point = PointMe . pure

-- | For any @'Applicative' f@, produce a value that would require
-- @'Pointed' f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Pointed' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafePointed :: forall f proxy r. Applicative f => proxy f -> (Pointed f => r) -> r
unsafePointed _ x = case unsafeCoerceConstraint @(Pointed (PointMe f)) @(Pointed f) of
    Sub Dict -> x

-- | Turn 'Identity' into any @'Applicative' f@.  Can be useful as an
-- argument to 'hmap', 'hbimap', or 'Data.HFunctor.Interpret.interpret'.
--
-- It is a more general form of 'Control.Monad.Morph.generalize' from
-- /mmorph/.
generalize :: Applicative f => Identity ~> f
generalize (Identity x) = pure x

-- | Natural transformation from any functor @f@ into 'Proxy'.  Can be
-- useful for "zeroing out" a functor with 'hmap' or 'hbimap' or
-- 'Data.HFunctor.Interpret.interpret'.
absorb :: f ~> Proxy
absorb _ = Proxy

instance HFunctor Coyoneda where
    hmap = hoistCoyoneda

instance HFunctor Ap where
    hmap = hoistAp

instance HFunctor ListF where
    hmap f (ListF xs) = ListF (map f xs)

instance HFunctor NonEmptyF where
    hmap f (NonEmptyF xs) = NonEmptyF (fmap f xs)

instance HFunctor MaybeF where
    hmap f (MaybeF xs) = MaybeF (fmap f xs)

instance HFunctor Alt.Alt where
    hmap = Alt.hoistAlt

instance HFunctor Step where
    hmap f (Step n x) = Step n (f x)

instance HFunctor Steps where
    hmap f (Steps xs) = Steps (f <$> xs)

instance HFunctor Free where
    hmap = hoistFree

instance HFunctor Free1 where
    hmap = hoistFree1

instance HFunctor MC.F where
    hmap = MC.hoistF

instance HFunctor MaybeT where
    hmap f = mapMaybeT f

instance HFunctor Yoneda where
    hmap f x = Yoneda $ f . runYoneda x

instance HFunctor FA.Ap where
    hmap = FA.hoistAp

instance HFunctor FAF.Ap where
    hmap = FAF.hoistAp

instance HFunctor IdentityT where
    hmap = mapIdentityT

instance HFunctor Lift where
    hmap = mapLift

instance HFunctor MaybeApply where
    hmap f (MaybeApply x) = MaybeApply (first f x)

instance HFunctor Backwards where
    hmap f (Backwards x) = Backwards (f x)

instance HFunctor WrappedApplicative where
    hmap f (WrapApplicative x) = WrapApplicative (f x)

instance HFunctor (ReaderT r) where
    hmap = mapReaderT

instance HFunctor Tagged where
    hmap _ = coerce

instance HFunctor Reverse where
    hmap f (Reverse x) = Reverse (f x)

instance (HFunctor s, HFunctor t) => HFunctor (ComposeT s t) where
    hmap f (ComposeT x) = ComposeT $ hmap (hmap f) x

instance Functor f => HFunctor ((:.:) f) where
    hmap f (Comp1 x) = Comp1 (f <$> x)

instance HFunctor (M1 i c) where
    hmap f (M1 x) = M1 (f x)

instance HFunctor Void2 where
    hmap _ = coerce

instance HFunctor (EnvT e) where
    hmap f (EnvT e x) = EnvT e (f x)

instance HBifunctor (:*:) where
    hleft  f (x :*: y) = f x :*:   y
    hright g (x :*: y) =   x :*: g y
    hbimap f g (x :*: y) = f x :*: g y

instance HBifunctor Product where
    hleft  f (Pair x y)   = Pair (f x)    y
    hright g (Pair x y)   = Pair    x  (g y)
    hbimap f g (Pair x y) = Pair (f x) (g y)

instance HBifunctor Day where
    hleft  = D.trans1
    hright = D.trans2
    hbimap f g (Day x y z) = Day (f x) (g y) z

instance HBifunctor (:+:) where
    hleft f = \case
      L1 x -> L1 (f x)
      R1 y -> R1 y

    hright g = \case
      L1 x -> L1 x
      R1 y -> R1 (g y)

    hbimap f g = \case
      L1 x -> L1 (f x)
      R1 y -> R1 (g y)

instance HBifunctor Sum where
    hleft f = \case
      InL x -> InL (f x)
      InR y -> InR y

    hright g = \case
      InL x -> InL x
      InR y -> InR (g y)

    hbimap f g = \case
      InL x -> InL (f x)
      InR y -> InR (g y)

instance HBifunctor These1 where
    hbimap f g = \case
      This1  x   -> This1  (f x)
      That1    y -> That1        (g y)
      These1 x y -> These1 (f x) (g y)

instance HBifunctor Joker where
    hleft  f   (Joker x) = Joker (f x)
    hright   _           = coerce
    hbimap f _ (Joker x) = Joker (f x)

instance HBifunctor Void3 where
    hleft  _   = coerce
    hright   _ = coerce
    hbimap _ _ = coerce

instance HBifunctor Comp where
    hleft  f   (x :>>= h) = f x :>>= h
    hright   g (x :>>= h) =   x :>>= (g . h)
    hbimap f g (x :>>= h) = f x :>>= (g . h)

instance HBifunctor t => HFunctor (WrappedHBifunctor t f) where
    hmap f = WrapHBifunctor . hright f . unwrapHBifunctor

deriving via (WrappedHBifunctor Day f)     instance HFunctor (Day f)
deriving via (WrappedHBifunctor (:*:) f)   instance HFunctor ((:*:) f)
deriving via (WrappedHBifunctor Product f) instance HFunctor (Product f)
deriving via (WrappedHBifunctor Sum f)     instance HFunctor (Sum f)
deriving via (WrappedHBifunctor Joker f)   instance HFunctor (Joker f)
deriving via (WrappedHBifunctor These1 f)  instance HFunctor (These1 f)
deriving via (WrappedHBifunctor Void3 f)   instance HFunctor (Void3 f)
deriving via (WrappedHBifunctor Comp f)    instance HFunctor (Comp f)
