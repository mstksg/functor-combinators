{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Functor.HFunctor.Internal (
    HFunctor(..)
  , HBifunctor(..)
  , WrappedHBifunctor(..)
  ) where

import           Control.Applicative.Backwards
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Maybe
import           Control.Monad.Trans.Reader
import           Control.Natural
import           Data.Coerce
import           Data.Functor.Coyoneda
import           Data.Functor.Day               (Day(..))
import           Data.Functor.Reverse
import           Data.Functor.Yoneda
import           Data.Kind
import           Data.Tagged
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
-- 'Interpret'.
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
    -- Essentially, @'t' f@ adds some "extra structure" to @f@.  'hmap'
    -- must swap out the functor, /without affecting the added structure/.
    --
    -- For example, @'ListF' f a@ is essentially a list of @f a@s.  If we
    -- 'hmap' to swap out the @f a@s for @g a@s, then we must ensure that
    -- the "added structure" (here, the number of items in the list)
    -- remains the same.  So, 'hmap' must preserve the number of items in
    -- the list.
    --
    -- The law @'hmap' 'id' == id@ is a way of formalizing this informal
    -- property.
    --
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

instance HFunctor Coyoneda where
    hmap = hoistCoyoneda

instance HFunctor Ap where
    hmap = hoistAp

instance HFunctor ListF where
    hmap f (ListF xs) = ListF (map f xs)

instance HFunctor Alt.Alt where
    hmap = Alt.hoistAlt

instance HFunctor Step where
    hmap f (Step n x) = Step n (f x)

instance HFunctor Steps where
    hmap f (Steps xs) = Steps (f <$> xs)

instance HFunctor Free where
    hmap f x = Free $ \p b -> runFree x p $ \y z -> b (f y) z

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

instance HFunctor Backwards where
    hmap f (Backwards x) = Backwards (f x)

instance HFunctor (ReaderT r) where
    hmap = mapReaderT

instance HFunctor Tagged where
    hmap _ = coerce

instance HFunctor Reverse where
    hmap f (Reverse x) = Reverse (f x)

instance (HFunctor s, HFunctor t) => HFunctor (ComposeT s t) where
    hmap f (ComposeT x) = ComposeT $ hmap (hmap f) x

instance HBifunctor (:*:) where
    hleft  f (x :*: y) = f x :*:   y
    hright g (x :*: y) =   x :*: g y
    hbimap f g (x :*: y) = f x :*: g y

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
    = WrappedHBifunctor { unwrapHBifunctor :: t f g a }
  deriving Functor

instance HBifunctor t => HFunctor (WrappedHBifunctor t f) where
    hmap f = WrappedHBifunctor . hright f . unwrapHBifunctor

deriving via (WrappedHBifunctor Day f)    instance HFunctor (Day f)
deriving via (WrappedHBifunctor (:*:) f)  instance HFunctor ((:*:) f)
deriving via (WrappedHBifunctor (:+:) f)  instance HFunctor ((:+:) f)
