{-# LANGUAGE DerivingVia #-}

module Data.HFunctor.Internal (
    HFunctor(..)
  , HBifunctor(..)
  , WrappedHBifunctor(..)
  , sumSum, prodProd
  , generalize, absorb
  , NDL, ndlSingleton, fromNDL
  ) where

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
import           Data.Foldable
import           Data.Functor.Bind
import           Data.Functor.Contravariant.Night    (Night(..))
import           Data.Functor.Coyoneda
import           Data.Functor.Day                    (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Functor.Reverse
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.Functor.Yoneda
import           Data.Kind
import           Data.List.NonEmpty                  (NonEmpty(..))
import           Data.Proxy
import           Data.Tagged
import           Data.Vinyl.CoRec
import           Data.Vinyl.Core                     (Rec)
import           Data.Vinyl.Recursive
import           GHC.Generics
import qualified Control.Alternative.Free            as Alt
import qualified Control.Applicative.Free.Fast       as FAF
import qualified Control.Applicative.Free.Final      as FA
import qualified Control.Monad.Free.Church           as MC
import qualified Data.Functor.Contravariant.Coyoneda as CCY
import qualified Data.Functor.Contravariant.Day      as CD
import qualified Data.Functor.Contravariant.Night    as N
import qualified Data.Functor.Day                    as D
import qualified Data.Functor.Invariant.Day          as ID
import qualified Data.Functor.Invariant.Night        as IN
import qualified Data.SOP                            as SOP
import qualified Data.SOP.NP                         as SOP
import qualified Data.SOP.NS                         as SOP

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
--
-- This class is similar to 'Control.Monad.Morph.MFunctor' from
-- "Control.Monad.Morph", but instances must work without a 'Monad' constraint.
--
-- This class is also found in the /hschema/ library with the same name.
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
class HBifunctor (t :: (k -> Type) -> (k -> Type) -> k -> Type) where
    -- | Swap out the first transformed functor.
    hleft  :: f ~> j -> t f g ~> t j g
    hleft f x = hbimap f id x

    -- | Swap out the second transformed functor.
    hright :: g ~> l -> t f g ~> t f l
    hright f x = hbimap id f x

    -- | Swap out both transformed functors at the same time.
    hbimap :: f ~> j -> g ~> l -> t f g ~> t j l
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
newtype WrappedHBifunctor t (f :: k -> Type) (g :: k -> Type) (a :: k)
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

-- | Internal type, used to not require dlist-1.0
newtype NDL a = NDL ([a] -> NonEmpty a)

ndlSingleton :: a -> NDL a
ndlSingleton x = NDL (x:|)

fromNDL :: NDL a -> NonEmpty a
fromNDL (NDL f) = f []

instance Semigroup (NDL a) where
    NDL x <> NDL y = NDL (x . toList . y)

instance HFunctor Coyoneda where
    hmap f x = hoistCoyoneda f x

-- | @since 0.3.0.0
instance HFunctor CCY.Coyoneda where
    hmap f (CCY.Coyoneda g x) = CCY.Coyoneda g (f x)

instance HFunctor Ap where
    hmap f x = hoistAp f x

instance HFunctor ListF where
    hmap f (ListF xs) = ListF (map f xs)

instance HFunctor NonEmptyF where
    hmap f (NonEmptyF xs) = NonEmptyF (fmap f xs)

instance HFunctor MaybeF where
    hmap f (MaybeF xs) = MaybeF (fmap f xs)

instance HFunctor (MapF k) where
    hmap f (MapF xs) = MapF (fmap f xs)

instance HFunctor (NEMapF k) where
    hmap f (NEMapF xs) = NEMapF (fmap f xs)

instance HFunctor Alt.Alt where
    hmap f x = Alt.hoistAlt f x

-- | @since 0.3.6.0
instance HFunctor Alt.AltF where
    hmap f = \case
      Alt.Ap x xs -> Alt.Ap (f x) (hmap f xs)
      Alt.Pure x  -> Alt.Pure x

instance HFunctor Step where
    hmap f (Step n x) = Step n (f x)

instance HFunctor Steps where
    hmap f (Steps xs) = Steps (f <$> xs)

instance HFunctor Flagged where
    hmap f (Flagged b x) = Flagged b (f x)

instance HFunctor Free where
    hmap f x = hoistFree f x

instance HFunctor Free1 where
    hmap f x = hoistFree1 f x

-- | Note that there is no 'Data.HFunctor.Interpret.Interpret' or
-- 'Data.HFunctor.Bind' instance, because 'Data.HFunctor.inject' requires
-- @'Functor' f@.
instance HFunctor MC.F where
    hmap f x = MC.hoistF f x

-- | Note that there is no 'Data.HFunctor.Interpret.Interpret' or
-- 'Data.HFunctor.Bind' instance, because 'Data.HFunctor.inject' requires
-- @'Functor' f@.
instance HFunctor MaybeT where
    hmap f x = mapMaybeT f x

instance HFunctor Yoneda where
    hmap f x = Yoneda $ f . runYoneda x

instance HFunctor FA.Ap where
    hmap f x = FA.hoistAp f x

instance HFunctor FAF.Ap where
    hmap f x = FAF.hoistAp f x

instance HFunctor IdentityT where
    hmap f x = mapIdentityT f x

instance HFunctor Lift where
    hmap f x = mapLift f x

instance HFunctor MaybeApply where
    hmap f (MaybeApply x) = MaybeApply (first f x)

instance HFunctor Backwards where
    hmap f (Backwards x) = Backwards (f x)

instance HFunctor WrappedApplicative where
    hmap f (WrapApplicative x) = WrapApplicative (f x)

instance HFunctor (ReaderT r) where
    hmap f x = mapReaderT f x

instance HFunctor Tagged where
    hmap _ x = coerce x

instance HFunctor Reverse where
    hmap f (Reverse x) = Reverse (f x)

instance (HFunctor s, HFunctor t) => HFunctor (ComposeT s t) where
    hmap f (ComposeT x) = ComposeT $ hmap (hmap f) x

instance Functor f => HFunctor ((:.:) f) where
    hmap f (Comp1 x) = Comp1 (f <$> x)

instance HFunctor (M1 i c) where
    hmap f (M1 x) = M1 (f x)

instance HFunctor Void2 where
    hmap _ x = coerce x

instance HFunctor (EnvT e) where
    hmap f (EnvT e x) = EnvT e (f x)

instance HFunctor Rec where
    hmap f x = rmap f x

instance HFunctor CoRec where
    hmap f (CoRec x) = CoRec (f x)

-- | @since 0.3.0.0
instance HFunctor SOP.NP where
    hmap f = SOP.cata_NP SOP.Nil ((SOP.:*) . f)

-- | @since 0.3.0.0
instance HFunctor SOP.NS where
    hmap f = SOP.cata_NS (SOP.Z . f) SOP.S

instance HFunctor (Joker f) where
    hmap _ x = coerce x

instance HFunctor (Void3 f) where
    hmap _ = \case {}

instance HFunctor (Comp f) where
    hmap f (x :>>= h) = x :>>= (f . h)

instance HBifunctor (:*:) where
    hleft  f (x :*: y) = f x :*:   y
    hright g (x :*: y) =   x :*: g y
    hbimap f g (x :*: y) = f x :*: g y

instance HBifunctor Product where
    hleft  f (Pair x y)   = Pair (f x)    y
    hright g (Pair x y)   = Pair    x  (g y)
    hbimap f g (Pair x y) = Pair (f x) (g y)

instance HBifunctor Day where
    hleft f x = D.trans1 f x
    hright f x = D.trans2 f x
    hbimap f g (Day x y z) = Day (f x) (g y) z

-- | @since 0.3.0.0
instance HBifunctor CD.Day where
    hleft f x = CD.trans1 f x
    hright f x = CD.trans2 f x
    hbimap f g (CD.Day x y z) = CD.Day (f x) (g y) z

-- | @since 0.3.4.0
instance HBifunctor ID.Day where
    hbimap f g (ID.Day x y h j) = ID.Day (f x) (g y) h j

instance HBifunctor IN.Night where
    hbimap f g (IN.Night x y h j k) = IN.Night (f x) (g y) h j k

-- | @since 0.3.0.0
instance HBifunctor Night where
    hleft f x = N.trans1 f x
    hright f x = N.trans2 f x
    hbimap f g (Night x y z) = Night (f x) (g y) z

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

deriving via (WrappedHBifunctor Day f)      instance HFunctor (Day f)
deriving via (WrappedHBifunctor ID.Day f)   instance HFunctor (ID.Day f)
deriving via (WrappedHBifunctor IN.Night f) instance HFunctor (IN.Night f)
deriving via (WrappedHBifunctor (:*:) f)    instance HFunctor ((:*:) f)
deriving via (WrappedHBifunctor (:+:) f)    instance HFunctor ((:+:) f)
deriving via (WrappedHBifunctor Product f)  instance HFunctor (Product f)
deriving via (WrappedHBifunctor Sum f)      instance HFunctor (Sum f)
deriving via (WrappedHBifunctor These1 f)   instance HFunctor (These1 f)
