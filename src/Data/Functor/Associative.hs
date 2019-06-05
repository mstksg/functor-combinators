{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE EmptyDataDeriving          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}


module Data.Functor.Associative (
  -- * 'Associative'
    Associative(..)
  , assoc
  , disassoc
  , LiftT(..)
  -- * 'Semigroupoidal'
  , Semigroupoidal(..)
  , matchingSF
  -- ** Utility
  , extractT
  , getT
  , collectT
  , (!*!)
  , (!$!)
  -- * 'Chain1'
  , Chain1(..)
  , foldChain1
  , unfoldChain1
  , unrollingSF
  , unrollSF
  , rerollSF
  ) where

import           Control.Applicative
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Data.Copointed
import           Data.Deriving
import           Data.Foldable
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Day             (Day(..))
import           Data.Functor.HBifunctor
import           Data.Functor.HFunctor
import           Data.Functor.HFunctor.IsoF
import           Data.Functor.Identity
import           Data.Functor.Interpret
import           Data.Functor.Plus
import           Data.Kind
import           Data.List.NonEmpty           (NonEmpty(..))
import           Data.Proxy
import           GHC.Generics hiding          (C)
import qualified Data.Functor.Day             as D

-- | An 'HBifunctor' where it doesn't matter which binds first is
-- 'Associative'.  Knowing this gives us a lot of power to rearrange the
-- internals of our 'HFunctor' at will.
--
-- For example, for the functor product:
--
-- @
-- data (f ':*:' g) a = f a :*: g a
-- @
--
-- We know that @f :*: (g :*: h)@ is the same as @(f :*: g) :*: h@.
class HBifunctor t => Associative t where
    -- | The isomorphism between @t f (t g h) a@ and @t (t f g) h a@.  To
    -- use this isomorphism, see 'assoc' and 'disassoc'.
    associating
        :: (Functor f, Functor g, Functor h)
        => t f (t g h) <~> t (t f g) h
    {-# MINIMAL associating #-}

-- | Reassociate an application of @t@.
assoc
    :: (Associative t, Functor f, Functor g, Functor h)
    => t f (t g h)
    ~> t (t f g) h
assoc = viewF associating

-- | Reassociate an application of @t@.
disassoc
    :: (Associative t, Functor f, Functor g, Functor h)
    => t (t f g) h
    ~> t f (t g h)
disassoc = reviewF associating

class (Associative t, Interpret (SF t)) => Semigroupoidal t where
    type SF t :: (Type -> Type) -> Type -> Type

    -- | If a @'SF' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'SF' t f@s applied to
    -- themselves into one giant @'SF' t f@ containing all of the @t f@s.
    appendSF :: t (SF t f) (SF t f) ~> SF t f
    matchSF  :: Functor f => SF t f ~> f :+: t f (SF t f)

    -- | Prepend an application of @t f@ to the front of a @'SF' t f@.
    consSF :: t f (SF t f) ~> SF t f
    consSF = appendSF . hleft inject

    -- | Embed a direct application of @f@ to itself into a @'SF' t f@.
    toSF :: t f f ~> SF t f
    toSF = consSF . hright inject

    -- | A version of 'retract' that works for a 'Tensor'.  It retracts
    -- /both/ @f@s into a single @f@.
    biretract :: C (SF t) f => t f f ~> f
    biretract = retract . toSF

    -- | A version of 'interpret' that works for a 'Tensor'.  It takes two
    -- interpreting functions, and interprets both joined functors one
    -- after the other into @h@.
    binterpret
        :: C (SF t) h
        => f ~> h
        -> g ~> h
        -> t f g ~> h
    binterpret f g = retract . toSF . hbimap f g

    {-# MINIMAL appendSF, matchSF #-}

data Chain1 t f a = Done1 (f a)
                  | More1 (t f (Chain1 t f) a)

deriving instance (Functor f, Functor (t f (Chain1 t f))) => Functor (Chain1 t f)

instance (Show1 (t f (Chain1 t f)), Show1 f) => Show1 (Chain1 t f) where
    liftShowsPrec sp sl d = \case
        Done1 x  -> showsUnaryWith (liftShowsPrec sp sl) "Done1" d x
        More1 xs -> showsUnaryWith (liftShowsPrec sp sl) "More1" d xs

instance (Show1 (t f (Chain1 t f)), Show1 f, Show a) => Show (Chain1 t f a) where
    showsPrec = liftShowsPrec showsPrec showList


foldChain1 :: forall t f g. HBifunctor t => f ~> g -> t f g ~> g -> Chain1 t f ~> g
foldChain1 f g = go
  where
    go :: Chain1 t f ~> g
    go = \case
      Done1 x  -> f x
      More1 xs -> g (hright go xs)

unfoldChain1 :: forall t f g. HBifunctor t => (g ~> f :+: t f g) -> g ~> Chain1 t f
unfoldChain1 f = go
  where
    go :: g ~> Chain1 t f
    go = (Done1 !*! More1 . hright go) . f

instance HBifunctor t => HFunctor (Chain1 t) where
    hmap f = foldChain1 (Done1 . f) (More1 . hleft f)

instance (HBifunctor t, Semigroupoidal t) => Interpret (Chain1 t) where
    type C (Chain1 t) = C (SF t)
    inject  = Done1
    retract = \case
      Done1 x  -> x
      More1 xs -> binterpret id retract xs
    interpret :: forall f g. C (SF t) g => f ~> g -> Chain1 t f ~> g
    interpret f = go
      where
        go :: Chain1 t f ~> g
        go = \case
          Done1 x  -> f x
          More1 xs -> binterpret f go xs

-- | An @'SF' t f@ represents the successive application of @t@ to @f@,
-- over and over again.   So, that means that an @'SF' t f@ must either be
-- a single @f@, or an @t f (SF t f)@.
--
-- 'matchingSF' states that these two are isomorphic.  Use 'matchSF' and
-- @'inject' '!*!' 'consSF'@ to convert between one and the other.
matchingSF :: (Semigroupoidal t, Functor f) => SF t f <~> f :+: t f (SF t f)
matchingSF = isoF matchSF (inject !*! consSF)

-- | A type @'SF' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain1' t f@ is an actual concrete ADT that contains
-- successive applications of @t@ to itself, and you can pattern match on
-- each layer.
--
-- 'unrollingSF' states that the two types are isormorphic.  Use 'runollSF'
-- and 'rerollSF' to convert between the two.
unrollingSF :: forall t f. (Semigroupoidal t, Functor f) => SF t f <~> Chain1 t f
unrollingSF = isoF unrollSF rerollSF

-- | A type @'SF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unrollSF' makes that successive application explicit,
-- buy converting it to a literal 'Chain1' of applications of @t@ to
-- itself.
unrollSF :: forall t f. (Semigroupoidal t, Functor f) => SF t f ~> Chain1 t f
unrollSF = unfoldChain1 (matchSF @t)

-- | A type @'SF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollSF' takes an explicit 'Chain1' of applications
-- of @t@ to itself and rolls it back up into an @'SF' t@.
rerollSF :: Semigroupoidal t => Chain1 t f ~> SF t f
rerollSF = foldChain1 inject consSF

-- | Useful wrapper over 'retractT' to allow you to directly extract an @a@
-- from a @t f f a@, if @f@ is a valid retraction from @t@, and @f@ is an
-- instance of 'Copointed'.
--
-- Useful @f@s include 'Identity' or related newtype wrappers from
-- base:
--
-- @
-- 'extractT'
--     :: ('Monoidal' t, 'C' ('MF' t) 'Identity')
--     => t 'Identity' 'Identity' a
--     -> a
-- @
extractT
    :: (Semigroupoidal t, C (SF t) f, Copointed f)
    => t f f a
    -> a
extractT = copoint . biretract

-- | Useful wrapper over 'interpret' to allow you to directly extract
-- a value @b@ out of the @t f a@, if you can convert @f x@ into @b@.
--
-- Note that depending on the constraints on the interpretation of @t@, you
-- may have extra constraints on @b@.
--
-- *    If @'C' ('MF' t)@ is 'Data.Constraint.Trivial.Unconstrained', there
--      are no constraints on @b@
-- *    If @'C' ('MF' t)@ is 'Apply', @b@ needs to be an instance of 'Semigroup'
-- *    If @'C' ('MF' t)@ is 'Applicative', @b@ needs to be an instance of 'Monoid'
--
-- For some constraints (like 'Monad'), this will not be usable.
--
-- @
-- -- Return the length of either the list, or the Map, depending on which
-- --   one s in the '+'
-- length !*! length
--     :: ([] :+: Map Int) Char
--     -> Int
--
-- -- Return the length of both the list and the map, added together
-- (Sum . length) !*! (Sum . length)
--     :: Day [] (Map Int) Char
--     -> Sum Int
-- @
getT
    :: (Semigroupoidal t, C (SF t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
getT f g = getConst . binterpret (Const . f) (Const . g)

-- | Infix alias for 'getT'
(!$!)
    :: (Semigroupoidal t, C (SF t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
(!$!) = getT
infixr 5 !$!

-- | Infix alias for 'binterpret'
(!*!)
    :: (Semigroupoidal t, C (SF t) h)
    => (f ~> h)
    -> (g ~> h)
    -> t f g
    ~> h
(!*!) = binterpret
infixr 5 !*!

-- | Useful wrapper over 'getT' to allow you to collect a @b@ from all
-- instances of @f@ and @g@ inside a @t f g a@.
--
-- This will work if @'C' t@ is 'Data.Constraint.Trivial.Unconstrained',
-- 'Apply', or 'Applicative'.
collectT
    :: (Semigroupoidal t, C (SF t) (Const [b]))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> [b]
collectT f g = getConst . binterpret (Const . (:[]) . f) (Const . (:[]) . g)

instance Associative (:*:) where
    associating = isoF to_ from_
      where
        to_   (x :*: (y :*: z)) = (x :*: y) :*: z
        from_ ((x :*: y) :*: z) = x :*: (y :*: z)

instance Semigroupoidal (:*:) where
    type SF (:*:) = NonEmptyF

    appendSF (NonEmptyF xs :*: NonEmptyF ys) = NonEmptyF (xs <> ys)
    matchSF x = case ys of
        L1 ~Proxy -> L1 y
        R1 zs     -> R1 $ y :*: zs
      where
        y :*: ys = fromListF `hright` nonEmptyProd x

    consSF (x :*: NonEmptyF xs) = NonEmptyF $ x :| toList xs
    toSF   (x :*: y           ) = NonEmptyF $ x :| [y]

    biretract (x :*: y) = x <!> y
    binterpret f g (x :*: y) = f x <!> g y

instance Associative Day where
    associating = isoF D.assoc D.disassoc

instance Semigroupoidal Day where
    type SF Day = Ap1

    appendSF (Day x y z) = z <$> x <.> y
    matchSF a = case fromAp `hright` ap1Day a of
      Day x y z -> case y of
        L1 (Identity y') -> L1 $ (`z` y') <$> x
        R1 ys            -> R1 $ Day x ys z

    consSF (Day x y z) = Ap1 x $ flip z <$> toAp y
    toSF   (Day x y z) = z <$> inject x <.> inject y

    biretract (Day x y z) = z <$> x <.> y
    binterpret f g (Day x y z) = z <$> f x <.> g y

instance Associative (:+:) where
    associating = isoF to_ from_
      where
        to_ = \case
          L1 x      -> L1 (L1 x)
          R1 (L1 y) -> L1 (R1 y)
          R1 (R1 z) -> R1 z
        from_ = \case
          L1 (L1 x) -> L1 x
          L1 (R1 y) -> R1 (L1 y)
          R1 z      -> R1 (R1 z)

instance Semigroupoidal (:+:) where
    type SF (:+:) = Step

    appendSF = \case
      L1 x          -> x
      R1 (Step n y) -> Step (n + 1) y
    matchSF = hright R1 . stepDown

    consSF = \case
      L1 x          -> Step 0       x
      R1 (Step n y) -> Step (n + 1) y
    toSF = \case
      L1 x -> Step 0 x
      R1 y -> Step 1 y

    biretract = \case
      L1 x -> x
      R1 y -> y
    binterpret f g = \case
      L1 x -> f x
      R1 y -> g y

instance Associative Comp where
    associating = isoF to_ from_
      where
        to_   (x :>>= y) = (x :>>= (unComp . y)) :>>= id
        from_ ((x :>>= y) :>>= z) = x :>>= ((:>>= z) . y)

instance Semigroupoidal Comp where
    type SF Comp = Free1

    appendSF (x :>>= y) = x >>- y
    matchSF = matchFree1

    consSF (x :>>= y) = liftFree1 x >>- y
    toSF   (x :>>= g) = liftFree1 x >>- inject . g

    biretract      (x :>>= y) = x >>- y
    binterpret f g (x :>>= y) = f x >>- (g . y)

instance (Interpret t, HBind t) => Associative (ClownT t) where
    associating = isoF runClownT                ClownT
                . isoF (hmap (ClownT . inject)) (hbind runClownT)
                . isoF ClownT                   runClownT

data LiftT t f a = PureT   (f a)
                 | ImpureT (t f a)
  deriving Show

instance (Show1 (t f), Show1 f) => Show1 (LiftT t f) where
    liftShowsPrec sp sl d = \case
      PureT x -> showsUnaryWith (liftShowsPrec sp sl) "PureT" d x
      ImpureT x -> showsUnaryWith (liftShowsPrec sp sl) "ImpureT" d x


instance HFunctor t => HFunctor (LiftT t) where
    hmap f = \case
      PureT   x -> PureT   (f x)
      ImpureT x -> ImpureT (hmap f x)

instance Interpret t => Interpret (LiftT t) where
    type C (LiftT t) = C t
    inject  = PureT
    retract = \case
      PureT   x -> x
      ImpureT x -> retract x

instance (HBind t, Interpret t) => HBind (LiftT t) where
    hbind f = \case
      PureT   x -> f x
      ImpureT x -> ImpureT $ hbind ((\case PureT y -> inject y; ImpureT y -> y) . f) x

instance (Interpret t, HBind t) => Semigroupoidal (ClownT t) where
    type SF (ClownT t) = LiftT t

    appendSF = hbind id . ImpureT . runClownT
    matchSF  = \case
      PureT   x -> L1 x
      ImpureT x -> R1 $ ClownT x

-- data JokerChain1 t f a = JokerDone1 (f a)
--                        | JokerMore1 (JokerT t f (JokerChain1 t f) a)

-- data FreeI t f a = PureI (f a)
--                  | MoreI (t (FreeI t f) a)

-- data JokerChain1 t f a = JokerDone1 (f a)
--                        | JokerMore1 (t (JokerChain1 t f) a)


instance (Interpret t, HBind t) => Associative (JokerT t) where
    associating = isoF runJokerT         JokerT
                . isoF (hbind runJokerT) (hmap (JokerT . inject))
                . isoF JokerT            runJokerT

-- | A 'Chain1' unrolled from a @'JokerT' t@ is always infinitely long.
instance (Interpret t, HBind t) => Semigroupoidal (JokerT t) where
    type SF (JokerT t) = HFix (LiftT t)
    -- t  -- we have to be able to instantly retract!

    appendSF = HFix . ImpureT . runJokerT
    matchSF  (HFix x) = case x of
      PureT y   -> matchSF y
      ImpureT y -> R1 . JokerT $ y
    -- appendSF = hbind id . runJokerT
    -- hm, this is a problem, because rerollSF is not infinitely long. this
    -- has to be an inverse with inject !*! consSF
    --
    -- yeah, this is illegal, because this breaks with unrolling, and also
    -- even matching
    --
    -- overF (fromF (matchingSF @(Joker ListF))) id /= id
    --
    -- it's because we need to be able to retract from t, but we can't.
    -- t is bad!
    -- matchSF  = R1 . JokerT . hmap inject

-- newtype MaybeClownT t f g a = MaybeClownT { runMaybeClownT :: ComposeT MaybeF t f a }

-- deriving instance Functor (t f) => Functor (MaybeClownT t f g)

-- instance HFunctor t => HBifunctor (MaybeClownT t) where
--     hbimap f _ (MaybeClownT x) = MaybeClownT (hmap f x)

-- deriving via (WrappedHBifunctor (MaybeClownT t) f)
--     instance HFunctor t => HFunctor (MaybeClownT t f)

-- instance (Interpret t, HBind t, forall f. C t (MaybeF (t f))) => Associative (MaybeClownT t) where
--     associating = isoF runMaybeClownT MaybeClownT
--                 . isoF (hmap (MaybeClownT . ComposeT . MaybeF . Just . inject @t))
--                        (ComposeT . from_ . getComposeT)
--                 . isoF MaybeClownT    runMaybeClownT
--       where
--         from_ :: (Functor f, C t (MaybeF (t f))) => MaybeF (t (MaybeClownT t f g)) ~> MaybeF (t f)
--         from_ = MaybeF
--               . (=<<) (runMaybeF . interpret (getComposeT . runMaybeClownT))
--               . runMaybeF
--         -- from_ :: ComposeT MaybeF t (MaybeClownT t f g) ~> ComposeT MaybeF t f
--         -- from_ = ComposeT
--         --       . hbind (MaybeF . fmap _ . interpret @t (_ . getComposeT . runMaybeClownT))
--         --       . getComposeT
--         -- hmap (_ . runMaybeF . getComposeT . runMaybeClownT)
-- --       where
-- --         to_   :: MaybeClownT t f (MaybeClownT t g h) ~> MaybeClownT t (MaybeClownT t f g) h
-- --         to_ = MaybeClownT
-- --             . fmap (hmap (MaybeClownT . Just . inject))
-- --             . runMaybeClownT
-- --         from_ :: MaybeClownT t (MaybeClownT t f g) h ~> MaybeClownT t f (MaybeClownT t g h)
-- --         from_ = MaybeClownT
-- --               -- . runMaybeF
-- --               -- . hbind (MaybeF . _ . runMaybeF)
-- --               -- . MaybeF
-- --               . join
-- --               . fmap (_ . hbind (maybe _ id . runMaybeF) . hmap (MaybeF . runMaybeClownT))
-- --               -- . fmap (hbind (maybe _ id . runMaybeF) . hmap (MaybeF . runMaybeClownT))
-- --               . runMaybeClownT
