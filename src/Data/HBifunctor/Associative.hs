{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
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

-- |
-- Module      : Data.HBifunctor.Associative
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides tools for working with binary functor combinators
-- that represent interpretable schemas.
--
-- These are types @'HBifunctor' t@ that take two functors @f@ and @g@ and returns a new
-- functor @t f g@, that "mixes together" @f@ and @g@ in some way.
--
-- The high-level usage of this is
--
-- @
-- 'biretract' :: t f f ~> f
-- @
--
-- which lets you fully "mix" together the two input functors.
--
-- This class also associates each 'HBifunctor' with its "semigroup functor
-- combinator", so we can "squish together" repeated applications of @t@.
--
-- That is, an @'SF' t f a@ is either:
--
-- *   @f a@
-- *   @t f f a@
-- *   @t f (t f f) a@
-- *   @t f (t f (t f f)) a@
-- *   .. etc.
--
-- which means we can have "list-like" schemas that represent multiple
-- copies of @f@.
--
-- See "Data.HBifunctor.Tensor" for a version that also provides an analogy
-- to 'inject', and a more flexible "squished" combinator
-- 'Data.HBifunctor.Tensor.MF' that has an "empty" element.
module Data.HBifunctor.Associative (
  -- * 'Associative'
    Associative(..)
  , assoc
  , disassoc
  -- * 'Semigroupoidal'
  , Semigroupoidal(..)
  , matchingSF
  -- ** Utility
  , getS
  , collectS
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
import           Control.Natural
import           Data.Data
import           Data.Foldable
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Day           (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.HBifunctor
import           Data.HFunctor
import           Data.HFunctor.Interpret
import           Data.HFunctor.IsoF
import           Data.Kind
import           Data.List.NonEmpty         (NonEmpty(..))
import           GHC.Generics hiding        (C)
import qualified Data.Functor.Day           as D

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

-- | For some @t@s, you can represent the act of applying a functor @f@ to
-- @t@ many times, as a single type.  That is, there is some type @'SF'
-- t f@ that is equivalent to one of:
--
-- *  @f a@                             -- 1 time
-- *  @t f f a@                         -- 2 times
-- *  @t f (t f f) a@                   -- 3 times
-- *  @t f (t f (t f f)) a@             -- 4 times
-- *  @t f (t f (t f (t f f))) a@       -- 5 times
-- *  .. etc
--
-- This typeclass associates each @t@ with its "semigroupoidal functor
-- combinator" @'SF' t@.
--
-- This is useful because sometimes you might want to describe a type that
-- can be @t f f@, @t f (t f f)@, @t f (t f (t f f))@, etc.; "f applied to
-- itself", with at least one @f@.  This typeclass lets you use a type like
-- 'NonEmptyF' in terms of repeated applications of ':*:', or 'Ap1' in
-- terms of repeated applications of 'Day', or 'Free1' in terms of repeated
-- applications of 'Comp', etc.
--
-- For example, @f ':*:' f@ can be interpreted as "a free selection of two
-- @f@s", allowing you to specify "I have to @f@s that I can use".  If you
-- want to specify "I want 1, 2, or many different @f@s that I can use",
-- you can use @'NonEmptyF' f@.
--
-- At the high level, the main way to /use/ a 'Semigroupoidal' is with
-- 'biretract' and 'binterpret':
--
-- @
-- 'biretract' :: t f f '~>' f
-- 'binterpret' :: (f ~> h) -> (g ~> h) -> t f g ~> h
-- @
--
-- which are like the 'HBifunctor' versions of 'retract' and 'interpret':
-- they fully "mix" together the two inputs of @t@.
--
-- Also useful is:
--
-- @
-- 'toSF' :: t f f a -> SF t f a
-- @
--
-- Which converts a @t@ into its aggregate type 'SF'
class (Associative t, Interpret (SF t)) => Semigroupoidal t where
    -- | The "semigroup functor combinator" generated by @t@.
    --
    -- A value of type @SF t f a@ is either:
    --
    -- *  @f a@
    -- *  @t f f a@
    -- *  @t f (t f f) a@
    -- *  @t f (t f (t f f)) a@
    -- *  @t f (t f (t f (t f f))) a@
    -- *  .. etc
    --
    -- For example, for ':*:', we have 'NonEmptyF'.  This is because:
    --
    -- @
    -- x             ~ NonEmptyF (x :| [])
    -- x :*: y       ~ NonEmptyF (x :| [y])
    -- x :*: y :*: z ~ NonEmptyF (x :| [y,z])
    -- -- etc.
    -- @
    --
    -- You can create an "singleton" one with 'inject', or else one from
    -- a single @t f f@ with 'toSF'.
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

    -- | The 'HBifunctor' analogy of 'retract'. It retracts /both/ @f@s
    -- into a single @f@, effectively fully mixing them together.
    biretract :: C (SF t) f => t f f ~> f
    biretract = retract . toSF

    -- | The 'HBifunctor' analogy of 'interpret'.  It takes two
    -- interpreting functions, and mixes them together into a target
    -- functor @h@.
    binterpret
        :: C (SF t) h
        => f ~> h
        -> g ~> h
        -> t f g ~> h
    binterpret f g = retract . toSF . hbimap f g

    {-# MINIMAL appendSF, matchSF #-}

-- | A @'Chain1' t f a@ is explicitly one of:
--
-- *  @f a@
-- *  @t f f a@
-- *  @t f (t f f) a@
-- *  @t f (t f (t f f)) a@
-- *  .. etc
--
-- Note that this is exactly the description of @'SF' t@.  And that's "the
-- point": for all instances of 'Semigroupoidal', @'Chain1' t@ is
-- isomorphic to @'SF' t@ (witnessed by 'unrollingSF').  That's big picture
-- of 'SF': it's supposed to be a type that consists of all possible
-- self-applications of @f@ to @t@.
--
-- 'Chain1' gives you a way to work with all @'SF' t@ in a uniform way.
-- Unlike for @'SF' t f@ in general, you can always explicitly /pattern
-- match/ on a 'Chain1' (with its two constructors) and do what you please
-- with it.  You can also /construct/ 'Chain1' using normal constructors
-- and functions.
--
-- You can convert in between @'SF' t f@ and @'Chain1' t f@ with 'unrollSF'
-- and 'rerollSF'.
--
-- See 'Data.HBifunctor.Tensor.Chain' for a version that has an "empty"
-- value.
data Chain1 t f a = Done1 (f a)
                  | More1 (t f (Chain1 t f) a)
  deriving (Typeable, Generic)

deriving instance (Eq (f a), Eq (t f (Chain1 t f) a)) => Eq (Chain1 t f a)
deriving instance (Ord (f a), Ord (t f (Chain1 t f) a)) => Ord (Chain1 t f a)
deriving instance (Show (f a), Show (t f (Chain1 t f) a)) => Show (Chain1 t f a)
deriving instance (Read (f a), Read (t f (Chain1 t f) a)) => Read (Chain1 t f a)
deriving instance (Functor f, Functor (t f (Chain1 t f))) => Functor (Chain1 t f)
deriving instance (Foldable f, Foldable (t f (Chain1 t f))) => Foldable (Chain1 t f)
deriving instance (Traversable f, Traversable (t f (Chain1 t f))) => Traversable (Chain1 t f)

instance (Eq1 f, Eq1 (t f (Chain1 t f))) => Eq1 (Chain1 t f) where
    liftEq eq = \case
      Done1 x -> \case
        Done1 y -> liftEq eq x y
        More1 _ -> False
      More1 x -> \case
        Done1 _ -> False
        More1 y -> liftEq eq x y

instance (Ord1 f, Ord1 (t f (Chain1 t f))) => Ord1 (Chain1 t f) where
    liftCompare c = \case
      Done1 x -> \case
        Done1 y -> liftCompare c x y
        More1 _ -> LT
      More1 x -> \case
        Done1 _ -> GT
        More1 y -> liftCompare c x y

instance (Show1 (t f (Chain1 t f)), Show1 f) => Show1 (Chain1 t f) where
    liftShowsPrec sp sl d = \case
        Done1 x  -> showsUnaryWith (liftShowsPrec sp sl) "Done1" d x
        More1 xs -> showsUnaryWith (liftShowsPrec sp sl) "More1" d xs

instance (Functor f, Read1 (t f (Chain1 t f)), Read1 f) => Read1 (Chain1 t f) where
    liftReadsPrec rp rl = readsData $
            readsUnaryWith (liftReadsPrec rp rl) "Done1" Done1
         <> readsUnaryWith (liftReadsPrec rp rl) "More1" More1

-- | Recursively fold down a 'Chain1'.  Provide a function on how to handle
-- the "single @f@ case" ('inject'), and how to handle the "combined @t
-- f g@ case", and this will fold the entire @'Chain1' t f@ into a single
-- @g@.
--
-- This is a catamorphism.
foldChain1
    :: forall t f g. HBifunctor t
    => f ~> g                   -- ^ handle 'Done1'
    -> t f g ~> g               -- ^ handle 'More1'
    -> Chain1 t f ~> g
foldChain1 f g = go
  where
    go :: Chain1 t f ~> g
    go = \case
      Done1 x  -> f x
      More1 xs -> g (hright go xs)

-- | Recursively build up a 'Chain1'.  Provide a function that takes some
-- starting seed @g@ and returns either "done" (@f@) or "continue further"
-- (@t f g@), and it will create a @'Chain1' t f@ from a @g@.
--
-- This is an anamorphism.
unfoldChain1
    :: forall t f g. HBifunctor t
    => (g ~> f :+: t f g)
    -> g ~> Chain1 t f
unfoldChain1 f = go
  where
    go :: g ~> Chain1 t f
    go = (Done1 !*! More1 . hright go) . f

instance HBifunctor t => HFunctor (Chain1 t) where
    hmap f = foldChain1 (Done1 . f) (More1 . hleft f)

instance HBifunctor t => Inject (Chain1 t) where
    inject  = Done1

instance (HBifunctor t, Semigroupoidal t) => Interpret (Chain1 t) where
    type C (Chain1 t) = C (SF t)
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
-- 'unrollingSF' states that the two types are isormorphic.  Use 'unrollSF'
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

-- | Useful wrapper over 'binterpret' to allow you to directly extract
-- a value @b@ out of the @t f a@, if you can convert @f x@ into @b@.
--
-- Note that depending on the constraints on the interpretation of @t@, you
-- may have extra constraints on @b@.
--
-- *    If @'C' ('SF' t)@ is 'Data.Constraint.Trivial.Unconstrained', there
--      are no constraints on @b@
-- *    If @'C' ('SF' t)@ is 'Apply', @b@ needs to be an instance of 'Semigroup'
-- *    If @'C' ('SF' t)@ is 'Applicative', @b@ needs to be an instance of 'Monoid'
--
-- For some constraints (like 'Monad'), this will not be usable.
--
-- @
-- -- Return the length of either the list, or the Map, depending on which
-- --   one s in the '+'
-- 'getS' 'length' length
--     :: ([] :+: 'Data.Map.Map' 'Int') 'Char'
--     -> Int
--
-- -- Return the length of both the list and the map, added together
-- 'getS' ('Data.Monoid.Sum' . length) (Sum . length)
--     :: 'Day' [] (Map Int) Char
--     -> Sum Int
-- @
getS
    :: (Semigroupoidal t, C (SF t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
getS f g = getConst . binterpret (Const . f) (Const . g)

-- | Infix alias for 'getS'
--
-- @
-- -- Return the length of either the list, or the Map, depending on which
-- --   one s in the '+'
-- 'length' '!$!' length
--     :: ([] :+: 'Data.Map.Map' 'Int') 'Char'
--     -> Int
--
-- -- Return the length of both the list and the map, added together
-- 'Data.Monoid.Sum' . length !$! Sum . length
--     :: 'Day' [] (Map Int) Char
--     -> Sum Int
-- @
(!$!)
    :: (Semigroupoidal t, C (SF t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
(!$!) = getS
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

-- | Useful wrapper over 'getS' to allow you to collect a @b@ from all
-- instances of @f@ and @g@ inside a @t f g a@.
--
-- This will work if @'C' t@ is 'Data.Constraint.Trivial.Unconstrained',
-- 'Apply', or 'Applicative'.
collectS
    :: (Semigroupoidal t, C (SF t) (Const [b]))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> [b]
collectS f g = getS ((:[]) . f) ((:[]) . g)

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

instance HBind t => Associative (HClown t) where
    associating = isoF runHClown                HClown
                . isoF (hmap (HClown . inject)) (hbind runHClown)
                . isoF HClown                   runHClown


instance (Interpret t, HBind t) => Semigroupoidal (HClown t) where
    type SF (HClown t) = HLift t

    appendSF = hbind id . HOther . runHClown
    matchSF  = \case
      HPure  x -> L1 x
      HOther x -> R1 $ HClown x

instance HBind t => Associative (HJoker t) where
    associating = isoF runHJoker         HJoker
                . isoF (hbind runHJoker) (hmap (HJoker . inject))
                . isoF HJoker            runHJoker

instance (Interpret t, HBind t) => Semigroupoidal (HJoker t) where
    type SF (HJoker t) = HFree t

    appendSF = HJoin . runHJoker
    matchSF  = \case
      HReturn x -> L1 x
      HJoin   x -> R1 $ HJoker x
