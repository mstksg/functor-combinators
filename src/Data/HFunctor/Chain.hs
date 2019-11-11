{-# LANGUAGE DeriveFoldable        #-}
{-# LANGUAGE DeriveFunctor         #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE DeriveTraversable     #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE InstanceSigs          #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances  #-}

-- |
-- Module      : Data.HFunctor.Chain
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides an 'Interpret'able data type of "linked list of
-- tensor applications".
--
-- The type @'Chain' t@, for any @'Monoidal' t@, is meant to be the same as
-- @'MF' t@ (the monoidal functor combinator for @t@), and represents "zero
-- or more" applications of @f@ to @t@.
--
-- The type @'Chain1' t@, for any @'Semigroupoidal' t@, is meant to be the
-- same as @'SF' t@ (the semigroupoidal functor combinator for @t@) and
-- represents "one or more" applications of @f@ to @t@.
--
-- The advantage of using 'Chain' and 'Chain1' over 'MF' or 'SF' is that
-- they provide a universal interface for pattern matching and constructing
-- such values, which may simplify working with new such functor
-- combinators you might encounter.
module Data.HFunctor.Chain (
  -- * 'Chain'
    Chain(..)
  , foldChain
  , unfoldChain
  , unrollMF
  , rerollMF
  , unrollingMF
  , appendChain
  -- * 'Chain1'
  , Chain1(..)
  , foldChain1
  , unfoldChain1
  , unrollingSF
  , unrollSF
  , rerollSF
  , appendChain1
  , fromChain1
  -- ** Matchable
  -- | The following conversions between 'Chain' and 'Chain1' are only
  -- possible if @t@ is 'Matchable'
  , splittingChain1
  , splitChain1
  , matchingChain
  , unmatchChain
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Functor.Classes
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor
import           Data.HFunctor.Interpret
import           Data.Kind
import           Data.Typeable
import           GHC.Generics hiding         (C)

-- | A useful construction that works like a "non-empty linked list" of @t
-- f@ applied to itself multiple times.  That is, it contains @t f f@, @t
-- f (t f f)@, @t f (t f (t f f))@, etc, with @f@ occuring /one or more/
-- times.  It is meant to be the same as @'SF' t@.
--
-- A @'Chain1' t f a@ is explicitly one of:
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
-- and 'rerollSF'.  You can fully "collapse" a @'Chain1' t f@ into an @f@
-- with 'retract', if @t@ is 'Semigroupoidal'; this could be considered
-- a fundamental property of semigroupoidal-ness.
--
-- See 'Chain' for a version that has an "empty" value.
--
-- This construction is inspired by iteratees and machines.
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
    :: forall t f (g :: Type -> Type). HBifunctor t
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

instance (HBifunctor t, SemigroupIn t f) => Interpret (Chain1 t) f where
    retract = \case
      Done1 x  -> x
      More1 xs -> binterpret id retract xs
    interpret :: forall g. g ~> f -> Chain1 t g ~> f
    interpret f = go
      where
        go :: Chain1 t g ~> f
        go = \case
          Done1 x  -> f x
          More1 xs -> binterpret f go xs

-- | A type @'SF' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain1' t f@ is an actual concrete ADT that contains
-- successive applications of @t@ to itself, and you can pattern match on
-- each layer.
--
-- 'unrollingSF' states that the two types are isormorphic.  Use 'unrollSF'
-- and 'rerollSF' to convert between the two.
unrollingSF :: forall t f. (SemigroupIn t f, Functor f) => SF t f <~> Chain1 t f
unrollingSF = isoF unrollSF rerollSF

-- | A type @'SF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unrollSF' makes that successive application explicit,
-- buy converting it to a literal 'Chain1' of applications of @t@ to
-- itself.
--
-- @
-- 'unrollSF' = 'unfoldChain1' 'matchSF'
-- @
unrollSF :: (SemigroupIn t f, Functor f) => SF t f ~> Chain1 t f
unrollSF = unfoldChain1 matchSF

-- | A type @'SF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollSF' takes an explicit 'Chain1' of applications
-- of @t@ to itself and rolls it back up into an @'SF' t@.
--
-- @
-- 'rerollSF' = 'foldChain1' 'inject' 'consSF'
-- @
rerollSF :: SemigroupIn t f => Chain1 t f ~> SF t f
rerollSF = foldChain1 inject consSF

-- | 'Chain1' is a semigroup with respect to @t@: we can "combine" them in
-- an associative way.
--
-- @since 0.1.1.0
appendChain1
    :: forall t f. (SemigroupIn t f, Functor f)
    => t (Chain1 t f) (Chain1 t f) ~> Chain1 t f
appendChain1 = unrollSF
             . appendSF
             . hbimap rerollSF rerollSF

-- | A useful construction that works like a "linked list" of @t f@ applied
-- to itself multiple times.  That is, it contains @t f f@, @t f (t f f)@,
-- @t f (t f (t f f))@, etc, with @f@ occuring /zero or more/ times.  It is
-- meant to be the same as @'MF' t@.
--
-- If @t@ is 'Monoidal', then it means we can "collapse" this linked list
-- into some final type @'MF' t@ ('rerollMF'), and also extract it back
-- into a linked list ('unrollMF').
--
-- So, a value of type @'Chain' t i f a@ is one of either:
--
-- *  @i a@
-- *  @f a@
-- *  @t f f a@
-- *  @t f (t f f) a@
-- *  @t f (t f (t f f)) a@
-- *  .. etc.
--
-- Note that this is /exactly/ what an @'MF' t@ is supposed to be.  Using
-- 'Chain' allows us to work with all @'MF' t@s in a uniform way, with
-- normal pattern matching and normal constructors.
--
-- You can fully "collapse" a @'Chain' t t f@ into an @f@ with
-- 'retract', if @t@ is 'Monoidal'; this could be considered a fundamental
-- property of monoidal-ness.
--
-- This construction is inspired by
-- <http://oleg.fi/gists/posts/2018-02-21-single-free.html>
data Chain t i f a = Done (i a)
                   | More (t f (Chain t i f) a)

deriving instance (Eq (i a), Eq (t f (Chain t i f) a)) => Eq (Chain t i f a)
deriving instance (Ord (i a), Ord (t f (Chain t i f) a)) => Ord (Chain t i f a)
deriving instance (Show (i a), Show (t f (Chain t i f) a)) => Show (Chain t i f a)
deriving instance (Read (i a), Read (t f (Chain t i f) a)) => Read (Chain t i f a)
deriving instance (Functor i, Functor (t f (Chain t i f))) => Functor (Chain t i f)
deriving instance (Foldable i, Foldable (t f (Chain t i f))) => Foldable (Chain t i f)
deriving instance (Traversable i, Traversable (t f (Chain t i f))) => Traversable (Chain t i f)

instance (Eq1 i, Eq1 (t f (Chain t i f))) => Eq1 (Chain t i f) where
    liftEq eq = \case
      Done x -> \case
        Done y -> liftEq eq x y
        More _ -> False
      More x -> \case
        Done _ -> False
        More y -> liftEq eq x y

instance (Ord1 i, Ord1 (t f (Chain t i f))) => Ord1 (Chain t i f) where
    liftCompare c = \case
      Done x -> \case
        Done y -> liftCompare c x y
        More _ -> LT
      More x -> \case
        Done _ -> GT
        More y -> liftCompare c x y

instance (Show1 (t f (Chain t i f)), Show1 i) => Show1 (Chain t i f) where
    liftShowsPrec sp sl d = \case
        Done x  -> showsUnaryWith (liftShowsPrec sp sl) "Done" d x
        More xs -> showsUnaryWith (liftShowsPrec sp sl) "More" d xs

instance (Functor i, Read1 (t f (Chain t i f)), Read1 i) => Read1 (Chain t i f) where
    liftReadsPrec rp rl = readsData $
            readsUnaryWith (liftReadsPrec rp rl) "Done" Done
         <> readsUnaryWith (liftReadsPrec rp rl) "More" More

-- | Recursively fold down a 'Chain'.  Provide a function on how to handle
-- the "single @f@ case" ('nilMF'), and how to handle the "combined @t f g@
-- case", and this will fold the entire @'Chain' t i) f@ into a single @g@.
--
-- This is a catamorphism.
foldChain
    :: forall t i f g. HBifunctor t
    => (i ~> g)             -- ^ Handle 'Done'
    -> (t f g ~> g)         -- ^ Handle 'More'
    -> Chain t i f ~> g
foldChain f g = go
  where
    go :: Chain t i f ~> g
    go = \case
      Done x  -> f x
      More xs -> g (hright go xs)

-- | Recursively build up a 'Chain'.  Provide a function that takes some
-- starting seed @g@ and returns either "done" (@i@) or "continue further"
-- (@t f g@), and it will create a @'Chain' t i f@ from a @g@.
--
-- This is an anamorphism.
unfoldChain
    :: forall t f (g :: Type -> Type) i. HBifunctor t
    => (g ~> i :+: t f g)
    -> g ~> Chain t i f
unfoldChain f = go
  where
    go :: g a -> Chain t i f a
    go = (Done !*! More . hright go) . f

instance HBifunctor t => HFunctor (Chain t i) where
    hmap f = foldChain Done (More . hleft f)

instance Tensor t i => Inject (Chain t i) where
    inject = More . hright Done . intro1

-- | We can collapse and interpret an @'Chain' t i@ if we have @'Tensor' t@.
instance MonoidIn t i f => Interpret (Chain t i) f where
    interpret
        :: forall g. ()
        => g ~> f
        -> Chain t i g ~> f
    interpret f = go
      where
        go :: Chain t i g ~> f
        go = \case
          Done x  -> pureT @t x
          More xs -> binterpret f go xs

-- | A 'Chain1' is "one or more linked @f@s", and a 'Chain' is "zero or
-- more linked @f@s".  So, we can convert from a 'Chain1' to a 'Chain' that
-- always has at least one @f@.
--
-- The result of this function always is made with 'More' at the top level.
fromChain1
    :: Tensor t i
    => Chain1 t f ~> Chain t i f
fromChain1 = foldChain1 (More . hright Done . intro1) More

-- | A type @'MF' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain' t i f@ is an actual concrete
-- ADT that contains successive applications of @t@ to itself, and you can
-- pattern match on each layer.
--
-- 'unrollingMF' states that the two types are isormorphic.  Use 'unrollMF'
-- and 'rerollMF' to convert between the two.
unrollingMF
    :: MonoidIn t i f
    => MF t f <~> Chain t i f
unrollingMF = isoF unrollMF rerollMF

-- | A type @'MF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unrollMF' makes that successive application explicit,
-- buy converting it to a literal 'Chain' of applications of @t@ to
-- itself.
--
-- @
-- 'unrollMF' = 'unfoldChain' 'unconsMF'
-- @
unrollMF
    :: MonoidIn t i f
    => MF t f ~> Chain t i f
unrollMF = unfoldChain unconsMF

-- | A type @'MF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollSF' takes an explicit 'Chain' of applications of
-- @t@ to itself and rolls it back up into an @'MF' t@.
--
-- @
-- 'rerollMF' = 'foldChain' 'nilMF' 'consMF'
-- @
--
-- Because @t@ cannot be inferred from the input or output, you should call
-- this with /-XTypeApplications/:
--
-- @
-- 'rerollMF' \@'Control.Monad.Freer.Church.Comp'
--     :: 'Chain' Comp 'Data.Functor.Identity.Identity' f a -> 'Control.Monad.Freer.Church.Free' f a
-- @
rerollMF
    :: forall t i f. MonoidIn t i f
    => Chain t i f ~> MF t f
rerollMF = foldChain (nilMF @t) consMF

-- | 'Chain' is a monoid with respect to @t@: we can "combine" them in
-- an associative way.  The identity here is anything made with the 'Done'
-- constructor.
--
-- @since 0.1.1.0
appendChain
    :: forall t i f. MonoidIn t i f
    => t (Chain t i f) (Chain t i f) ~> Chain t i f
appendChain = unrollMF
            . appendMF
            . hbimap rerollMF rerollMF

-- | A @'Chain1' t f@ is like a non-empty linked list of @f@s, and
-- a @'Chain' t i f@ is a possibly-empty linked list of @f@s.  This
-- witnesses the fact that the former is isomorphic to @f@ consed to the
-- latter.
splittingChain1
    :: forall t i f. (MonoidIn t i f, Matchable t i, Functor f)
    => Chain1 t f <~> t f (Chain t i f)
splittingChain1 = fromF unrollingSF
                . splittingSF @t
                . overHBifunctor id unrollingMF

-- | The "forward" function representing 'splittingChain1'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
splitChain1
    :: forall t i f. MonoidIn t i f
    => Chain1 t f ~> t f (Chain t i f)
splitChain1 = hright (unrollMF @t) . splitSF @t . rerollSF

-- | A @'Chain' t i f@ is a linked list of @f@s, and a @'Chain1' t f@ is
-- a non-empty linked list of @f@s.  This witnesses the fact that
-- a @'Chain' t i f@ is either empty (@i@) or non-empty (@'Chain1' t f@).
matchingChain
    :: forall t i f. (MonoidIn t i f, Matchable t i, Functor f)
    => Chain t i f <~> i :+: Chain1 t f
matchingChain = fromF unrollingMF
              . matchingMF @t
              . overHBifunctor id unrollingSF

-- | The "reverse" function representing 'matchingChain'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
unmatchChain
    :: forall t i f. MonoidIn t i f
    => i :+: Chain1 t f ~> Chain t i f
unmatchChain = unrollMF . (nilMF @t !*! fromSF @t) . hright rerollSF
