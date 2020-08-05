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
-- The type @'Chain' t@, for any @'Tensor' t@, is meant to be the same as
-- @'ListBy' t@ (the monoidal functor combinator for @t@), and represents
-- "zero or more" applications of @f@ to @t@.
--
-- The type @'Chain1' t@, for any @'Associative' t@, is meant to be the
-- same as @'NonEmptyBy' t@ (the semigroupoidal functor combinator for @t@) and
-- represents "one or more" applications of @f@ to @t@.
--
-- The advantage of using 'Chain' and 'Chain1' over 'ListBy' or 'NonEmptyBy' is that
-- they provide a universal interface for pattern matching and constructing
-- such values, which may simplify working with new such functor
-- combinators you might encounter.
module Data.HFunctor.Chain (
  -- * 'Chain'
    Chain(..)
  , foldChain
  , unfoldChain
  , unroll
  , reroll
  , unrolling
  , appendChain
  , splittingChain
  , chainPair
  , injectChain
  , splitChain
  -- * 'Chain1'
  , Chain1(..)
  , foldChain1
  , unfoldChain1
  , unrollingNE
  , unrollNE
  , rerollNE
  , appendChain1
  , fromChain1
  , matchChain1
  , chain1Pair
  , injectChain1
  -- ** Matchable
  -- | The following conversions between 'Chain' and 'Chain1' are only
  -- possible if @t@ is 'Matchable'
  , splittingChain1
  , splitChain1
  , matchingChain
  , unmatchChain
  ) where

import           Control.Monad.Freer.Church
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Day hiding              (intro1, intro2, elim1, elim2)
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor
import           Data.HFunctor.Interpret
import           Data.Kind
import           Data.Typeable
import           GHC.Generics
import qualified Data.Functor.Contravariant.Day       as CD
import qualified Data.Functor.Contravariant.Night     as N

-- | A useful construction that works like a "non-empty linked list" of @t
-- f@ applied to itself multiple times.  That is, it contains @t f f@, @t
-- f (t f f)@, @t f (t f (t f f))@, etc, with @f@ occuring /one or more/
-- times.  It is meant to be the same as @'NonEmptyBy' t@.
--
-- A @'Chain1' t f a@ is explicitly one of:
--
-- *  @f a@
-- *  @t f f a@
-- *  @t f (t f f) a@
-- *  @t f (t f (t f f)) a@
-- *  .. etc
--
-- Note that this is exactly the description of @'NonEmptyBy' t@.  And that's "the
-- point": for all instances of 'Associative', @'Chain1' t@ is
-- isomorphic to @'NonEmptyBy' t@ (witnessed by 'unrollingNE').  That's big picture
-- of 'NonEmptyBy': it's supposed to be a type that consists of all possible
-- self-applications of @f@ to @t@.
--
-- 'Chain1' gives you a way to work with all @'NonEmptyBy' t@ in a uniform way.
-- Unlike for @'NonEmptyBy' t f@ in general, you can always explicitly /pattern
-- match/ on a 'Chain1' (with its two constructors) and do what you please
-- with it.  You can also /construct/ 'Chain1' using normal constructors
-- and functions.
--
-- You can convert in between @'NonEmptyBy' t f@ and @'Chain1' t f@ with 'unrollNE'
-- and 'rerollNE'.  You can fully "collapse" a @'Chain1' t f@ into an @f@
-- with 'retract', if you have @'SemigroupIn' t f@; this could be considered
-- a fundamental property of semigroup-ness.
--
-- See 'Chain' for a version that has an "empty" value.
--
-- Another way of thinking of this is that @'Chain1' t@ is the "free
-- @'SemigroupIn' t@".  Given any functor @f@, @'Chain1' t f@ is
-- a semigroup in the semigroupoidal category of endofunctors enriched by
-- @t@.  So, @'Chain1' 'Control.Monad.Freer.Church.Comp'@ is the "free
-- 'Data.Functor.Bind.Bind'", @'Chain1' 'Day'@ is the "free
-- 'Data.Functor.Apply.Apply'", etc. You "lift" from @f a@ to @'Chain1'
-- t f a@ using 'inject'.
--
-- Note: this instance doesn't exist directly because of restrictions in
-- typeclasses, but is implemented as
--
-- @
-- 'Associative' t => 'SemigroupIn' ('WrapHBF' t) ('Chain1' t f)
-- @
--
-- where 'biretract' is 'appendChain1'.
--
-- You can fully "collapse" a @'Chain' t i f@ into an @f@ with
-- 'retract', if you have @'MonoidIn' t i f@; this could be considered
-- a fundamental property of monoid-ness.
--
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

instance (Contravariant f, Contravariant (t f (Chain1 t f))) => Contravariant (Chain1 t f) where
    contramap f = \case
      Done1 x  -> Done1 (contramap f x )
      More1 xs -> More1 (contramap f xs)

instance (Invariant f, Invariant (t f (Chain1 t f))) => Invariant (Chain1 t f) where
    invmap f g = \case
      Done1 x  -> Done1 (invmap f g x )
      More1 xs -> More1 (invmap f g xs)


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
    inject  = injectChain1

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

-- | Convert a tensor value pairing two @f@s into a two-item chain.
chain1Pair :: HBifunctor t => t f f ~> Chain1 t f
chain1Pair = More1 . hright Done1

-- | Create a singleton 'Chain1'.
injectChain1 :: f ~> Chain1 t f
injectChain1 = Done1

-- | A type @'NonEmptyBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain1' t f@ is an actual concrete ADT that contains
-- successive applications of @t@ to itself, and you can pattern match on
-- each layer.
--
-- 'unrollingNE' states that the two types are isormorphic.  Use 'unrollNE'
-- and 'rerollNE' to convert between the two.
unrollingNE :: forall t f. (Associative t, FunctorBy t f) => NonEmptyBy t f <~> Chain1 t f
unrollingNE = isoF unrollNE rerollNE

-- | A type @'NonEmptyBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unrollNE' makes that successive application explicit,
-- buy converting it to a literal 'Chain1' of applications of @t@ to
-- itself.
--
-- @
-- 'unrollNE' = 'unfoldChain1' 'matchNE'
-- @
unrollNE :: (Associative t, FunctorBy t f) => NonEmptyBy t f ~> Chain1 t f
unrollNE = unfoldChain1 matchNE

-- | A type @'NonEmptyBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollNE' takes an explicit 'Chain1' of applications
-- of @t@ to itself and rolls it back up into an @'NonEmptyBy' t@.
--
-- @
-- 'rerollNE' = 'foldChain1' 'inject' 'consNE'
-- @
rerollNE :: Associative t => Chain1 t f ~> NonEmptyBy t f
rerollNE = foldChain1 inject consNE

-- | 'Chain1' is a semigroup with respect to @t@: we can "combine" them in
-- an associative way.
--
-- This is essentially 'biretract', but only requiring @'Associative' t@:
-- it comes from the fact that @'Chain1' t@ is the "free @'SemigroupIn'
-- t@".
--
-- @since 0.1.1.0
appendChain1
    :: forall t f. (Associative t, FunctorBy t f)
    => t (Chain1 t f) (Chain1 t f) ~> Chain1 t f
appendChain1 = unrollNE
             . appendNE
             . hbimap rerollNE rerollNE

-- | @'Chain1' t@ is the "free @'SemigroupIn' t@".  However, we have to
-- wrap @t@ in 'WrapHBF' to prevent overlapping instances.
instance (Associative t, FunctorBy t f, FunctorBy t (Chain1 t f)) => SemigroupIn (WrapHBF t) (Chain1 t f) where
    biretract = appendChain1 . unwrapHBF
    binterpret f g = biretract . hbimap f g

-- | @'Chain1' 'Day'@ is the free "semigroup in the semigroupoidal category
-- of endofunctors enriched by 'Day'" --- aka, the free 'Apply'.
instance Functor f => Apply (Chain1 Day f) where
    f <.> x = appendChain1 $ Day f x ($)

instance Functor f => Apply (Chain1 Comp f) where
    (<.>) = apDefault

-- | @'Chain1' 'Comp'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'Comp'" --- aka, the free 'Bind'.
instance Functor f => Bind (Chain1 Comp f) where
    x >>- f = appendChain1 (x :>>= f)

-- | @'Chain1' (':*:')@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by ':*:'" --- aka, the free 'Alt'.
instance Functor f => Alt (Chain1 (:*:) f) where
    x <!> y = appendChain1 (x :*: y)

-- | @'Chain1' 'Product'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'Product'" --- aka, the free 'Alt'.
instance Functor f => Alt (Chain1 Product f) where
    x <!> y = appendChain1 (Pair x y)

-- | @'Chain1' 'CD.Day'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'CD.Day'" --- aka, the free 'Divise'.
instance Contravariant f => Divise (Chain1 CD.Day f) where
    divise f x y = appendChain1 $ CD.Day x y f

-- | @'Chain1' 'N.Night'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'N.Night'" --- aka, the free
-- 'Decide'.
instance Contravariant f => Decide (Chain1 N.Night f) where
    decide f x y = appendChain1 $ N.Night x y f

-- | A useful construction that works like a "linked list" of @t f@ applied
-- to itself multiple times.  That is, it contains @t f f@, @t f (t f f)@,
-- @t f (t f (t f f))@, etc, with @f@ occuring /zero or more/ times.  It is
-- meant to be the same as @'ListBy' t@.
--
-- If @t@ is 'Tensor', then it means we can "collapse" this linked list
-- into some final type @'ListBy' t@ ('reroll'), and also extract it back
-- into a linked list ('unroll').
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
-- Note that this is /exactly/ what an @'ListBy' t@ is supposed to be.  Using
-- 'Chain' allows us to work with all @'ListBy' t@s in a uniform way, with
-- normal pattern matching and normal constructors.
--
-- You can fully "collapse" a @'Chain' t i f@ into an @f@ with
-- 'retract', if you have @'MonoidIn' t i f@; this could be considered
-- a fundamental property of monoid-ness.
--
-- Another way of thinking of this is that @'Chain' t i@ is the "free
-- @'MonoidIn' t i@".  Given any functor @f@, @'Chain' t i f@ is a monoid
-- in the monoidal category of endofunctors enriched by @t@.  So, @'Chain'
-- 'Control.Monad.Freer.Church.Comp' 'Data.Functor.Identity.Identity'@ is
-- the "free 'Monad'", @'Chain' 'Data.Functor.Day.Day'
-- 'Data.Functor.Identity.Identity'@ is the "free 'Applicative'", etc.  You
-- "lift" from @f a@ to @'Chain' t i f a@ using 'inject'.
--
-- Note: this instance doesn't exist directly because of restrictions in
-- typeclasses, but is implemented as
--
-- @
-- 'Tensor' t i => 'MonoidIn' ('WrapHBF' t) ('WrapF' i) ('Chain' t i f)
-- @
--
-- where 'pureT' is 'Done' and 'biretract' is 'appendChain'.
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

instance (Contravariant i, Contravariant (t f (Chain t i f))) => Contravariant (Chain t i f) where
    contramap f = \case
      Done x  -> Done (contramap f x )
      More xs -> More (contramap f xs)

instance (Invariant i, Invariant (t f (Chain t i f))) => Invariant (Chain t i f) where
    invmap f g = \case
      Done x  -> Done (invmap f g x )
      More xs -> More (invmap f g xs)

-- | Recursively fold down a 'Chain'.  Provide a function on how to handle
-- the "single @f@ case" ('nilLB'), and how to handle the "combined @t f g@
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
    inject = injectChain

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

-- | Convert a tensor value pairing two @f@s into a two-item chain.
chainPair :: Tensor t i => t f f ~> Chain t i f
chainPair = More . hright inject

-- | Create a singleton chain
injectChain :: Tensor t i => f ~> Chain t i f
injectChain = More . hright Done . intro1

-- | A 'Chain1' is "one or more linked @f@s", and a 'Chain' is "zero or
-- more linked @f@s".  So, we can convert from a 'Chain1' to a 'Chain' that
-- always has at least one @f@.
--
-- The result of this function always is made with 'More' at the top level.
fromChain1
    :: Tensor t i
    => Chain1 t f ~> Chain t i f
fromChain1 = foldChain1 (More . hright Done . intro1) More

-- | A type @'ListBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain' t i f@ is an actual concrete
-- ADT that contains successive applications of @t@ to itself, and you can
-- pattern match on each layer.
--
-- 'unrolling' states that the two types are isormorphic.  Use 'unroll'
-- and 'reroll' to convert between the two.
unrolling
    :: Tensor t i
    => ListBy t f <~> Chain t i f
unrolling = isoF unroll reroll

-- | A type @'ListBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unroll' makes that successive application explicit,
-- buy converting it to a literal 'Chain' of applications of @t@ to
-- itself.
--
-- @
-- 'unroll' = 'unfoldChain' 'unconsLB'
-- @
unroll
    :: Tensor t i
    => ListBy t f ~> Chain t i f
unroll = unfoldChain unconsLB

-- | A type @'ListBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollNE' takes an explicit 'Chain' of applications of
-- @t@ to itself and rolls it back up into an @'ListBy' t@.
--
-- @
-- 'reroll' = 'foldChain' 'nilLB' 'consLB'
-- @
--
-- Because @t@ cannot be inferred from the input or output, you should call
-- this with /-XTypeApplications/:
--
-- @
-- 'reroll' \@'Control.Monad.Freer.Church.Comp'
--     :: 'Chain' Comp 'Data.Functor.Identity.Identity' f a -> 'Control.Monad.Freer.Church.Free' f a
-- @
reroll
    :: forall t i f. Tensor t i
    => Chain t i f ~> ListBy t f
reroll = foldChain (nilLB @t) consLB

-- | 'Chain' is a monoid with respect to @t@: we can "combine" them in
-- an associative way.  The identity here is anything made with the 'Done'
-- constructor.
--
-- This is essentially 'biretract', but only requiring @'Tensor' t i@: it
-- comes from the fact that @'Chain1' t i@ is the "free @'MonoidIn' t i@".
-- 'pureT' is 'Done'.
--
-- @since 0.1.1.0
appendChain
    :: forall t i f. Tensor t i
    => t (Chain t i f) (Chain t i f) ~> Chain t i f
appendChain = unroll
            . appendLB
            . hbimap reroll reroll

-- | For completeness, an isomorphism between 'Chain1' and its two
-- constructors, to match 'matchNE'.
matchChain1 :: Chain1 t f ~> (f :+: t f (Chain1 t f))
matchChain1 = \case
    Done1 x  -> L1 x
    More1 xs -> R1 xs

-- | For completeness, an isomorphism between 'Chain' and its two
-- constructors, to match 'splittingLB'.
splittingChain :: Chain t i f <~> (i :+: t f (Chain t i f))
splittingChain = isoF to_ from_
  where
    to_ = \case
      Done x  -> L1 x
      More xs -> R1 xs
    from_ = \case
      L1 x  -> Done x
      R1 xs -> More xs

-- | An analogue of 'splitLB': match one of the two constructors of
-- a 'Chain'.
splitChain :: Chain t i f ~> i :+: t f (Chain t i f)
splitChain = \case
    Done x  -> L1 x
    More xs -> R1 xs

-- | A @'Chain1' t f@ is like a non-empty linked list of @f@s, and
-- a @'Chain' t i f@ is a possibly-empty linked list of @f@s.  This
-- witnesses the fact that the former is isomorphic to @f@ consed to the
-- latter.
splittingChain1
    :: forall t i f. (Matchable t i, FunctorBy t f)
    => Chain1 t f <~> t f (Chain t i f)
splittingChain1 = fromF unrollingNE
                . splittingNE @t
                . overHBifunctor id unrolling

-- | The "forward" function representing 'splittingChain1'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
splitChain1
    :: forall t i f. Tensor t i
    => Chain1 t f ~> t f (Chain t i f)
splitChain1 = hright (unroll @t) . splitNE @t . rerollNE

-- | A @'Chain' t i f@ is a linked list of @f@s, and a @'Chain1' t f@ is
-- a non-empty linked list of @f@s.  This witnesses the fact that
-- a @'Chain' t i f@ is either empty (@i@) or non-empty (@'Chain1' t f@).
matchingChain
    :: forall t i f. (Tensor t i, Matchable t i, FunctorBy t f)
    => Chain t i f <~> i :+: Chain1 t f
matchingChain = fromF unrolling
              . matchingLB @t
              . overHBifunctor id unrollingNE

-- | The "reverse" function representing 'matchingChain'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
unmatchChain
    :: forall t i f. Tensor t i
    => i :+: Chain1 t f ~> Chain t i f
unmatchChain = unroll . (nilLB @t !*! fromNE @t) . hright rerollNE

-- | We have to wrap @t@ in 'WrapHBF' to prevent overlapping instances.
instance (Tensor t i, FunctorBy t (Chain t i f)) => SemigroupIn (WrapHBF t) (Chain t i f) where
    biretract = appendChain . unwrapHBF
    binterpret f g = biretract . hbimap f g

-- | @'Chain' t i@ is the "free @'MonoidIn' t i@".  However, we have to
-- wrap @t@ in 'WrapHBF' and @i@ in 'WrapF' to prevent overlapping instances.
instance (Tensor t i, FunctorBy t (Chain t i f)) => MonoidIn (WrapHBF t) (WrapF i) (Chain t i f) where
    pureT = Done . unwrapF

instance Apply (Chain Day Identity f) where
    f <.> x = appendChain $ Day f x ($)

-- | @'Chain' 'Day' 'Identity'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by 'Day'" --- aka, the free
-- 'Applicative'.
instance Applicative (Chain Day Identity f) where
    pure  = Done . Identity
    (<*>) = (<.>)

instance Divise (Chain CD.Day Proxy f) where
    divise f x y = appendChain $ CD.Day x y f

-- | @'Chain' 'CD.Day' 'Proxy'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by contravariant 'CD.Day'" --- aka,
-- the free 'Divisible'.
instance Divisible (Chain CD.Day Proxy f) where
    divide f x y = appendChain $ CD.Day x y f
    conquer = Done Proxy

instance Decide (Chain N.Night N.Not f) where
    decide f x y = appendChain $ N.Night x y f

-- | @'Chain' 'N.Night' 'N.Refutec'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by 'N.Night'" --- aka, the free
-- 'Conclude'.
instance Conclude (Chain N.Night N.Not f) where
    conclude = Done . N.Not

instance Apply (Chain Comp Identity f) where
    (<.>) = apDefault

instance Applicative (Chain Comp Identity f) where
    pure  = Done . Identity
    (<*>) = (<.>)

instance Bind (Chain Comp Identity f) where
    x >>- f = appendChain (x :>>= f)

-- | @'Chain' 'Comp' 'Identity'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by 'Comp'" --- aka, the free
-- 'Monad'.
instance Monad (Chain Comp Identity f) where
    (>>=) = (>>-)

instance Functor f => Alt (Chain (:*:) Proxy f) where
    x <!> y = appendChain (x :*: y)

-- | @'Chain' (':*:') 'Proxy'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by ':*:'" --- aka, the free
-- 'Plus'.
instance Functor f => Plus (Chain (:*:) Proxy f) where
    zero = Done Proxy

instance Functor f => Alt (Chain Product Proxy f) where
    x <!> y = appendChain (Pair x y)

-- | @'Chain' (':*:') 'Proxy'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by ':*:'" --- aka, the free
-- 'Plus'.
instance Functor f => Plus (Chain Product Proxy f) where
    zero = Done Proxy
