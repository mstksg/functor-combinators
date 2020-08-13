
module Data.HFunctor.Chain.Internal (
    Chain1(..)
  , foldChain1, unfoldChain1
  , toChain1, injectChain1
  , matchChain1
  , Chain(..)
  , foldChain, unfoldChain
  , splittingChain, unconsChain
  , DayChain1(..)
  , DayChain(..)
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Functor.Classes
import           Data.Functor.Contravariant
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.HBifunctor
import           Data.HFunctor
import           Data.Kind
import           Data.Typeable
import           GHC.Generics
import qualified Data.Functor.Invariant.Day as ID


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

-- | @since 0.3.0.0
instance (Contravariant f, Contravariant (t f (Chain1 t f))) => Contravariant (Chain1 t f) where
    contramap f = \case
      Done1 x  -> Done1 (contramap f x )
      More1 xs -> More1 (contramap f xs)

-- | @since 0.3.0.0
instance (Invariant f, Invariant (t f (Chain1 t f))) => Invariant (Chain1 t f) where
    invmap f g = \case
      Done1 x  -> Done1 (invmap f g x )
      More1 xs -> More1 (invmap f g xs)

instance HBifunctor t => HFunctor (Chain1 t) where
    hmap f = foldChain1 (Done1 . f) (More1 . hleft f)

instance HBifunctor t => Inject (Chain1 t) where
    inject  = injectChain1

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
    go = (\case L1 x -> Done1 x; R1 y -> More1 (hright go y)) . f

-- | Convert a tensor value pairing two @f@s into a two-item 'Chain1'.  An
-- analogue of 'toNonEmptyBy'.
--
-- @since 0.3.1.0
toChain1 :: HBifunctor t => t f f ~> Chain1 t f
toChain1 = More1 . hright Done1

-- | Create a singleton 'Chain1'.
--
-- @since 0.3.0.0
injectChain1 :: f ~> Chain1 t f
injectChain1 = Done1

-- | For completeness, an isomorphism between 'Chain1' and its two
-- constructors, to match 'matchNE'.
--
-- @since 0.3.0.0
matchChain1 :: Chain1 t f ~> (f :+: t f (Chain1 t f))
matchChain1 = \case
    Done1 x  -> L1 x
    More1 xs -> R1 xs

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

instance HBifunctor t => HFunctor (Chain t i) where
    hmap f = foldChain Done (More . hleft f)

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
    go = (\case L1 x -> Done x; R1 y ->  More (hright go y)) . f

-- | For completeness, an isomorphism between 'Chain' and its two
-- constructors, to match 'splittingLB'.
--
-- @since 0.3.0.0
splittingChain :: Chain t i f <~> (i :+: t f (Chain t i f))
splittingChain = isoF unconsChain $ \case
      L1 x  -> Done x
      R1 xs -> More xs

-- | An analogue of 'unconsLB': match one of the two constructors of
-- a 'Chain'.
--
-- @since 0.3.0.0
unconsChain :: Chain t i f ~> i :+: t f (Chain t i f)
unconsChain = \case
    Done x  -> L1 x
    More xs -> R1 xs

-- | Instead of defining yet another separate free semigroup like
-- 'Data.Functor.Apply.Free.Ap1',
-- 'Data.Functor.Contravariant.Divisible.Free.Div1', or
-- 'Data.Functor.Contravariant.Divisible.Free.Dec1', we re-use 'Chain1'.
--
-- You can assemble values using the combinators in "Data.HFunctor.Chain",
-- and then tear them down/interpret them using 'runCoDayChain1' and
-- 'runContraDayChain1'.  There is no general invariant interpreter (and so no
-- 'SemigroupIn' instance for 'Day') because the typeclasses used to
-- express the target contexts are probably not worth defining given how
-- little the Haskell ecosystem uses invariant functors as an abstraction.
newtype DayChain1 f a = DayChain1_ { unDayChain1 :: Chain1 ID.Day f a }
  deriving (Invariant, HFunctor, Inject)

-- | Instead of defining yet another separate free monoid like
-- 'Control.Applicative.Free.Ap',
-- 'Data.Functor.Contravariant.Divisible.Free.Div', or
-- 'Data.Functor.Contravariant.Divisible.Free.Dec', we re-use 'Chain'.
--
-- You can assemble values using the combinators in "Data.HFunctor.Chain",
-- and then tear them down/interpret them using 'runCoDayChain' and
-- 'runContraDayChain'.  There is no general invariant interpreter (and so no
-- 'MonoidIn' instance for 'Day') because the typeclasses used to express
-- the target contexts are probably not worth defining given how little the
-- Haskell ecosystem uses invariant functors as an abstraction.
newtype DayChain f a = DayChain { unDayChain :: Chain ID.Day Identity f a }
  deriving (Invariant, HFunctor)

instance Inject DayChain where
    inject x = DayChain $ More (ID.Day x (Done (Identity ())) const (,()))
