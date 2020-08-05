
-- |
-- Module      : Data.Functor.Invariant.Day
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides an 'Invariant' version of the typical Haskell Day convolution
-- over tuples.
module Data.Functor.Invariant.Day (
    Day(..)
  , day
  , runDayApply
  , runDayDivise
  , toCoDay
  , toContraDay
  , assoc, unassoc
  , intro1, intro2
  , elim1, elim2
  , swapped
  , trans1, trans2
  -- * Chain
  , DayChain
  , runCoDayChain
  , runContraDayChain
  , assembleDayChain
  , assembleDayChainRec
  , gatherDayChain
  , gatherDayChainRec
  -- * Nonempty Chain
  , DayChain1
  , runCoDayChain1
  , runContraDayChain1
  , assembleDayChain1
  , assembleDayChain1Rec
  , gatherDayChain1
  , gatherDayChain1Rec
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Functor.Apply
import           Data.Functor.Combinator.Unsafe
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.HBifunctor
import           Data.HBifunctor.Associative hiding   (assoc)
import           Data.HBifunctor.Tensor hiding        (elim1, elim2, intro1, intro2)
import           Data.HFunctor
import           Data.HFunctor.Chain
import           Data.Kind
import           Data.Proxy
import           Data.SOP
import qualified Data.Bifunctor.Assoc                 as B
import qualified Data.Bifunctor.Swap                  as B
import qualified Data.Functor.Contravariant.Day       as CD
import qualified Data.Functor.Day                     as D
import qualified Data.HBifunctor.Tensor               as T
import qualified Data.Vinyl                           as V
import qualified Data.Vinyl.Functor                   as V

-- | A pairing of invariant functors to create a new invariant functor that
-- represents the "combination" between the two.
--
-- A @'Day' f g a@ is a invariant "consumer" and "producer" of @a@, and
-- it does this by taking the @a@ and feeding it to both @f@ and @g@, and
-- aggregating back the results.
--
-- For example, if we have @x :: f a@ and @y :: g b@, then @'day' x y ::
-- 'Day' f g (a, b)@.  This is a consumer/producer of @(a, b)@s, and it
-- feeds the @a@ to @x@ and the @b@ to @y@, and tuples the results back
-- together.
--
-- Mathematically, this is a invariant day convolution along a tuple.
data Day :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Day :: f b
        -> g c
        -> (a -> (b, c))
        -> (b -> c -> a)
        -> Day f g a

-- | Pair two invariant actions together in a way that tuples together
-- their input/outputs.  The first one will take the 'fst' part of the
-- tuple, and the second one will take the 'snd' part of the tuple.
day :: f a -> g b -> Day f g (a, b)
day x y = Day x y id (,)

-- | Interpret the covariant part of a 'Day' into a target context @h@,
-- as long as the context is an instance of 'Apply'.  The 'Apply' is used to
-- combine results back together using '<*>'.
runDayApply
    :: forall f g h. Apply h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayApply f g (Day x y _ j) = liftF2 j (f x) (g y)

-- | Interpret the contravariant part of a 'Day' into a target context
-- @h@, as long as the context is an instance of 'Divise'.  The 'Divise' is
-- used to split up the input to pass to each of the actions.
runDayDivise
    :: forall f g h. Divise h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayDivise f g (Day x y h _) = divise h (f x) (g y)

-- | Convert an invariant 'Day' into the covariant version, dropping the
-- contravariant part.
toCoDay :: Day f g ~> D.Day f g
toCoDay (Day x y _ g) = D.Day x y g

-- | Convert an invariant 'Day' into the contravariant version, dropping
-- the covariant part.
toContraDay :: Day f g ~> CD.Day f g
toContraDay (Day x y f _) = CD.Day x y f

-- | 'Day' is associative.
assoc :: Day f (Day g h) ~> Day (Day f g) h
assoc (Day x (Day y z f g) h j) =
    Day (Day x y id (,)) z
      (B.unassoc . second f . h)
      (\(a,b) c -> j a (g b c))

-- | 'Day' is associative.
unassoc :: Day (Day f g) h ~> Day f (Day g h)
unassoc (Day (Day x y f g) z h j) =
    Day x (Day y z id (,))
      (B.assoc . first f . h)
      (\a (b, c) -> j (g a b) c)

-- | The left identity of 'Day' is 'Identity'; this is one side of that
-- isomorphism.
intro1 :: g ~> Day Identity g
intro1 y = Day (Identity ()) y ((),) (const id)

-- | The right identity of 'Day' is 'Identity'; this is one side of that
-- isomorphism.
intro2 :: f ~> Day f Identity
intro2 x = Day x (Identity ()) (,()) const

-- | The left identity of 'Day' is 'Identity'; this is one side of that
-- isomorphism.
elim1 :: Invariant g => Day Identity g ~> g
elim1 (Day (Identity x) y f g) = invmap (g x) (snd . f) y

-- | The right identity of 'Day' is 'Identity'; this is one side of that
-- isomorphism.
elim2 :: Invariant f => Day f Identity ~> f
elim2 (Day x (Identity y) f g) = invmap (`g` y) (fst . f) x

-- | The two sides of a 'Day' can be swapped.
swapped :: Day f g ~> Day g f
swapped (Day x y f g) = Day y x (B.swap . f) (flip g)

-- | Hoist a function over the left side of a 'Day'.
trans1 :: f ~> h -> Day f g ~> Day h g
trans1 f (Day x y g h) = Day (f x) y g h

-- | Hoist a function over the right side of a 'Day'.
trans2 :: g ~> h -> Day f g ~> Day f h
trans2 f (Day x y g h) = Day x (f y) g h

-- | In the covariant direction, we can interpret out of a 'Chain1' of 'Day'
-- into any 'Apply'.
runCoDayChain1
    :: forall f g. Apply g
    => f ~> g
    -> DayChain1 f ~> g
runCoDayChain1 f = foldChain1 f (runDayApply f id)

-- | In the contravariant direction, we can interpret out of a 'Chain1' of
-- 'Day' into any 'Divise'.
runContraDayChain1
    :: forall f g. Divise g
    => f ~> g
    -> DayChain1 f ~> g
runContraDayChain1 f = foldChain1 f (runDayDivise f id)

-- | In the covariant direction, we can interpret out of a 'Chain' of 'Day'
-- into any 'Applicative'.
runCoDayChain
    :: forall f g. Applicative g
    => f ~> g
    -> DayChain f ~> g
runCoDayChain f = unsafeApply (Proxy @g) $
    foldChain (pure . runIdentity) (runDayApply f id)

-- | In the contravariant direction, we can interpret out of a 'Chain' of
-- 'Day' into any 'Divisible'.
runContraDayChain
    :: forall f g. Divisible g
    => f ~> g
    -> DayChain f ~> g
runContraDayChain f = unsafeDivise (Proxy @g) $
    foldChain (const conquer) (runDayDivise f id)

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
type DayChain  = Chain Day Identity

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
type DayChain1 = Chain1 Day

instance Invariant (Day f g) where
    invmap f g (Day x y h j) = Day x y (h . g) (\q -> f . j q)

instance HFunctor (Day f) where
    hmap f = hbimap id f

instance HBifunctor Day where
    hbimap f g (Day x y h j) = Day (f x) (g y) h j

instance Associative Day where
    type NonEmptyBy Day = DayChain1
    type FunctorBy Day = Invariant
    associating = isoF assoc unassoc

    appendNE (Day xs ys f g) = case xs of
      Done1 x              -> More1 (Day x ys f g)
      More1 (Day z zs h j) -> More1 $
        Day z (appendNE (Day zs ys id (,)))
          (B.assoc . first h . f)
          (\a (b, c) -> g (j a b) c)
    matchNE = matchChain1

    consNE = More1
    toNonEmptyBy = More1 . hright Done1

instance Tensor Day Identity where
    type ListBy Day = DayChain

    intro1 = intro2
    intro2 = intro1
    elim1 = elim2
    elim2 = elim1

    appendLB = appendChain
    splitNE = splitChain1
    splittingLB = splittingChain

    toListBy = More . hright inject

-- | Convenient wrapper to build up a 'DayChain' on by providing each
-- component of it.  This makes it much easier to build up longer chains
-- because you would only need to write the splitting/joining functions in
-- one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MT Int Bool String
-- @
--
-- and an invariant functor @Prim@ (representing, say, a bidirectional
-- parser, where @Prim Int@ is a bidirectional parser for an 'Int'@),
-- then you could assemble a bidirectional parser for a 'MyType' using:
--
-- @
-- invmap (\(MyType x y z) -> I x :* I y :* I z :* Nil)
--        (\(I x :* I y :* I z :* Nil) -> MyType x y z) $
--   assembleDayChain $ intPrim
--                   :* boolPrim
--                   :* stringPrim
--                   :* Nil
-- @
--
-- This is much more convenient than doing it using manual applications of
-- 'divide' or 'divise' or 'Day', which would require manually peeling off
-- tuples one-by-one.
assembleDayChain
    :: NP f as
    -> DayChain f (NP I as)
assembleDayChain = \case
    Nil     -> Done $ Identity Nil
    x :* xs -> More $ Day
      x
      (assembleDayChain xs)
      unconsNPI
      consNPI

-- | A version of 'assembleDayChain' where each component is itself
-- a 'DayChain'.
--
-- @
-- assembleDayChain (x :* y :* z :* Nil)
--   = gatherDayChain (injectChain x :* injectChain y :* injectChain z :* Nil)
-- @
gatherDayChain
    :: NP (DayChain f) as
    -> DayChain f (NP I as)
gatherDayChain = \case
    Nil     -> Done $ Identity Nil
    x :* xs -> appendChain $ Day
      x
      (gatherDayChain xs)
      unconsNPI
      consNPI

-- | A version of 'assembleDayChain' but for 'DayChain1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Divise' or 'Apply' instance, but no 'Divisible' or 'Applicative'.
assembleDayChain1
    :: Invariant f
    => NP f (a ': as)
    -> DayChain1 f (NP I (a ': as))
assembleDayChain1 = \case
    x :* xs -> case xs of
      Nil    -> Done1 $ invmap ((:* Nil) . I) (unI . hd) x
      _ :* _ -> More1 $ Day
        x
        (assembleDayChain1 xs)
        unconsNPI
        consNPI

-- | A version of 'gatherDayChain' but for 'DayChain1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Divise' or 'Apply' instance, but no 'Divisible' or 'Applicative'.
gatherDayChain1
    :: Invariant f
    => NP (DayChain1 f) (a ': as)
    -> DayChain1 f (NP I (a ': as))
gatherDayChain1 = \case
    x :* xs -> case xs of
      Nil    -> invmap ((:* Nil) . I) (unI . hd) x
      _ :* _ -> appendChain1 $ Day
        x
        (gatherDayChain1 xs)
        unconsNPI
        consNPI

unconsNPI :: NP I (a ': as) -> (a, NP I as)
unconsNPI (I y :* ys) = (y, ys)

consNPI :: a -> NP I as -> NP I (a ': as)
consNPI y ys = I y :* ys

-- | A version of 'assembleDayChain' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @
-- data MyType = MT Int Bool String
--
-- invmap (\(MyType x y z) -> x ::& y ::& z ::& RNil)
--        (\(x ::& y ::& z ::& RNil) -> MyType x y z) $
--   assembleDayChain $ intPrim
--                   :& boolPrim
--                   :& stringPrim
--                   :& Nil
-- @
assembleDayChainRec
    :: V.Rec f as
    -> DayChain f (V.XRec V.Identity as)
assembleDayChainRec = \case
    V.RNil    -> Done $ Identity V.RNil
    x V.:& xs -> More $ Day
      x
      (assembleDayChainRec xs)
      unconsRec
      (V.::&)

-- | A version of 'gatherDayChain' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
gatherDayChainRec
    :: V.Rec (DayChain f) as
    -> DayChain f (V.XRec V.Identity as)
gatherDayChainRec = \case
    V.RNil    -> Done $ Identity V.RNil
    x V.:& xs -> appendChain $ Day
      x
      (gatherDayChainRec xs)
      unconsRec
      (V.::&)

-- | A version of 'assembleDayChain1' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
assembleDayChain1Rec
    :: Invariant f
    => V.Rec f (a ': as)
    -> DayChain1 f (V.XRec V.Identity (a ': as))
assembleDayChain1Rec = \case
    x V.:& xs -> case xs of
      V.RNil   -> Done1 $ invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
      _ V.:& _ -> More1 $ Day
        x
        (assembleDayChain1Rec xs)
        unconsRec
        (V.::&)

-- | A version of 'gatherDayChain1' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
gatherDayChain1Rec
    :: Invariant f
    => V.Rec (DayChain1 f) (a ': as)
    -> DayChain1 f (V.XRec V.Identity (a ': as))
gatherDayChain1Rec = \case
    x V.:& xs -> case xs of
      V.RNil   -> invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
      _ V.:& _ -> appendChain1 $ Day
        x
        (gatherDayChain1Rec xs)
        unconsRec
        (V.::&)

unconsRec :: V.XRec V.Identity (a ': as) -> (a, V.XRec V.Identity as)
unconsRec (y V.::& ys) = (y, ys)
