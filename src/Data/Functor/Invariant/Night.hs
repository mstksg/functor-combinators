
-- |
-- Module      : Data.Functor.Invariant.Night
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides an 'Invariant' version of a Day convolution over 'Either'.
--
-- @since 0.3.0.0
module Data.Functor.Invariant.Night (
    Night(..)
  , Not(..)
  , night
  , runNightAlt
  , runNightDecide
  , toCoNight
  , toContraNight
  , assoc, unassoc
  , intro1, intro2
  , elim1, elim2
  , swapped
  , trans1, trans2
  -- * Chain
  , NightChain
  , pattern Share, pattern Reject
  , runCoNightChain
  , runContraNightChain
  , assembleNightChain
  , concatNightChain
  -- * Nonempty Chain
  , NightChain1
  , pattern NightChain1
  , runCoNightChain1
  , runContraNightChain1
  , assembleNightChain1
  , concatNightChain1
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Functor.Alt
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Night    (Not(..))
import           Data.Functor.Invariant
import           Data.Functor.Plus
import           Data.HBifunctor
import           Data.HBifunctor.Associative hiding  (assoc)
import           Data.HBifunctor.Tensor hiding       (elim1, elim2, intro1, intro2)
import           Data.HFunctor
import           Data.HFunctor.Chain
import           Data.Kind
import           Data.SOP
import           Data.Void
import           GHC.Generics
import qualified Data.Bifunctor.Assoc                as B
import qualified Data.Bifunctor.Swap                 as B
import qualified Data.Functor.Contravariant.Night    as CN
import qualified Data.HBifunctor.Tensor              as T

-- | A pairing of invariant functors to create a new invariant functor that
-- represents the "choice" between the two.
--
-- A @'Night' f g a@ is a invariant "consumer" and "producer" of @a@, and
-- it does this by either feeding the @a@ to @f@, or feeding the @a@ to
-- @g@, and then collecting the result from whichever one it was fed to.
-- Which decision of which path to takes happens at runtime depending
-- /what/ @a@ is actually given.
--
-- For example, if we have @x :: f a@ and @y :: g b@, then @'night' x y ::
-- 'Night' f g ('Either' a b)@.  This is a consumer/producer of @'Either' a b@s, and
-- it consumes 'Left' branches by feeding it to @x@, and 'Right' branches
-- by feeding it to @y@.  It then passes back the single result from the one of
-- the two that was chosen.
--
-- Mathematically, this is a invariant day convolution, except with
-- a different choice of bifunctor ('Either') than the typical one we talk
-- about in Haskell (which uses @(,)@).  Therefore, it is an alternative to
-- the typical 'Data.Functor.Day' convolution --- hence, the name 'Night'.
data Night :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Night :: f b
          -> g c
          -> (a -> Either b c)
          -> (b -> a)
          -> (c -> a)
          -> Night f g a

-- | Pair two invariant actions together into a 'Night'; assigns the first
-- one to 'Left' inputs and outputs and the second one to 'Right' inputs
-- and outputs.
night :: f a -> g b -> Night f g (Either a b)
night x y = Night x y id Left Right

-- | Interpret the covariant part of a 'Night' into a target context @h@,
-- as long as the context is an instance of 'Alt'.  The 'Alt' is used to
-- combine results back together, chosen by '<!>'.
runNightAlt
    :: forall f g h. Alt h
    => f ~> h
    -> g ~> h
    -> Night f g ~> h
runNightAlt f g (Night x y _ j k) = fmap j (f x) <!> fmap k (g y)

-- | Interpret the contravariant part of a 'Night' into a target context
-- @h@, as long as the context is an instance of 'Decide'.  The 'Decide' is
-- used to pick which part to feed the input to.
runNightDecide
    :: forall f g h. Decide h
    => f ~> h
    -> g ~> h
    -> Night f g ~> h
runNightDecide f g (Night x y h _ _) = decide h (f x) (g y)

-- | Convert an invariant 'Night' into the covariant version, dropping the
-- contravariant part.
--
-- Note that there is no covariant version of 'Night' defined in any common
-- library, so we use an equivalent type (if @f@ and @g@ are 'Functor's) @f
-- ':*:' g@.
toCoNight :: (Functor f, Functor g) => Night f g ~> f :*: g
toCoNight (Night x y _ f g) = fmap f x :*: fmap g y

-- | Convert an invariant 'Night' into the contravariant version, dropping
-- the covariant part.
toContraNight :: Night f g ~> CN.Night f g
toContraNight (Night x y f _ _) = CN.Night x y f

-- | 'Night' is associative.
assoc :: Night f (Night g h) ~> Night (Night f g) h
assoc (Night x (Night y z f g h) j k l) =
    Night (Night x y id Left Right) z
      (B.unassoc . second f . j)
      (either k (l . g))
      (l . h)

-- | 'Night' is associative.
unassoc :: Night (Night f g) h ~> Night f (Night g h)
unassoc (Night (Night x y f g h) z j k l) =
    Night x (Night y z id Left Right)
      (B.assoc . first f . j)
      (k . g)
      (either (k . h) l)

-- | The left identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
intro1 :: g ~> Night Not g
intro1 y = Night (Not id) y Right absurd id

-- | The right identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
intro2 :: f ~> Night f Not
intro2 x = Night x (Not id) Left id absurd

-- | The left identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
elim1 :: Invariant g => Night Not g ~> g
elim1 (Night x y f _ h) = invmap h (either (absurd . refute x) id . f) y

-- | The right identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
elim2 :: Invariant f => Night f Not ~> f
elim2 (Night x y f g _) = invmap g (either id (absurd . refute y) . f) x

-- | The two sides of a 'Night' can be swapped.
swapped :: Night f g ~> Night g f
swapped (Night x y f g h) = Night y x (B.swap . f) h g

-- | Hoist a function over the left side of a 'Night'.
trans1 :: f ~> h -> Night f g ~> Night h g
trans1 f (Night x y g h j) = Night (f x) y g h j

-- | Hoist a function over the right side of a 'Night'.
trans2 :: g ~> h -> Night f g ~> Night f h
trans2 f (Night x y g h j) = Night x (f y) g h j

-- | In the covariant direction, we can interpret out of a 'Chain1' of 'Night'
-- into any 'Alt'.
runCoNightChain1
    :: forall f g. Alt g
    => f ~> g
    -> NightChain1 f ~> g
runCoNightChain1 f = foldChain1 f (runNightAlt f id)

-- | In the contravariant direction, we can interpret out of a 'Chain1' of
-- 'Night' into any 'Decide'.
runContraNightChain1
    :: forall f g. Decide g
    => f ~> g
    -> NightChain1 f ~> g
runContraNightChain1 f = foldChain1 f (runNightDecide f id)

-- | In the covariant direction, we can interpret out of a 'Chain' of 'Night'
-- into any 'Plus'.
runCoNightChain
    :: forall f g. Plus g
    => f ~> g
    -> NightChain f ~> g
runCoNightChain f = foldChain (const zero) (runNightAlt f id)

-- | In the contravariant direction, we can interpret out of a 'Chain' of
-- 'Night' into any 'Conclude'.
runContraNightChain
    :: forall f g. Conclude g
    => f ~> g
    -> NightChain f ~> g
runContraNightChain f = foldChain (conclude . refute) (runNightDecide f id)

-- | Instead of defining yet another separate free monoid like
-- 'Control.Applicative.Free.Ap',
-- 'Data.Functor.Contravariant.Divisible.Free.Div', or
-- 'Data.Functor.Contravariant.Divisible.Free.Dec', we re-use 'Chain'.
--
-- You can assemble values using the combinators in "Data.HFunctor.Chain",
-- and then tear them down/interpret them using 'runCoNightChain' and
-- 'runContraNightChain'.  There is no general invariant interpreter (and so no
-- 'MonoidIn' instance for 'Night') because the typeclasses used to express
-- the target contexts are probably not worth defining given how little the
-- Haskell ecosystem uses invariant functors as an abstraction.
type NightChain  = Chain Night Not

-- | Instead of defining yet another separate free semigroup like
-- 'Data.Functor.Apply.Free.Ap1',
-- 'Data.Functor.Contravariant.Divisible.Free.Div1', or
-- 'Data.Functor.Contravariant.Divisible.Free.Dec1', we re-use 'Chain1'.
--
-- You can assemble values using the combinators in "Data.HFunctor.Chain",
-- and then tear them down/interpret them using 'runCoNightChain1' and
-- 'runContraNightChain1'.  There is no general invariant interpreter (and so no
-- 'SemigroupIn' instance for 'Night') because the typeclasses used to
-- express the target contexts are probably not worth defining given how
-- little the Haskell ecosystem uses invariant functors as an abstraction.
type NightChain1 = Chain1 Night

-- | Match on a non-empty 'NightChain'; contains no @f@s, but only the
-- terminal value.  Analogous to the
-- 'Data.Functor.Contravariant.Divisible.Free.Choose' constructor.
pattern Share :: (a -> Either b c) -> (b -> a) -> (c -> a) -> f b -> NightChain f c -> NightChain f a
pattern Share f g h x xs = More (Night x xs f g h)

-- | Match on an "empty" 'NightChain'; contains no @f@s, but only the
-- terminal value.  Analogous to the
-- 'Data.Functor.Contravariant.Divisible.Free.Lose' constructor.
pattern Reject :: (a -> Void) -> NightChain f a
pattern Reject x = Done (Not x)
{-# COMPLETE Share, Reject #-}

-- | Match on a 'NightChain1' to get the head and the rest of the items.
-- Analogous to the 'Data.Functor.Contravariant.Divisible.Free.Dec1'
-- constructor.
pattern NightChain1 :: Invariant f => (a -> Either b c) -> (b -> a) -> (c -> a) -> f b -> NightChain f c -> NightChain1 f a
pattern NightChain1 f g h x xs <- (splitChain1->Night x xs f g h)
  where
    NightChain1 f g h x xs = unsplitNE $ Night x xs f g h
{-# COMPLETE NightChain1 #-}

instance Invariant (Night f g) where
    invmap f g (Night x y h j k) = Night x y (h . g) (f . j) (f . k)

instance HFunctor (Night f) where
    hmap f = hbimap id f

instance HBifunctor Night where
    hbimap f g (Night x y h j k) = Night (f x) (g y) h j k

instance Associative Night where
    type NonEmptyBy Night = NightChain1
    type FunctorBy Night = Invariant
    associating = isoF assoc unassoc

    appendNE (Night xs ys f g h) = case xs of
      Done1 x                  -> More1 (Night x ys f g h)
      More1 (Night z zs j k l) -> More1 $
        Night z (appendNE (Night zs ys id Left Right))
          (B.assoc . first j . f)
          (g . k)
          (either (g . l) h)
    matchNE = matchChain1

    consNE = More1
    toNonEmptyBy = chain1Pair

instance Tensor Night Not where
    type ListBy Night = NightChain

    intro1 = intro2
    intro2 = intro1
    elim1 = elim2
    elim2 = elim1

    appendLB = appendChain
    splitNE = splitChain1
    splittingLB = splittingChain

    toListBy = chainPair

instance Matchable Night Not where
    unsplitNE (Night x xs f g h) = case xs of
      Done r  -> Done1 $ invmap g (either id (absurd . refute r) . f) x
      More ys -> More1 $ Night x (unsplitNE ys) f g h
    matchLB = \case
      Done x  -> L1 x
      More xs -> R1 $ unsplitNE xs

-- | Convenient wrapper to build up a 'NightChain' on by providing each
-- component of it.  This makes it much easier to build up longer chains
-- because you would only need to write the splitting/joining functions in
-- one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MTI Int | MTB Bool | MTS String
-- @
--
-- and an invariant functor @Prim@ (representing, say, a bidirectional
-- parser, where @Prim Int@ is a bidirectional parser for an 'Int'@),
-- then you could assemble a bidirectional parser for a @MyType@ using:
--
-- @
-- invmap (\case MTI x -> Z (I x); MTB y -> S (Z (I y)); MTS z -> S (S (Z (I z))))
--        (\case Z (I x) -> MTI x; S (Z (I y)) -> MTB y; S (S (Z (I z))) -> MTS z) $
--   assembleNightChain $ intPrim
--                     :* boolPrim
--                     :* stringPrim
--                     :* Nil
-- @
--
-- This is much more convenient than doing it using manual applications of
-- 'decide' or 'Data.Functor.Contravariant.Divisible.choose' or 'Night',
-- which would require manually peeling off eithers one-by-one.
assembleNightChain
    :: NP f as
    -> NightChain f (NS I as)
assembleNightChain = \case
    Nil     -> Done $ Not (\case {})
    x :* xs -> More $ Night
      x
      (assembleNightChain xs)
      unconsNSI
      (Z . I)
      S

-- | A version of 'assembleNightChain' where each component is itself
-- a 'NightChain'.
--
-- @
-- assembleNightChain (x :* y :* z :* Nil)
--   = concatNightChain (injectChain x :* injectChain y :* injectChain z :* Nil)
-- @
concatNightChain
    :: NP (NightChain f) as
    -> NightChain f (NS I as)
concatNightChain = \case
    Nil     -> Done $ Not (\case {})
    x :* xs -> appendChain $ Night
      x
      (concatNightChain xs)
      unconsNSI
      (Z . I)
      S

-- | A version of 'assembleNightChain' but for 'NightChain1' instead.  Can
-- be useful if you intend on interpreting it into something with only
-- a 'Decide' or 'Alt' instance, but no
-- 'Data.Functor.Contravariant.Divisible.Decidable' or 'Plus' or
-- 'Control.Applicative.Alternative'.
assembleNightChain1
    :: Invariant f
    => NP f (a ': as)
    -> NightChain1 f (NS I (a ': as))
assembleNightChain1 = \case
    x :* xs -> case xs of
      Nil    -> Done1 $ invmap (Z . I) (unI . unZ) x
      _ :* _ -> More1 $ Night
        x
        (assembleNightChain1 xs)
        unconsNSI
        (Z . I)
        S

-- | A version of 'concatNightChain' but for 'NightChain1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Decide' or 'Alt' instance, but no 'Decidable' or 'Plus' or
-- 'Control.Applicative.Alternative'.
concatNightChain1
    :: Invariant f
    => NP (NightChain1 f) (a ': as)
    -> NightChain1 f (NS I (a ': as))
concatNightChain1 = \case
    x :* xs -> case xs of
      Nil    -> invmap (Z . I) (unI . unZ) x
      _ :* _ -> appendChain1 $ Night
        x
        (concatNightChain1 xs)
        unconsNSI
        (Z . I)
        S

unconsNSI :: NS I (a ': as) -> Either a (NS I as)
unconsNSI = \case
  Z (I x) -> Left x
  S xs    -> Right xs
