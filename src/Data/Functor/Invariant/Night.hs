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
  Night (..),
  Not (..),
  refuted,
  night,
  runNight,
  nerve,
  runNightAlt,
  runNightDecide,
  toCoNight,
  toCoNight_,
  toContraNight,
  assoc,
  unassoc,
  intro1,
  intro2,
  elim1,
  elim2,
  swapped,
  trans1,
  trans2,
) where

import Control.Natural
import Data.Bifunctor
import qualified Data.Bifunctor.Assoc as B
import qualified Data.Bifunctor.Swap as B
import Data.Functor.Alt
import Data.Functor.Contravariant.Decide
import Data.Functor.Contravariant.Night (Not (..), refuted)
import qualified Data.Functor.Contravariant.Night as CN
import qualified Data.Functor.Coyoneda as CY
import Data.Functor.Invariant
import Data.Functor.Invariant.Internative
import Data.Kind
import Data.Void
import GHC.Generics

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
  Night ::
    f b ->
    g c ->
    (b -> a) ->
    (c -> a) ->
    (a -> Either b c) ->
    Night f g a

instance Invariant (Night f g) where
  invmap f g (Night x y h j k) = Night x y (f . h) (f . j) (k . g)

-- | Pair two invariant actions together into a 'Night'; assigns the first
-- one to 'Left' inputs and outputs and the second one to 'Right' inputs
-- and outputs.
night :: f a -> g b -> Night f g (Either a b)
night x y = Night x y Left Right id

-- | Interpret the covariant part of a 'Night' into a target context @h@,
-- as long as the context is an instance of 'Alt'.  The 'Alt' is used to
-- combine results back together, chosen by '<!>'.
runNightAlt ::
  forall f g h.
  Alt h =>
  f ~> h ->
  g ~> h ->
  Night f g ~> h
runNightAlt f g (Night x y h j _) = fmap h (f x) <!> fmap j (g y)

-- | Interpret the contravariant part of a 'Night' into a target context
-- @h@, as long as the context is an instance of 'Decide'.  The 'Decide' is
-- used to pick which part to feed the input to.
runNightDecide ::
  forall f g h.
  Decide h =>
  f ~> h ->
  g ~> h ->
  Night f g ~> h
runNightDecide f g (Night x y _ _ k) = decide k (f x) (g y)

-- | Convert an invariant 'Night' into the covariant version, dropping the
-- contravariant part.
--
-- Note that there is no covariant version of 'Night' defined in any common
-- library, so we use an equivalent type (if @f@ and @g@ are 'Functor's) @f
-- ':*:' g@.
toCoNight :: (Functor f, Functor g) => Night f g ~> f :*: g
toCoNight (Night x y f g _) = fmap f x :*: fmap g y

-- | Convert an invariant 'Night' into the covariant version, dropping the
-- contravariant part.
--
-- This version does not require a 'Functor' constraint because it converts
-- to the coyoneda-wrapped product, which is more accurately the covariant
-- 'Night' convolution.
--
-- @since 0.3.2.0
toCoNight_ :: Night f g ~> CY.Coyoneda f :*: CY.Coyoneda g
toCoNight_ (Night x y f g _) = CY.Coyoneda f x :*: CY.Coyoneda g y

-- | Convert an invariant 'Night' into the contravariant version, dropping
-- the covariant part.
toContraNight :: Night f g ~> CN.Night f g
toContraNight (Night x y _ _ h) = CN.Night x y h

-- | Interpret out of a 'Night' into any instance of 'Inalt' by providing
-- two interpreting functions.
--
-- @since 0.4.0.0
runNight ::
  Inalt h =>
  (f ~> h) ->
  (g ~> h) ->
  Night f g ~> h
runNight f g (Night x y a b c) = swerve a b c (f x) (g y)

-- | Squash the two items in a 'Night' using their natural 'Inalt'
-- instances.
--
-- @since 0.4.0.0
nerve ::
  Inalt f =>
  Night f f ~> f
nerve (Night x y a b c) = swerve a b c x y

-- | 'Night' is associative.
assoc :: Night f (Night g h) ~> Night (Night f g) h
assoc (Night x (Night y z f g h) j k l) =
  Night
    (Night x y Left Right id)
    z
    (either j (k . f))
    (k . g)
    (B.unassoc . second h . l)

-- | 'Night' is associative.
unassoc :: Night (Night f g) h ~> Night f (Night g h)
unassoc (Night (Night x y f g h) z j k l) =
  Night
    x
    (Night y z Left Right id)
    (j . f)
    (either (j . g) k)
    (B.assoc . first h . l)

-- (k . g)
-- (either (k . h) l)

-- | The left identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
intro1 :: g ~> Night Not g
intro1 y = Night refuted y absurd id Right

-- | The right identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
intro2 :: f ~> Night f Not
intro2 x = Night x refuted id absurd Left

-- | The left identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
elim1 :: Invariant g => Night Not g ~> g
elim1 (Night x y _ g h) = invmap g (either (absurd . refute x) id . h) y

-- | The right identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
elim2 :: Invariant f => Night f Not ~> f
elim2 (Night x y f _ h) = invmap f (either id (absurd . refute y) . h) x

-- | The two sides of a 'Night' can be swapped.
swapped :: Night f g ~> Night g f
swapped (Night x y f g h) = Night y x g f (B.swap . h)

-- | Hoist a function over the left side of a 'Night'.
trans1 :: f ~> h -> Night f g ~> Night h g
trans1 f (Night x y g h j) = Night (f x) y g h j

-- | Hoist a function over the right side of a 'Night'.
trans2 :: g ~> h -> Night f g ~> Night f h
trans2 f (Night x y g h j) = Night x (f y) g h j
