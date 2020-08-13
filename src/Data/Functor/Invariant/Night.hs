
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
  , Not(..), refuted
  , night
  , runNightAlt
  , runNightDecide
  , toCoNight
  , toCoNight_
  , toContraNight
  , assoc, unassoc
  , intro1, intro2
  , elim1, elim2
  , swapped
  , trans1, trans2
  ) where

import           Control.Natural
import           Data.Bifunctor
import           Data.Functor.Alt
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Night  (Not(..), refuted)
import           Data.Functor.Invariant
import           Data.Kind
import           Data.Void
import           GHC.Generics
import qualified Data.Bifunctor.Assoc              as B
import qualified Data.Bifunctor.Swap               as B
import qualified Data.Functor.Contravariant.Night  as CN
import qualified Data.Functor.Coyoneda             as CY

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

instance Invariant (Night f g) where
    invmap f g (Night x y h j k) = Night x y (h . g) (f . j) (f . k)

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

-- | Convert an invariant 'Night' into the covariant version, dropping the
-- contravariant part.
--
-- This version does not require a 'Functor' constraint because it converts
-- to the coyoneda-wrapped product, which is more accurately the covariant
-- 'Night' convolution.
--
-- @since 0.3.2.0
toCoNight_ :: Night f g ~> CY.Coyoneda f :*: CY.Coyoneda g
toCoNight_ (Night x y _ f g) = CY.Coyoneda f x :*: CY.Coyoneda g y


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
intro1 y = Night refuted y Right absurd id

-- | The right identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
intro2 :: f ~> Night f Not
intro2 x = Night x refuted Left id absurd

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

