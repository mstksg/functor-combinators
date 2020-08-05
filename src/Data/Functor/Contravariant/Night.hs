
-- |
-- Module      : Data.Functor.Contravariant.Night
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides 'Night', a form of the day convolution that is contravariant
-- and splits on 'Either'.
--
-- @since 0.3.0.0
module Data.Functor.Contravariant.Night (
    Night(..)
  , night
  , runNight
  , assoc, unassoc
  , swapped
  , trans1, trans2
  , intro1, intro2
  , elim1, elim2
  , Not(..)
  ) where

import           Control.Natural
import           Data.Bifunctor
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Invariant
import           Data.Kind
import           Data.Void
import qualified Data.Bifunctor.Assoc              as B
import qualified Data.Bifunctor.Swap               as B

-- | A pairing of contravariant functors to create a new contravariant
-- functor that represents the "choice" between the two.
--
-- A @'Night' f g a@ is a contravariant "consumer" of @a@, and it does this
-- by either feeding the @a@ to @f@, or feeding the @a@ to @g@.  Which one
-- it gives it to happens at runtime depending /what/ @a@ is actually
-- given.
--
-- For example, if we have @x :: f a@ (a consumer of @a@s) and @y :: g b@
-- (a consumer of @b@s), then @'night' x y :: 'Night' f g ('Either' a b)@.
-- This is a consumer of @'Either' a b@s, and it consumes 'Left' branches
-- by feeding it to @x@, and 'Right' branches by feeding it to @y@.
--
-- Mathematically, this is a contravariant day convolution, except with
-- a different choice of bifunctor ('Either') than the typical one we talk
-- about in Haskell (which uses @(,)@).  Therefore, it is an alternative to
-- the typical 'Data.Functor.Day' convolution --- hence, the name 'Night'.
data Night :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Night :: f b
          -> g c
          -> (a -> Either b c)
          -> Night f g a

instance Contravariant (Night f g) where
    contramap f (Night x y g) = Night x y (g . f)

instance Invariant (Night f g) where
    invmap _ f (Night x y g) = Night x y (g . f)

-- | Inject into a 'Night'.
--
-- @'night' x y@ is a consumer of @'Either' a b@; 'Left' will be passed
-- to @x@, and 'Right' will be passed to @y@.
night
    :: f a
    -> g b
    -> Night f g (Either a b)
night x y = Night x y id

-- | Interpret out of a 'Night' into any instance of 'Decide' by providing
-- two interpreting functions.
runNight
    :: Decide h
    => (f ~> h)
    -> (g ~> h)
    -> Night f g ~> h
runNight f g (Night x y z) = decide z (f x) (g y)

-- | 'Night' is associative.
assoc :: Night f (Night g h) ~> Night (Night f g) h
assoc (Night x (Night y z f) g) = Night (Night x y id) z (B.unassoc . second f . g)

-- | 'Night' is associative.
unassoc :: Night (Night f g) h ~> Night f (Night g h)
unassoc (Night (Night x y f) z g) = Night x (Night y z id) (B.assoc . first f . g)

-- | The two sides of a 'Night' can be swapped.
swapped :: Night f g ~> Night g f
swapped (Night x y f) = Night y x (B.swap . f)

-- | Hoist a function over the left side of a 'Night'.
trans1 :: f ~> h -> Night f g ~> Night h g
trans1 f (Night x y z) = Night (f x) y z

-- | Hoist a function over the right side of a 'Night'.
trans2 :: g ~> h -> Night f g ~> Night f h
trans2 f (Night x y z) = Night x (f y) z

-- | A value of type @'Not' a@ is "proof" that @a@ is uninhabited.
newtype Not a = Not { refute :: a -> Void }

instance Contravariant Not where
    contramap f (Not g) = Not (g . f)

instance Semigroup (Not a) where
    Not f <> Not g = Not (f <> g)

-- | The left identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
intro1 :: g ~> Night Not g
intro1 x = Night (Not id) x Right

-- | The right identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
intro2 :: f ~> Night f Not
intro2 x = Night x (Not id) Left

-- | The left identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
elim1 :: Contravariant g => Night Not g ~> g
elim1 (Night x y z) = contramap (either (absurd . refute x) id . z) y

-- | The right identity of 'Night' is 'Not'; this is one side of that
-- isomorphism.
elim2 :: Contravariant f => Night f Not ~> f
elim2 (Night x y z) = contramap (either id (absurd . refute y) . z) x
