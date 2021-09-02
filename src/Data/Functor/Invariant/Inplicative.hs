
module Data.Functor.Invariant.Inplicative (
    Inply(..)
  , Inplicative(..)
  ) where

import           Data.Functor.Invariant

-- | Invariantly combine two 'DivAp's.
--
-- Analogous to 'liftA2' and 'divise'.  If there was some typeclass that
-- represented semigroups on invariant 'Day', this would be the method of
-- that typeclass.
--
-- The identity of this is 'Knot'.

-- | Convenient wrapper over 'gather' that simply combines the two options
-- in a tuple.  Analogous to 'divised'.
--
-- @since 0.3.4.0

class Invariant f => Inply f where
    gather
        :: (b -> c -> a)
        -> (a -> (b, c))
        -> f b
        -> f c
        -> f a
    gather f g x y = invmap (uncurry f) g (gathered x y)
    gathered
        :: f a
        -> f b
        -> f (a, b)
    gathered = gather (,) id

    {-# MINIMAL gather | gathered #-}

class Inply f => Inplicative f where
    knot :: a -> f a


