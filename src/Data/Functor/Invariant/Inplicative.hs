-- |
-- Module      : Data.Functor.Invariant.Inplicative
-- Copyright   : (c) Justin Le 2021
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Contains the classes 'Inply' and 'Inplicative', the invariant
-- counterparts to 'Apply'/'Divise' and 'Applicative'/'Divisible'.
--
-- @since 0.4.0.0
module Data.Functor.Invariant.Inplicative (
  -- * Typeclass
    Inply(..)
  , Inplicative(..)
  -- * Invariant 'Day'
  , runDay
  , dather
  -- * Assembling Helpers
  , concatInplicative
  , concatInply
  , concatInplicativeRec
  , concatInplyRec
  ) where

import           Control.Natural
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Day
import           Data.SOP hiding            (hmap)
import qualified Data.Vinyl                 as V
import qualified Data.Vinyl.Functor         as V

-- | The invariant counterpart of 'Apply' and 'Divise'.
--
-- Conceptually you can think of 'Apply' as, given a way to "combine" @a@ and
-- @b@ to @c@, lets you merge @f a@ (producer of @a@) and @f b@ (producer
-- of @b@) into a @f c@ (producer of @c@).  'Divise' can be thought of as,
-- given a way to "split" a @c@ into an @a@ and a @b@, lets you merge @f
-- a@ (consumer of @a@) and @f b@ (consumder of @b@) into a @f c@ (consumer
-- of @c@).
--
-- 'Inply', for 'gather', requires both a combining function and
-- a splitting function in order to merge @f b@ (producer and consumer of
-- @b@) and @f c@ (producer and consumer of @c@) into a @f a@.  You can
-- think of it as, for the @f a@, it "splits" the a into @b@ and @c@ with
-- the @a -> (b, c)@, feeds it to the original @f b@ and @f c@, and then
-- re-combines the output back into a @a@ with the @b -> c -> a@.
--
-- @since 0.4.0.0
class Invariant f => Inply f where
    -- | Like '<.>', '<*>', 'divise', or 'divide', but requires both
    -- a splitting and a recombining function.  '<.>' and '<*>' require
    -- only a combining function, and 'divise' and 'divide' require only
    -- a splitting function.
    --
    -- It is used to merge @f b@ (producer and consumer of @b@) and @f c@
    -- (producer and consumer of @c@) into a @f a@.  You can think of it
    -- as, for the @f a@, it "splits" the a into @b@ and @c@ with the @a ->
    -- (b, c)@, feeds it to the original @f b@ and @f c@, and then
    -- re-combines the output back into a @a@ with the @b -> c -> a@.
    --
    -- An important property is that it will always use @both@ of the
    -- ccomponents given in order to fulfil its job.  If you gather an @f
    -- a@ and an @f b@ into an @f c@, in order to consume/produdce the @c@,
    -- it will always use both the @f a@ or the @f b@ -- exactly one of
    -- them.
    --
    -- @since 0.4.0.0
    gather
        :: (b -> c -> a)
        -> (a -> (b, c))
        -> f b
        -> f c
        -> f a
    gather f g x y = invmap (uncurry f) g (gathered x y)
    -- | A simplified version of 'gather' that combines into a tuple.  You
    -- can then use 'invmap' to reshape it into the proper shape.
    --
    -- @since 0.4.0.0
    gathered
        :: f a
        -> f b
        -> f (a, b)
    gathered = gather (,) id

    {-# MINIMAL gather | gathered #-}

-- | The invariant counterpart of 'Applicative' and 'Divisible'.
--
-- The main important action is described in 'Inply', but this adds 'knot',
-- which is the counterpart to 'pure' and 'conquer'.  It's the identity to
-- 'gather'; if combine two @f a@s with 'gather', and one of them is
-- 'knot', it will leave the structure unchanged.
--
-- Conceptually, if you think of 'gather' as "splitting and re-combining"
-- along multiple forks, then 'knot' introduces a fork that is never taken.
--
-- @since 0.4.0.0
class Inply f => Inplicative f where
    knot :: a -> f a

-- | Interpret out of a contravariant 'Day' into any instance of 'Inply' by
-- providing two interpreting functions.
--
-- This should go in "Data.Functor.Invariant.Day", but that module is in
-- a different package.
--
-- @since 0.4.0.0
runDay
    :: Inply h
    => (f ~> h)
    -> (g ~> h)
    -> Day f g ~> h
runDay f g (Day x y a b) = gather a b (f x) (g y)

-- | Squash the two items in a 'Day' using their natural 'Inply'
-- instances.
--
-- This should go in "Data.Functor.Invariant.Day", but that module is in
-- a different package.
--
-- @since 0.4.0.0
dather
    :: Inply f
    => Day f f ~> f
dather (Day x y a b) = gather a b x y

-- | Convenient wrapper to build up an 'Inplicative' instance by providing
-- each component of it.  This makes it much easier to build up longer
-- chains because you would only need to write the splitting/joining
-- functions in one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MT Int Bool String
-- @
--
-- and an invariant functor and 'Inplicative' instance @Prim@
-- (representing, say, a bidirectional parser, where @Prim Int@ is
-- a bidirectional parser for an 'Int'@), then you could assemble
-- a bidirectional parser for a @MyType@ using:
--
-- @
-- invmap (\(MyType x y z) -> I x :* I y :* I z :* Nil)
--        (\(I x :* I y :* I z :* Nil) -> MyType x y z) $
--   concatInplicative $ intPrim
--                    :* boolPrim
--                    :* stringPrim
--                    :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'knot' directly.
-- *    If you have 1 component, use 'inject' directly.
-- *    If you have 2 components, use 'gather' directly.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off tuples one-by-one.
--
-- @since 0.4.0.0
concatInplicative
    :: Inplicative f
    => NP f as
    -> f (NP I as)
concatInplicative = \case
    Nil     -> knot Nil
    x :* xs -> gather
      (\y ys -> I y :* ys)
      (\case I y :* ys -> (y, ys))
      x
      (concatInplicative xs)

-- | A version of 'concatInplicative' for non-empty 'NP', but only
-- requiring an 'Inply' instance.
--
-- @since 0.4.0.0
concatInply
    :: Inply f
    => NP f (a ': as)
    -> f (NP I (a ': as))
concatInply (x :* xs) = case xs of
    Nil    -> invmap ((:* Nil) . I) (\case I y :* _ -> y) x
    _ :* _ -> gather
      (\y ys -> I y :* ys)
      (\case I y :* ys -> (y, ys))
      x
      (concatInply xs)

-- | A version of 'concatInplicative' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @since 0.4.0.0
concatInplicativeRec
    :: Inplicative f
    => V.Rec f as
    -> f (V.XRec V.Identity as)
concatInplicativeRec = \case
    V.RNil    -> knot V.RNil
    x V.:& xs -> gather
      (V.::&)
      (\case y V.::& ys -> (y, ys))
      x
      (concatInplicativeRec xs)

-- | A version of 'concatInply' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @since 0.4.0.0
concatInplyRec
    :: Inply f
    => V.Rec f (a ': as)
    -> f (V.XRec V.Identity (a ': as))
concatInplyRec (x V.:& xs) = case xs of
    V.RNil   -> invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
    _ V.:& _ -> gather
      (V.::&)
      (\case y V.::& ys -> (y, ys))
      x
      (concatInplyRec xs)
