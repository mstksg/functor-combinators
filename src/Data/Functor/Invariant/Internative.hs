-- |
-- Module      : Data.Functor.Invariant.Internative
-- Copyright   : (c) Justin Le 2021
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Contains the classes 'Inalt' and 'Inplus', the invariant
-- counterparts to 'Alt'/'Plus' and 'Decide'/'Conclude' and
-- 'Alternative'/'Decidable'.
--
-- @since 0.4.0.0
module Data.Functor.Invariant.Internative (
  -- * Typeclass
    Inalt(..)
  , Inplus(..)
  , Internative
  -- * Assembling Helpers
  , concatInplus
  , concatInalt
  ) where

import           Data.Functor.Invariant
import           Data.Functor.Invariant.Inplicative
import           Data.SOP hiding                    (hmap)
import           Data.Void

-- | The invariant counterpart of 'Alt' and 'Decide'.
--
-- Conceptually you can think of 'Alt' as, given a way to "inject" @a@ and
-- @b@ as @c@, lets you merge @f a@ (producer of @a@) and @f b@ (producer
-- of @b@) into a @f c@ (producer of @c@), in an "either-or" fashion.
-- 'Decide' can be thought of as, given a way to "discriminate" a @c@ as
-- either a @a@ or a @b@, lets you merge @f a@ (consumer of @a@) and @f b@
-- (consumder of @b@) into a @f c@ (consumer of @c@) in an "either-or"
-- forking fashion (split the @c@ into @a@ or @b@, and use the appropriate
-- handler).
--
-- 'Inalt', for 'swerve', requires both an injecting function and
-- a choosing function in order to merge @f b@ (producer and consumer of
-- @b@) and @f c@ (producer and consumer of @c@) into a @f a@ in an
-- either-or manner.  You can think of it as, for the @f a@, it "chooses"
-- if the @a@ is actually a @b@ or a @c@ with the @a -> 'Either' b c@,
-- feeds it to either the original @f b@ or the original @f c@, and then
-- re-injects the output back into a @a@ with the @b -> a@ or the @c -> a@.
--
-- @since 0.4.0.0
class Invariant f => Inalt f where
    -- | Like '<!>', 'decide', or 'choose', but requires both
    -- an injecting and a choosing function.
    --
    -- It is used to merge @f b@ (producer and consumer of @b@) and @f c@
    -- (producer and consumer of @c@) into a @f a@ in an either-or manner.
    -- You can think of it as, for the @f a@, it "chooses" if the @a@ is
    -- actually a @b@ or a @c@ with the @a -> 'Either' b c@, feeds it to
    -- either the original @f b@ or the original @f c@, and then re-injects
    -- the output back into a @a@ with the @b -> a@ or the @c -> a@.
    --
    -- An important property is that it will only ever use exactly @one@ of
    -- the options given in order to fulfil its job.  If you swerve an @f
    -- a@ and an @f b@ into an @f c@, in order to consume/produdce the @c@,
    -- it will only use either the @f a@ or the @f b@ -- exactly one of
    -- them.
    --
    -- @since 0.4.0.0
    swerve
        :: (b -> a)
        -> (c -> a)
        -> (a -> Either b c)
        -> f b
        -> f c
        -> f a
    swerve f g h x y = invmap (either f g) h (swerved x y)
    -- | A simplified version of 'swerive' that splits to and from an
    -- 'Either'. You can then use 'invmap' to reshape it into the proper
    -- shape.
    --
    -- @since 0.4.0.0
    swerved
        :: f a
        -> f b
        -> f (Either a b)
    swerved = swerve Left Right id
    {-# MINIMAL swerve | swerved #-}

-- | The invariant counterpart of 'Alt' and 'Conclude'.
--
-- The main important action is described in 'Inalt', but this adds 'reject',
-- which is the counterpart to 'empty' and 'conclude' and 'conquer'.  It's the identity to
-- 'swerve'; if combine two @f a@s with 'swerve', and one of them is
-- 'reject', then that banch will never be taken.
--
-- Conceptually, if you think of 'swerve' as "choosing one path and
-- re-injecting back", then 'reject' introduces a branch that is impossible
-- to take.

-- @since 0.4.0.0
class Inalt f => Inplus f where
    reject :: (a -> Void) -> f a

-- | The invariant counterpart to 'Alternative' and 'Decidable': represents
-- a combination of both 'Applicative' and 'Alt', or 'Divisible' and
-- 'Conclude'.  There are laws?

-- @since 0.4.0.0
class (Inplus f, Inplicative f) => Internative f

-- | Convenient wrapper to build up an 'Inplus' instance on by providing
-- each branch of it.  This makes it much easier to build up longer chains
-- because you would only need to write the splitting/joining functions in
-- one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MTI Int | MTB Bool | MTS String
-- @
--
-- and an invariant functor and 'Inplus' instance @Prim@ (representing, say,
-- a bidirectional parser, where @Prim Int@ is a bidirectional parser for
-- an 'Int'@), then you could assemble a bidirectional parser for
-- a @MyType@ using:
--
-- @
-- invmap (\case MTI x -> Z (I x); MTB y -> S (Z (I y)); MTS z -> S (S (Z (I z))))
--        (\case Z (I x) -> MTI x; S (Z (I y)) -> MTB y; S (S (Z (I z))) -> MTS z) $
--   concatInplus $ intPrim
--               :* boolPrim
--               :* stringPrim
--               :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'reject' directly.
-- *    If you have 1 component, use 'inject' directly.
-- *    If you have 2 components, use 'swerve' directly.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off eithers one-by-one.
concatInplus
    :: Inplus f
    => NP f as
    -> f (NS I as)
concatInplus = \case
    Nil     -> reject $ \case {}
    x :* xs -> swerve
      (Z . I)
      S
      (\case Z (I y) -> Left y; S ys -> Right ys)
      x
      (concatInplus xs)

-- | A version of 'concatInplus' for non-empty 'NP', but only
-- requiring an 'Inalt' instance.
--
-- @since 0.4.0.0
concatInalt
    :: Inalt f
    => NP f (a ': as)
    -> f (NS I (a ': as))
concatInalt (x :* xs) = case xs of
    Nil    -> invmap (Z . I) (\case Z (I y) -> y; S ys -> case ys of {}) x
    _ :* _ -> swerve
      (Z . I)
      S
      (\case Z (I y) -> Left y; S ys -> Right ys)
      x
      (concatInalt xs)
