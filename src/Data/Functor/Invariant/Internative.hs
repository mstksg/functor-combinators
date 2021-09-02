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
    Inalt(..)
  , Inplus(..)
  , Internative
  ) where

import           Data.Functor.Invariant
import           Data.Functor.Invariant.Inplicative
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
class Inalt f => Inplus f where
    reject :: (a -> Void) -> f a

-- | The invariant counterpart to 'Alternative' and 'Decidable': represents
-- a combination of both 'Applicative' and 'Alt', or 'Divisible' and
-- 'Conclude'.  There are laws?
class (Inplus f, Inplicative f) => Internative f

