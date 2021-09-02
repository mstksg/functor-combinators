
module Data.Functor.Invariant.Internative (
    Inalt(..)
  , Inplus(..)
  , Internative
  ) where

import           Data.Functor.Invariant
import           Data.Functor.Invariant.Inplicative
import           Data.Void

class Invariant f => Inalt f where
    swerve
        :: (b -> a)
        -> (c -> a)
        -> (a -> Either b c)
        -> f b
        -> f c
        -> f a
    swerve f g h x y = invmap (either f g) h (swerved x y)
    swerved
        :: f a
        -> f b
        -> f (Either a b)
    swerved = swerve Left Right id
    {-# MINIMAL swerve | swerved #-}

class Inalt f => Inplus f where
    reject :: (a -> Void) -> f a

class (Inplus f, Inplicative f) => Internative f

---- | Invariantly combine two 'DecAlt's.
----
---- Analogous to '<|>' and 'decide'.  If there was some typeclass that
---- represented semigroups on invariant 'Night', this would be the method of that
---- typeclass.
----
---- The identity of this is 'Reject'.
----
---- @since 0.3.4.0
--swerve
--    :: (a -> Either b c)
--    -> (b -> a)
--    -> (c -> a)
--    -> DecAlt f b
--    -> DecAlt f c
--    -> DecAlt f a
--swerve f g h x y = coerce appendChain (Night x y f g h)

---- | Convenient wrapper over 'swerve' that simply combines the two options
---- in an 'Either'.  Analogous to '<|>' and 'decided'.
----
---- @since 0.3.4.0
--swerved
--    :: DecAlt f a
--    -> DecAlt f b
--    -> DecAlt f (Either a b)
--swerved = swerve id Left Right

