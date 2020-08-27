-- |
-- Module      : Data.Functor.Apply.Free
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- The free 'Apply'.  Provides 'Ap1' and various utility methods.  See
-- 'Ap1' for more details.
--
-- Ideally 'Ap1' would be in the /free/ package.  However, it is defined
-- here for now.
module Data.Functor.Apply.Free (
    Ap1(.., DayAp1, ap1Day)
  , toAp, fromAp
  , liftAp1
  , retractAp1
  , runAp1
  ) where

import           Control.Applicative.Free
import           Control.Natural
import           Data.Function
import           Data.Functor.Apply
import           Data.Functor.Day
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.HFunctor
import           Data.HFunctor.HTraversable
import           Data.HFunctor.Interpret
import           Data.Kind
import           GHC.Generics

-- | One or more @f@s convolved with itself.
--
-- Essentially:
--
-- @
-- 'Ap1' f
--     ~ f                            -- one f
--   ':+:' (f \`'Day'` f)          -- two f's
--   :+: (f \`Day\` f \`Day\` f)           -- three f's
--   :+: (f \`Day\` f \`Day\` f \`Day\` f)  -- four f's
--   :+: ...                          -- etc.
-- @
--
-- Useful if you want to promote an @f@ to a situation with "at least one
-- @f@ sequenced with itself".
--
-- Mostly useful for its 'HFunctor' and 'Interpret' instance, along with
-- its relationship with 'Ap' and 'Day'.
--
-- This is the free 'Apply' ---  Basically a "non-empty" 'Ap'.
--
-- The construction here is based on 'Ap', similar to now
-- 'Data.List.NonEmpty.NonEmpty' is built on list.
data Ap1 :: (Type -> Type) -> Type -> Type where
    Ap1 :: f a -> Ap f (a -> b) -> Ap1 f b

-- | An 'Ap1' is a "non-empty" 'Ap'; this function "forgets" the non-empty
-- property and turns it back into a normal 'Ap'.
toAp :: Ap1 f ~> Ap f
toAp (Ap1 x xs) = Ap x xs

-- | Convert an 'Ap' into an 'Ap1' if possible.  If the 'Ap' was "empty",
-- return the 'Pure' value instead.
fromAp :: Ap f ~> (Identity :+: Ap1 f)
fromAp = \case
    Pure x  -> L1 $ Identity x
    Ap x xs -> R1 $ Ap1 x xs

-- | @since 0.3.0.0
instance Invariant (Ap1 f) where
    invmap f _ = fmap f

-- | An @'Ap1' f@ is just a @'Day' f ('Ap' f)@.  This bidirectional pattern
-- synonym lets you treat it as such.
pattern DayAp1 :: Day f (Ap f) a -> Ap1 f a
pattern DayAp1 { ap1Day } <- ((\case Ap1 x y -> Day x y (&)) -> ap1Day)
  where
    DayAp1 (Day x y f) = Ap1 x (flip f <$> y)
{-# COMPLETE DayAp1 #-}

deriving instance Functor (Ap1 f)

instance Apply (Ap1 f) where
    Ap1 x xs <.> ys = Ap1 x (flip <$> xs <*> toAp ys)

-- | Embed an @f@ into 'Ap1'.
liftAp1 :: f ~> Ap1 f
liftAp1 x = Ap1 x (Pure id)

-- | Extract the @f@ out of the 'Ap1'.
--
-- @
-- 'retractAp1' . 'liftAp1' == id
-- @
retractAp1 :: Apply f => Ap1 f ~> f
retractAp1 (Ap1 x xs) = retractAp1_ x xs

-- | Interpret an @'Ap' f@ into some 'Apply' context @g@.
runAp1
    :: Apply g
    => (f ~> g)
    -> Ap1 f ~> g
runAp1 f (Ap1 x xs) = runAp1_ f x xs

instance HFunctor Ap1 where
    hmap f (Ap1 x xs) = Ap1 (f x) (hmap f xs)

instance Inject Ap1 where
    inject = liftAp1

instance HBind Ap1 where
    hbind = runAp1

instance HTraversable Ap1 where
    htraverse f (Ap1 x xs) = Ap1 <$> f x <*> htraverse f xs

instance HTraversable1 Ap1 where
    htraverse1 f (Ap1 x xs) = traverseAp1_ f x xs

traverseAp1_
    :: forall f g h a b. Apply h
    => (forall x. f x -> h (g x))
    -> f a
    -> Ap f (a -> b)
    -> h (Ap1 g b)
traverseAp1_ f = go
  where
    go :: f x -> Ap f (x -> y) -> h (Ap1 g y)
    go x = \case
      Pure y  -> (`Ap1` Pure y) <$> f x
      Ap y ys -> Ap1 <$> f x <.> (toAp <$> go y ys)


instance Apply f => Interpret Ap1 f where
    retract = retractAp1
    interpret = runAp1

retractAp1_ :: Apply f => f a -> Ap f (a -> b) -> f b
retractAp1_ x = \case
    Pure y  ->   y <$> x
    Ap y ys -> (&) <$> x <.> retractAp1_ y ys

runAp1_
    :: forall f g a b. Apply g
    => (f ~> g)
    -> f a
    -> Ap f (a -> b)
    -> g b
runAp1_ f = go
  where
    go :: f x -> Ap f (x -> y) -> g y
    go x = \case
      Pure y  ->   y <$> f x
      Ap y ys -> (&) <$> f x <.> go y ys

