{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}

module Data.Functor.Apply.Free (
    Ap1(..)
  , toAp
  , liftAp1
  , retractAp1
  , runAp1
  ) where

import           Control.Applicative.Free
import           Control.Natural
import           Data.Function
import           Data.Functor.Apply
import           Data.Functor.HFunctor
import           Data.Kind

-- | The free 'Apply'.  Basically a "non-empty" 'Ap'.
--
-- The construction here is based on 'Ap', similar to now
-- 'Data.List.NonEmpty.NonEmpty' is built on list.
data Ap1 :: (Type -> Type) -> Type -> Type where
    Ap1 :: f a -> Ap f (a -> b) -> Ap1 f b

-- | An 'Ap1' is a "non-empty" 'Ap'; this function "forgets" the non-empty
-- property and turns it back into a normal 'Ap'.
toAp :: Ap1 f ~> Ap f
toAp (Ap1 x xs) = Ap x xs

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

instance Interpret Ap1 where
    type C Ap1 = Apply

    inject = liftAp1
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

