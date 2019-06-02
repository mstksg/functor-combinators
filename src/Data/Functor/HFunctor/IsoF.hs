{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Functor.HFunctor.IsoF (
    type (<~>)
  , isoF
  , viewF, reviewF, overF
  , fromF
  , AnIsoF'
  , cloneIsoF'
  , Exchange(..)
  ) where

import           Data.Profunctor
import           Control.Natural
import           Data.Tagged

type f <~> g  = forall p a. Profunctor p => p (g a) (g a) -> p (f a) (f a)
infixr 0 <~>

isoF
    :: f ~> g
    -> g ~> f
    -> f <~> g
isoF = dimap

viewF :: f <~> g -> f ~> g
viewF i = runForget (i (Forget id))

reviewF :: f <~> g -> g ~> f
reviewF i x = unTagged (i (Tagged x))

overF :: (f <~> g) -> (g ~> g) -> (f ~> f)
overF i f = i f

fromF :: AnIsoF' f g -> (g <~> f)
fromF i = isoF g f
  where
    Exchange f g = i (Exchange id id)

data Exchange a b s t = Exchange (s -> a) (b -> t)

instance Profunctor (Exchange a b) where
    dimap f g (Exchange x y) = Exchange (x . f) (g . y)

type AnIsoF' f g = forall a. Exchange (g a) (g a) (g a) (g a)
                          -> Exchange (g a) (g a) (f a) (f a)

cloneIsoF' :: AnIsoF' f g -> (f <~> g)
cloneIsoF' i = isoF f g
  where
    Exchange f g = i (Exchange id id)
