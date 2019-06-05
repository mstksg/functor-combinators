{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Data.HBifunctor.Tensor.Matchable (
    Matchable(..)
  , splittingSF
  , matchingMF
  -- * 'Chain'
  , splitChain1, unsplitChain1, splittingChain1
  , matchChain, unmatchChain, matchingChain
  ) where

import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Natural
import           Data.Functor.Apply.Free
import           Data.Functor.Day
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor.IsoF
import           GHC.Generics hiding         (C)

class Monoidal t => Matchable t where
    unsplitSF :: t f (MF t f) ~> SF t f
    matchMF   :: MF t f ~> I t :+: SF t f

instance Matchable (:*:) where
    unsplitSF = ProdNonEmpty
    matchMF   = fromListF

instance Matchable Day where
    unsplitSF = DayAp1
    matchMF   = fromAp

instance Matchable (:+:) where
    unsplitSF   = stepUp
    matchMF     = R1

splittingSF :: Matchable t => SF t f <~> t f (MF t f)
splittingSF = isoF splitSF unsplitSF

matchingMF :: forall t f. Matchable t => MF t f <~> I t :+: SF t f
matchingMF = isoF (matchMF @t) (unmatchMF @t)

splittingChain1
    :: forall t f. (Matchable t, Functor f)
    => Chain1 t f <~> t f (Chain t (I t) f)
splittingChain1 = fromF unrollingSF
                . splittingSF @t
                . overHBifunctor id unrollingMF

splitChain1
    :: forall t f. Matchable t
    => Chain1 t f ~> t f (Chain t (I t) f)
splitChain1 = hright (unrollMF @t) . splitSF @t . rerollSF

unsplitChain1
    :: forall t f. (Matchable t, Functor f)
    => t f (Chain t (I t) f) ~> Chain1 t f
unsplitChain1 = reviewF splittingChain1

matchingChain
    :: forall t f. (Matchable t, Functor f)
    => Chain t (I t) f <~> I t :+: Chain1 t f
matchingChain = fromF unrollingMF
              . matchingMF @t
              . overHBifunctor id unrollingSF

matchChain
    :: forall t f. (Matchable t, Functor f)
    => Chain t (I t) f ~> I t :+: Chain1 t f
matchChain = hright (unrollSF @t)
           . matchMF @t
           . rerollMF @t

unmatchChain
    :: forall t f. Matchable t
    => I t :+: Chain1 t f ~> Chain t (I t) f
unmatchChain = unrollMF @t . unmatchMF @t . hright (rerollSF @t)
