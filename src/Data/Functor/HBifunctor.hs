{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DerivingVia        #-}
{-# LANGUAGE KindSignatures     #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Functor.HBifunctor (
    HBifunctor(..)
  , WrappedHBifunctor(..)
  , overHBifunctor
  ) where

import           Data.Functor.HFunctor.Internal
import           Data.Functor.HFunctor.IsoF

overHBifunctor
    :: HBifunctor t
    => AnIsoF' f f'
    -> AnIsoF' g g'
    -> t f g <~> t f' g'
overHBifunctor (cloneIsoF' -> f) (cloneIsoF' -> g) =
        isoF (hbimap (viewF   f) (viewF   g))
             (hbimap (reviewF f) (reviewF g))

