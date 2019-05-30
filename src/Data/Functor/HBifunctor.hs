{-# LANGUAGE DeriveFunctor      #-}
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
  ) where

import           Data.Functor.HFunctor.Internal
