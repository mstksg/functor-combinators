{-# LANGUAGE ExplicitNamespaces #-}

-- |
-- Module      : Data.Functor.Combinator
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Functor combinators and tools (typeclasses and utiility functions) to
-- manipulate them.
--
-- Classes include:
--
-- *  'HFunctor' and 'HBifunctor', used to swap out the functors that the
--    combinators modify
-- *  'Interpret', 'Tensor', 'Monoidal', used to inject and interpret
--    functor values with respect to their combinators.
--
-- We have some helpful utility functions, as well, built on top of these
-- typeclasses.
--
-- The second half of this module exports the various useful functor
-- combinators that can modify functors to add extra functionality, or join
-- two functors together and mix them in different ways.  Use them to build
-- your final structure by combining simpler ones in composable ways!
--
-- See README for a tutorial and a rundown on each different functor
-- combinator.
--
module Data.Functor.Combinator (
  -- * Classes
  -- | A lot of type signatures are stated in terms of '~>'.  '~>'
  -- represents a "natural transformation" between two functors: a value of
  -- type @f '~>' g@ is a value of type 'f a -> g a@ that works for /any/
  -- @a@.
    type (~>)
  -- ** Single Functors
  -- | Classes that deal with single-functor combinators, that enhance
  -- a single functor.
  , HFunctor(..)
  , Interpret(..), interpretFor
  , extractI, getI, collectI
  -- ** Multi-Functors
  -- | Classes that deal with two-functor combinators, that "mix" two
  -- functors together in some way.
  , HBifunctor(..)
  , Tensor(I)
  , Monoidal(TM, retractT, interpretT, pureT, toTM)
  , inL, inR
  , (!$!)
  , extractT, getT, (!*!), collectT
  -- * Combinators
  -- | Functor combinators
  -- ** Single
  , Coyoneda(..)
  , ListF(..)
  , NonEmptyF(..)
  , MaybeF(..)
  , Ap
  , Ap1
  , Alt
  , Free
  , Step(..)
  , Steps(..)
  -- ** Multi
  , Day(..)
  , (:*:)(..)
  , (:+:)(..)
  , These1(..)
  , Comp(Comp, unComp)
  , Final(..)
  , FreeOf(..)
  ) where

import           Control.Alternative.Free
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Functor.Apply.Free
import           Data.Functor.Coyoneda
import           Data.Functor.Day
import           Data.Functor.HFunctor
import           Data.Functor.HFunctor.Final
import           Data.Functor.Tensor
import           Data.Functor.These
import           GHC.Generics
