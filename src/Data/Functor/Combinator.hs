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
-- manipulate them.  This is the main "entrypoint" of the library.
--
-- Classes include:
--
-- *  'HFunctor' and 'HBifunctor', used to swap out the functors that the
--    combinators modify
-- *  'Interpret', 'Associative', 'Tensor', used to inject and interpret
-- functor values with respect to their combinators.
--
-- We have some helpful utility functions, as well, built on top of these
-- typeclasses.
--
-- The second half of this module exports the various useful functor
-- combinators that can modify functors to add extra functionality, or join
-- two functors together and mix them in different ways.  Use them to build
-- your final structure by combining simpler ones in composable ways!
--
-- See <https://blog.jle.im/entry/functor-combinatorpedia.html> and the
-- README for a tutorial and a rundown on each different functor
-- combinator.
module Data.Functor.Combinator (
  -- * Classes
  -- | A lot of type signatures are stated in terms of '~>'.  '~>'
  -- represents a "natural transformation" between two functors: a value of
  -- type @f '~>' g@ is a value of type 'f a -> g a@ that works for /any/
  -- @a@.
    type (~>)
  , type (<~>)
  -- ** Single Functors
  -- | Classes that deal with single-functor combinators, that enhance
  -- a single functor.
  , HFunctor(..)
  , Inject(..)
  , Interpret(..)
  , forI
  , getI
  , collectI
  -- ** Multi-Functors
  -- | Classes that deal with two-functor combinators, that "mix" two
  -- functors together in some way.
  , HBifunctor(..)
  -- *** Associative
  , Associative(..)
  , SemigroupIn(..)
  , biget, bicollect
  , (!*!)
  , (!$!)
  -- *** Tensor
  , Tensor(..)
  , MonoidIn(..)
  , nilLB, consLB
  , inL, inR
  , outL, outR
  -- * Combinators
  -- | Functor combinators
  -- ** Single
  , Coyoneda(..)
  , ListF(..)
  , NonEmptyF(..)
  , MaybeF(..)
  , MapF(..)
  , NEMapF(..)
  , Ap
  , Ap1(..)
  , Alt
  , Free
  , Free1
  , Lift
  , Step(..)
  , Steps(..)
  , ProxyF(..)
  , ConstF(..)
  , EnvT(..)
  , ReaderT(..)
  , Flagged(..)
  , IdentityT(..)
  , Void2
  , Final(..)
  , FreeOf(..)
  , ComposeT(..)
  -- ** Multi
  , Day(..)
  , (:*:)(..), prodOutL, prodOutR
  , (:+:)(..), V1
  , These1(..)
  , Comp(Comp, unComp)
  , LeftF(..)
  , RightF(..)
  -- ** Combinator Combinators
  , HLift(..)
  , HFree(..)
  -- * Util
  -- ** Natural Transformations
  , generalize
  , absorb
  ) where

import           Control.Alternative.Free
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Comonad.Trans.Env
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Reader
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Functor.Apply.Free
import           Data.Functor.Coyoneda
import           Data.Functor.Day
import           Data.Functor.These
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor
import           Data.HFunctor.Final
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
import           GHC.Generics
