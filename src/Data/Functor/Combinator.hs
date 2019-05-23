
module Data.Functor.Combinator (
  -- * Main interface
  -- ** Single Functors
    HFunctor(..)
  , Interpret(..)
  -- ** Mulit-Functors
  , HBifunctor(..)
  , Tensor(I)
  , Monoidal(TM, retractT, interpretT, pureT, toTM)
  -- * Combinators
  , Coyoneda(..)
  , ListF(..)
  , Ap
  , Alt
  , Free
  , Step(..)
  , Day(..)
  , (:*:)(..)
  , (:+:)(..)
  , Comp
  , Final(..)
  , Cons(..), Uncons(..)
  ) where

import           Control.Alternative.Free
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Data.Functor.Coyoneda
import           Data.Functor.Day
import           Data.Functor.HFunctor
import           Data.Functor.HFunctor.Final
import           Data.Functor.Tensor
import           Data.Functor.Tensor.Cons
import           GHC.Generics
