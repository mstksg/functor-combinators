{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE EmptyCase          #-}
{-# LANGUAGE EmptyDataDeriving  #-}
{-# LANGUAGE ExplicitNamespaces #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeInType         #-}

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
-- *  'Interpret', 'Associative', 'Monoidal', used to inject and interpret
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
-- See README for a tutorial and a rundown on each different functor
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
  , Interpret(..)
  , forI
  , getI
  , collectI
  -- ** Multi-Functors
  -- | Classes that deal with two-functor combinators, that "mix" two
  -- functors together in some way.
  , HBifunctor(..)
  , Semigroupoidal(SF, appendSF, consSF, toSF, biretract, binterpret)
  , Tensor(..)
  , Monoidal(MF, appendMF, splitSF, toMF, fromSF, pureT)
  , inL, inR
  , biget, bicollect
  , (!*!)
  , (!$!)
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
  , ProxyF(..)
  , Void2
  , Final(..)
  , FreeOf(..)
  -- ** Multi
  , Day(..)
  , (:*:)(..)
  , (:+:)(..), Void1
  , These1(..)
  , Comp(Comp, unComp)
  ) where

import           Control.Alternative.Free
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Coerce
import           Data.Constraint.Trivial
import           Data.Data
import           Data.Deriving
import           Data.Functor.Apply.Free
import           Data.Functor.Coyoneda
import           Data.Functor.Day
import           Data.Functor.These
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor
import           Data.HFunctor.Final
import           Data.HFunctor.Interpret
import           Data.HFunctor.IsoF
import           GHC.Generics

-- | The functor combinator that forgets all structure in the input.
-- Ignores the input structure and stores no information.
--
-- Acts like the "zero" with respect to functor combinator composition.
--
-- @
-- 'Control.Monad.Trans.Compose.ComposeT' ProxyF f      ~ ProxyF
-- 'Control.Monad.Trans.Compose.ComposeT' f      ProxyF ~ ProxyF
-- @
--
-- It can be 'inject'ed into (losing all information), but it is impossible
-- to ever 'retract' or 'interpret' it.
data ProxyF f a = ProxyF
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''ProxyF
deriveRead1 ''ProxyF
deriveEq1 ''ProxyF
deriveOrd1 ''ProxyF

instance HFunctor ProxyF where
    hmap _ = coerce

instance HBind ProxyF where
    hbind _ = coerce

instance Inject ProxyF where
    inject _ = ProxyF

instance Interpret ProxyF where
    type C ProxyF = Impossible
    retract  = absurdible . fromProxyF

fromProxyF :: ProxyF f a -> Proxy f
fromProxyF ~ProxyF = Proxy
