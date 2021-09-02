{-# OPTIONS_GHC -Wno-orphans #-}

-- |
-- Module      : Data.HFunctor.Chain
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides an 'Interpret'able data type of "linked list of
-- tensor applications".
--
-- The type @'Chain' t@, for any @'Tensor' t@, is meant to be the same as
-- @'ListBy' t@ (the monoidal functor combinator for @t@), and represents
-- "zero or more" applications of @f@ to @t@.
--
-- The type @'Chain1' t@, for any @'Associative' t@, is meant to be the
-- same as @'NonEmptyBy' t@ (the semigroupoidal functor combinator for @t@) and
-- represents "one or more" applications of @f@ to @t@.
--
-- The advantage of using 'Chain' and 'Chain1' over 'ListBy' or 'NonEmptyBy' is that
-- they provide a universal interface for pattern matching and constructing
-- such values, which may simplify working with new such functor
-- combinators you might encounter.
module Data.HFunctor.Chain (
  -- * 'Chain'
    Chain(..)
  , foldChain, foldChainA
  , unfoldChain
  , unroll
  , reroll
  , unrolling
  , appendChain
  , splittingChain
  , toChain
  , injectChain
  , unconsChain
  -- * 'Chain1'
  , Chain1(..)
  , foldChain1, foldChain1A
  , unfoldChain1
  , unrollingNE
  , unrollNE
  , rerollNE
  , appendChain1
  , fromChain1
  , matchChain1
  , toChain1
  , injectChain1
  -- ** Matchable
  -- | The following conversions between 'Chain' and 'Chain1' are only
  -- possible if @t@ is 'Matchable'
  , splittingChain1
  , splitChain1
  , matchingChain
  , unmatchChain
  ) where

import           Control.Monad.Freer.Church
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Functor.Bind
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Day hiding              (intro1, intro2, elim1, elim2)
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Inplicative
import           Data.Functor.Invariant.Internative
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HBifunctor.Tensor.Internal
import           Data.HFunctor
import           Data.HFunctor.Chain.Internal
import           Data.HFunctor.Interpret
import           Data.Typeable
import           GHC.Generics
import qualified Data.Functor.Contravariant.Day       as CD
import qualified Data.Functor.Contravariant.Night     as N
import qualified Data.Functor.Invariant.Day           as ID
import qualified Data.Functor.Invariant.Night         as IN

instance (HBifunctor t, SemigroupIn t f) => Interpret (Chain1 t) f where
    retract = \case
      Done1 x  -> x
      More1 xs -> binterpret id retract xs
    interpret :: forall g. g ~> f -> Chain1 t g ~> f
    interpret f = go
      where
        go :: Chain1 t g ~> f
        go = \case
          Done1 x  -> f x
          More1 xs -> binterpret f go xs

-- | A type @'NonEmptyBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain1' t f@ is an actual concrete ADT that contains
-- successive applications of @t@ to itself, and you can pattern match on
-- each layer.
--
-- 'unrollingNE' states that the two types are isormorphic.  Use 'unrollNE'
-- and 'rerollNE' to convert between the two.
unrollingNE :: forall t f. (Associative t, FunctorBy t f) => NonEmptyBy t f <~> Chain1 t f
unrollingNE = isoF unrollNE rerollNE

-- | A type @'NonEmptyBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unrollNE' makes that successive application explicit,
-- buy converting it to a literal 'Chain1' of applications of @t@ to
-- itself.
--
-- @
-- 'unrollNE' = 'unfoldChain1' 'matchNE'
-- @
unrollNE :: (Associative t, FunctorBy t f) => NonEmptyBy t f ~> Chain1 t f
unrollNE = unfoldChain1 matchNE

-- | 'Chain1' is a semigroup with respect to @t@: we can "combine" them in
-- an associative way.
--
-- This is essentially 'biretract', but only requiring @'Associative' t@:
-- it comes from the fact that @'Chain1' t@ is the "free @'SemigroupIn'
-- t@".
--
-- @since 0.1.1.0
appendChain1
    :: forall t f. (Associative t, FunctorBy t f)
    => t (Chain1 t f) (Chain1 t f) ~> Chain1 t f
appendChain1 = unrollNE
             . appendNE
             . hbimap rerollNE rerollNE

-- | @'Chain1' t@ is the "free @'SemigroupIn' t@".  However, we have to
-- wrap @t@ in 'WrapHBF' to prevent overlapping instances.
instance (Associative t, FunctorBy t f, FunctorBy t (Chain1 t f)) => SemigroupIn (WrapHBF t) (Chain1 t f) where
    biretract = appendChain1 . unwrapHBF
    binterpret f g = biretract . hbimap f g

-- | @'Chain1' 'Day'@ is the free "semigroup in the semigroupoidal category
-- of endofunctors enriched by 'Day'" --- aka, the free 'Apply'.
instance Functor f => Apply (Chain1 Day f) where
    f <.> x = appendChain1 $ Day f x ($)

instance Functor f => Apply (Chain1 Comp f) where
    (<.>) = apDefault

-- | @'Chain1' 'Comp'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'Comp'" --- aka, the free 'Bind'.
instance Functor f => Bind (Chain1 Comp f) where
    x >>- f = appendChain1 (x :>>= f)

-- | @'Chain1' (':*:')@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by ':*:'" --- aka, the free 'Alt'.
instance Functor f => Alt (Chain1 (:*:) f) where
    x <!> y = appendChain1 (x :*: y)

-- | @'Chain1' 'Product'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'Product'" --- aka, the free 'Alt'.
instance Functor f => Alt (Chain1 Product f) where
    x <!> y = appendChain1 (Pair x y)

-- | @'Chain1' 'CD.Day'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'CD.Day'" --- aka, the free 'Divise'.
--
-- @since 0.3.0.0
instance Contravariant f => Divise (Chain1 CD.Day f) where
    divise f x y = appendChain1 $ CD.Day x y f

-- | @'Chain1' 'N.Night'@ is the free "semigroup in the semigroupoidal
-- category of endofunctors enriched by 'N.Night'" --- aka, the free
-- 'Decide'.
--
-- @since 0.3.0.0
instance Contravariant f => Decide (Chain1 N.Night f) where
    decide f x y = appendChain1 $ N.Night x y f

-- | @since 0.4.0.0
instance Invariant f => Inply (Chain1 ID.Day f) where
    gather f g x y = appendChain1 (ID.Day x y f g)

instance Tensor t i => Inject (Chain t i) where
    inject = injectChain

-- | @since 0.4.0.0
instance Invariant f => Inalt (Chain1 IN.Night f) where
    swerve f g h x y = appendChain1 (IN.Night x y f g h)

-- | We can collapse and interpret an @'Chain' t i@ if we have @'Tensor' t@.
instance MonoidIn t i f => Interpret (Chain t i) f where
    interpret
        :: forall g. ()
        => g ~> f
        -> Chain t i g ~> f
    interpret f = go
      where
        go :: Chain t i g ~> f
        go = \case
          Done x  -> pureT @t x
          More xs -> binterpret f go xs

-- | Convert a tensor value pairing two @f@s into a two-item 'Chain'.  An
-- analogue of 'toListBy'.
--
-- @since 0.3.1.0
toChain :: Tensor t i => t f f ~> Chain t i f
toChain = More . hright inject

-- | Create a singleton chain.
--
-- @since 0.3.0.0
injectChain :: Tensor t i => f ~> Chain t i f
injectChain = More . hright Done . intro1

-- | A 'Chain1' is "one or more linked @f@s", and a 'Chain' is "zero or
-- more linked @f@s".  So, we can convert from a 'Chain1' to a 'Chain' that
-- always has at least one @f@.
--
-- The result of this function always is made with 'More' at the top level.
fromChain1
    :: Tensor t i
    => Chain1 t f ~> Chain t i f
fromChain1 = foldChain1 (More . hright Done . intro1) More

-- | A type @'ListBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain' t i f@ is an actual concrete
-- ADT that contains successive applications of @t@ to itself, and you can
-- pattern match on each layer.
--
-- 'unrolling' states that the two types are isormorphic.  Use 'unroll'
-- and 'reroll' to convert between the two.
unrolling
    :: Tensor t i
    => ListBy t f <~> Chain t i f
unrolling = isoF unroll reroll

-- | A @'Chain1' t f@ is like a non-empty linked list of @f@s, and
-- a @'Chain' t i f@ is a possibly-empty linked list of @f@s.  This
-- witnesses the fact that the former is isomorphic to @f@ consed to the
-- latter.
splittingChain1
    :: forall t i f. (Matchable t i, FunctorBy t f)
    => Chain1 t f <~> t f (Chain t i f)
splittingChain1 = fromF unrollingNE
                . splittingNE @t
                . overHBifunctor id unrolling

-- | A @'Chain' t i f@ is a linked list of @f@s, and a @'Chain1' t f@ is
-- a non-empty linked list of @f@s.  This witnesses the fact that
-- a @'Chain' t i f@ is either empty (@i@) or non-empty (@'Chain1' t f@).
matchingChain
    :: forall t i f. (Tensor t i, Matchable t i, FunctorBy t f)
    => Chain t i f <~> i :+: Chain1 t f
matchingChain = fromF unrolling
              . matchingLB @t
              . overHBifunctor id unrollingNE

-- | The "reverse" function representing 'matchingChain'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
unmatchChain
    :: forall t i f. Tensor t i
    => i :+: Chain1 t f ~> Chain t i f
unmatchChain = unroll . (nilLB @t !*! fromNE @t) . hright rerollNE

-- | We have to wrap @t@ in 'WrapHBF' to prevent overlapping instances.
instance (Tensor t i, FunctorBy t (Chain t i f)) => SemigroupIn (WrapHBF t) (Chain t i f) where
    biretract = appendChain . unwrapHBF
    binterpret f g = biretract . hbimap f g

-- | @'Chain' t i@ is the "free @'MonoidIn' t i@".  However, we have to
-- wrap @t@ in 'WrapHBF' and @i@ in 'WrapF' to prevent overlapping instances.
instance (Tensor t i, FunctorBy t (Chain t i f)) => MonoidIn (WrapHBF t) (WrapF i) (Chain t i f) where
    pureT = Done . unwrapF

instance Apply (Chain Day Identity f) where
    f <.> x = appendChain $ Day f x ($)

-- | @'Chain' 'Day' 'Identity'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by 'Day'" --- aka, the free
-- 'Applicative'.
instance Applicative (Chain Day Identity f) where
    pure  = Done . Identity
    (<*>) = (<.>)

-- | @since 0.3.0.0
instance Divise (Chain CD.Day Proxy f) where
    divise f x y = appendChain $ CD.Day x y f

-- | @'Chain' 'CD.Day' 'Proxy'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by contravariant 'CD.Day'" --- aka,
-- the free 'Divisible'.
--
-- @since 0.3.0.0
instance Divisible (Chain CD.Day Proxy f) where
    divide f x y = appendChain $ CD.Day x y f
    conquer = Done Proxy

-- | @since 0.4.0.0
instance Inply (Chain ID.Day Identity f) where
    gather f g x y = appendChain (ID.Day x y f g)

-- | @since 0.4.0.0
instance Inplicative (Chain ID.Day Identity f) where
    knot = Done  . Identity

-- | @since 0.4.0.0
instance Inalt (Chain IN.Night IN.Not f) where
    swerve f g h x y = appendChain (IN.Night x y f g h)

-- | @since 0.4.0.0
instance Inplus (Chain IN.Night IN.Not f) where
    reject = Done . IN.Not

-- | @since 0.3.0.0
instance Decide (Chain N.Night N.Not f) where
    decide f x y = appendChain $ N.Night x y f

-- | @'Chain' 'N.Night' 'N.Refutec'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by 'N.Night'" --- aka, the free
-- 'Conclude'.
--
-- @since 0.3.0.0
instance Conclude (Chain N.Night N.Not f) where
    conclude = Done . N.Not

instance Apply (Chain Comp Identity f) where
    (<.>) = apDefault

instance Applicative (Chain Comp Identity f) where
    pure  = Done . Identity
    (<*>) = (<.>)

instance Bind (Chain Comp Identity f) where
    x >>- f = appendChain (x :>>= f)

-- | @'Chain' 'Comp' 'Identity'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by 'Comp'" --- aka, the free
-- 'Monad'.
instance Monad (Chain Comp Identity f) where
    (>>=) = (>>-)

instance Functor f => Alt (Chain (:*:) Proxy f) where
    x <!> y = appendChain (x :*: y)

-- | @'Chain' (':*:') 'Proxy'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by ':*:'" --- aka, the free
-- 'Plus'.
instance Functor f => Plus (Chain (:*:) Proxy f) where
    zero = Done Proxy

instance Functor f => Alt (Chain Product Proxy f) where
    x <!> y = appendChain (Pair x y)

-- | @'Chain' (':*:') 'Proxy'@ is the free "monoid in the monoidal
-- category of endofunctors enriched by ':*:'" --- aka, the free
-- 'Plus'.
instance Functor f => Plus (Chain Product Proxy f) where
    zero = Done Proxy

