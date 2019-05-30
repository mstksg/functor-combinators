{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- |
-- Module      : Data.Functor.HFunctor
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides tools for working with unary functor combinators.
--
-- These are types @f@ that take a functor @f@ and return a new functor @t
-- f@, enhancing @f@ with new structure and abilities.
--
-- The main operations these combinators support are:
--
-- @
-- 'hmap' :: (forall x. f x -> g x) -> t f a -> t g a
-- @
--
-- which lets you "swap out" the functor being transformed,
--
-- @
-- 'inject' :: f a -> t f a
-- @
--
-- which lets you "lift" an @f a@ into its transformed version, and also:
--
-- @
-- 'interpret'
--     :: C t g
--     => (forall x. f a -> g a)
--     -> t f a
--     -> g a
-- @
--
-- that lets you "interpret" a @t f a@ into a context @g a@, essentially
-- "running" the computaiton that it encodes.  The context is required to
-- have a typeclass constraints that reflects what is "required" to be able
-- to run a functor combinator.
--
-- Every single instance provides different tools.  Check out the instance
-- list for a nice list of useful combinators, or also the README for
-- a high-level rundown.
--
-- See "Data.Functor.Tensor" for binary functor combinators that mix
-- together two or more different functors.
module Data.Functor.HFunctor (
    HFunctor(..)
  ) where

import           Data.Functor.HFunctor.Internal
