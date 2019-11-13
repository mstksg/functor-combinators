-- |
-- Module      : Data.Functor.Combinator.Unsafe
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Working with non-standard typeclasses like 'Plus', 'Apply', 'Bind', and
-- 'Pointed' will sometimes cause problems when using with libraries that
-- do not provide instances, even though their types already are instances
-- of 'Alternative' or 'Applicative' or 'Monad'.
--
-- This module provides unsafe methods to "promote" 'Applicative' instances
-- to 'Apply', 'Alternative' to 'Plus', etc.
--
-- They are unsafe in the sense that if those types /already/ have those
-- instances, this will cause overlapping instances errors or problems with
-- coherence.  Because of this, you should always use these with /specific/
-- @f@s, and never in a polymorphic way over @f@.
module Data.Functor.Combinator.Unsafe (
    unsafePlus
  , unsafeApply
  , unsafeBind
  , unsafePointed
  ) where

import           Control.Applicative
import           Data.Constraint
import           Data.Constraint.Unsafe
import           Data.Functor.Bind
import           Data.Functor.Plus
import           Data.Pointed

-- | For any @'Alternative' f@, produce a value that would require @'Plus'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Plus' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafePlus :: forall f proxy r. Alternative f => proxy f -> (Plus f => r) -> r
unsafePlus _ x = case unsafeCoerceConstraint @(Plus (WrappedApplicative f)) @(Plus f) of
    Sub Dict -> x

-- | For any @'Applicative' f@, produce a value that would require @'Apply'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Apply' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafeApply :: forall f proxy r. Applicative f => proxy f -> (Apply f => r) -> r
unsafeApply _ x = case unsafeCoerceConstraint @(Apply (WrappedApplicative f)) @(Apply f) of
    Sub Dict -> x

-- | For any @'Monad' f@, produce a value that would require @'Bind'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Bind' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafeBind :: forall f proxy r. Monad f => proxy f -> (Bind f => r) -> r
unsafeBind _ x = case unsafeCoerceConstraint @(Bind (WrappedMonad f)) @(Bind f) of
    Sub Dict -> x

newtype PointMe f a = PointMe (f a)

instance Applicative f => Pointed (PointMe f) where
    point = PointMe . pure

-- | For any @'Applicative' f@, produce a value that would require
-- @'Pointed' f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Pointed' instance.
--
-- See documentation for 'Data.HBifunctor.Tensor.upgradeC' for example
-- usages.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafePointed :: forall f proxy r. Applicative f => proxy f -> (Pointed f => r) -> r
unsafePointed _ x = case unsafeCoerceConstraint @(Pointed (PointMe f)) @(Pointed f) of
    Sub Dict -> x

