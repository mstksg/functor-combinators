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
  unsafePlus,
  unsafeApply,
  unsafeBind,
  unsafePointed,
  unsafeConclude,
  unsafeDivise,
  unsafeInvariantCo,
  unsafeInvariantContra,
  unsafeInplyCo,
  unsafeInplyContra,
  unsafeInplicativeCo,
  unsafeInplicativeContra,
) where

import Control.Applicative
import Data.Constraint
import Data.Constraint.Unsafe
import Data.Functor.Bind
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Conclude
import Data.Functor.Contravariant.Divise
import Data.Functor.Contravariant.Divisible
import Data.Functor.Invariant
import Data.Functor.Invariant.Inplicative
import Data.Functor.Plus
import Data.Pointed

-- | For any @'Alternative' f@, produce a value that would require @'Plus'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Plus' instance.
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
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
unsafePointed :: forall f proxy r. Applicative f => proxy f -> (Pointed f => r) -> r
unsafePointed _ x = case unsafeCoerceConstraint @(Pointed (PointMe f)) @(Pointed f) of
  Sub Dict -> x

-- | For any @'Decidable' f@, produce a value that would require @'Conclude'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Conclude' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.3.0.0
unsafeConclude :: forall f proxy r. Decidable f => proxy f -> (Conclude f => r) -> r
unsafeConclude _ x = case unsafeCoerceConstraint @(Conclude (WrappedDivisible f)) @(Conclude f) of
  Sub Dict -> x

-- | For any @'Divisible' f@, produce a value that would require @'Divise'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has a 'Divise' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.3.0.0
unsafeDivise :: forall f proxy r. Divisible f => proxy f -> (Divise f => r) -> r
unsafeDivise _ x = case unsafeCoerceConstraint @(Divise (WrappedDivisible f)) @(Divise f) of
  Sub Dict -> x

-- | For any @'Functor' f@, produce a value that would require @'Invariant'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has an 'Invariant' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.4.1.0
unsafeInvariantCo :: forall f proxy r. Functor f => proxy f -> (Invariant f => r) -> r
unsafeInvariantCo _ x = case unsafeCoerceConstraint @(Invariant (WrappedFunctor f)) @(Invariant f) of
  Sub Dict -> x

-- | For any @'Contravariant' f@, produce a value that would require @'Invariant'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has an 'Invariant' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.4.1.0
unsafeInvariantContra :: forall f proxy r. Contravariant f => proxy f -> (Invariant f => r) -> r
unsafeInvariantContra _ x = case unsafeCoerceConstraint @(Invariant (WrappedContravariant f)) @(Invariant f) of
  Sub Dict -> x

-- | For any @'Apply' f@, produce a value that would require @'Inply'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has an 'Inply' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.4.1.0
unsafeInplyCo :: forall f proxy r. Apply f => proxy f -> (Inply f => r) -> r
unsafeInplyCo _ x = case unsafeCoerceConstraint @(Inply (WrappedFunctor f)) @(Inply f) of
  Sub Dict -> x

-- | For any @'Divise' f@, produce a value that would require @'Inply'
-- f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has an 'Inply' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.4.1.0
unsafeInplyContra :: forall f proxy r. Divise f => proxy f -> (Inply f => r) -> r
unsafeInplyContra _ x = case unsafeCoerceConstraint @(Inply (WrappedContravariant f)) @(Inply f) of
  Sub Dict -> x

-- | For any @'Applicative' f@, produce a value that would require
-- @'Inplicative' f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has an 'Inplicative' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.4.1.0
unsafeInplicativeCo ::
  forall f proxy r. (Applicative f, Invariant f) => proxy f -> (Inplicative f => r) -> r
unsafeInplicativeCo _ x = case unsafeCoerceConstraint @(Inply (WrappedApplicativeOnly f)) @(Inplicative f) of
  Sub Dict -> x

-- | For any @'Divisibl3' f@, produce a value that would require
-- @'Inplicative' f@.
--
-- Always use with concrete and specific @f@ only, and never use with any
-- @f@ that already has an 'Inplicative' instance.
--
-- The 'Data.Proxy.Proxy' argument allows you to specify which specific @f@
-- you want to enhance.  You can pass in something like @'Data.Proxy.Proxy'
-- \@MyFunctor@.
--
-- @since 0.4.1.0
unsafeInplicativeContra ::
  forall f proxy r. (Divisible f, Invariant f) => proxy f -> (Inplicative f => r) -> r
unsafeInplicativeContra _ x = case unsafeCoerceConstraint @(Inply (WrappedDivisibleOnly f)) @(Inplicative f) of
  Sub Dict -> x
