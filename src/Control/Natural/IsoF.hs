-- |
-- Module      : Control.Natural.IsoF
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Types describing isomorphisms between two functors, and functions to
-- manipulate them.
module Control.Natural.IsoF (
  type (~>),
  type (<~>),
  isoF,
  coercedF,
  viewF,
  reviewF,
  overF,
  fromF,
) where

import Control.Natural
import Data.Coerce
import Data.Kind
import Data.Profunctor
import Data.Tagged

-- | The type of an isomorphism between two functors.  @f '<~>' g@ means that
-- @f@ and @g@ are isomorphic to each other.
--
-- We can effectively /use/ an @f \<~\> g@ with:
--
-- @
-- 'viewF'   :: (f \<~\> g) -> f a -> g a
-- 'reviewF' :: (f \<~\> g) -> g a -> a a
-- @
--
-- Use 'viewF' to extract the "@f@ to @g@" function, and 'reviewF' to
-- extract the "@g@ to @f@" function.  Reviewing and viewing the same value
-- (or vice versa) leaves the value unchanged.
--
-- One nice thing is that we can compose isomorphisms using '.' from
-- "Prelude":
--
-- @
-- ('.') :: f \<~\> g
--     -> g \<~\> h
--     -> f \<~\> h
-- @
--
-- Another nice thing about this representation is that we have the
-- "identity" isomorphism by using 'id' from "Prelude".
--
-- @
-- 'id' :: f '<~>' g
-- @
--
-- As a convention, most isomorphisms have form "X-ing", where the
-- forwards function is "ing".  For example, we have:
--
-- @
-- 'Data.HBifunctor.Tensor.splittingSF' :: 'Data.HBifunctor.Tensor.Monoidal' t => 'Data.HBifunctor.Associative.SF' t a '<~>' t f ('Data.HBifunctor.Tensor.MF' t f)
-- 'Data.HBifunctor.Tensor.splitSF'     :: Monoidal t => SF t a  '~>' t f (MF t f)
-- @
type f <~> g = forall p a. Profunctor p => p (g a) (g a) -> p (f a) (f a)

infixr 0 <~>

-- | Create an @f '<~>' g@ by providing both legs of the isomorphism (the
-- @f a -> g a@ and the @g a -> f a@.
isoF ::
  f ~> g ->
  g ~> f ->
  f <~> g
isoF f g a = dimap f g a

-- | An isomorphism between two functors that are coercible/have the same
-- internal representation.  Useful for newtype wrappers.
coercedF ::
  forall f g. (forall x. Coercible (f x) (g x), forall x. Coercible (g x) (f x)) => f <~> g
coercedF = isoF coerce coerce

-- | Use a '<~>' by retrieving the "forward" function:
--
-- @
-- 'viewF'   :: (f <~> g) -> f a -> g a
-- @
viewF :: f <~> g -> f ~> g
viewF i = runForget (i (Forget id))

-- | Use a '<~>' by retrieving the "backwards" function:
--
-- @
-- 'viewF'   :: (f <~> g) -> f a -> g a
-- @
reviewF :: f <~> g -> g ~> f
reviewF i x = unTagged (i (Tagged x))

-- | Lift a function @g a ~> g a@ to be a function @f a -> f a@, given an
-- isomorphism between the two.
--
-- One neat thing is that @'overF' i id == id@.
overF :: f <~> g -> g ~> g -> f ~> f
overF i f = i f

-- | Reverse an isomorphism.
--
-- @
-- 'viewF'   ('fromF' i) == 'reviewF' i
-- 'reviewF' ('fromF' i) == 'viewF' i
-- @
fromF ::
  forall (f :: Type -> Type) (g :: Type -> Type).
  () =>
  f <~> g ->
  g <~> f
fromF i = isoF (reviewF i) (viewF i)
