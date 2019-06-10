{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DefaultSignatures       #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- |
-- Module      : Data.HFunctor.Interpret
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides tools for working with unary functor combinators
-- that represent interpretable schemas.
--
-- These are types @t@ that take a functor @f@ and return a new functor @t
-- f@, enhancing @f@ with new structure and abilities.
--
-- For these, we have:
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
module Data.HFunctor.Interpret (
    HFunctor(..)
  , Interpret(..), forI
  -- * Utilities
  , getI
  , collectI
  , AndC
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Monad.Reader
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Data.Coerce
import           Data.Constraint.Trivial
import           Data.Functor.Bind
import           Data.Functor.Coyoneda
import           Data.Functor.Plus
import           Data.Functor.Reverse
import           Data.HFunctor
import           Data.Kind
import           Data.Maybe
import           Data.Pointed
import           Data.Semigroup.Foldable
import qualified Control.Alternative.Free       as Alt
import qualified Control.Applicative.Free       as Ap
import qualified Control.Applicative.Free.Fast  as FAF
import qualified Control.Applicative.Free.Final as FA
import qualified Data.Map.NonEmpty              as NEM

-- | An 'Interpret' lets us move in and out of the "enhanced" 'Functor'.
--
-- For example, @'Free' f@ is @f@ enhanced with monadic structure.  We get:
--
-- @
-- 'inject'    :: f a -> 'Free' f a
-- 'interpret' :: 'Monad' m => (forall x. f x -> m x) -> 'Free' f a -> m a
-- @
--
-- 'inject' will let us use our @f@ inside the enhanced @'Free' f@.
-- 'interpret' will let us "extract" the @f@ from a @'Free' f@ if
-- we can give an /interpreting function/ that interprets @f@ into some
-- target 'Monad'.
--
-- The type family 'C' tells us the typeclass constraint of the "target"
-- functor.  For 'Free', it is 'Monad', but for other 'Interpret'
-- instances, we might have other constraints.
--
-- We enforce that:
--
-- @
-- 'interpret' id . 'inject' == id
-- @
--
-- That is, if we lift a value into our structure, then immediately
-- interpret it out as itself, it should lave the value unchanged.
class Inject t => Interpret t where
    -- | The constraint on the target context of 'interpret'.  It's
    -- basically the constraint that allows you to "exit" or "run" an
    -- 'Interpret'.
    type C t :: (Type -> Type) -> Constraint

    -- | Remove the @f@ out of the enhanced @t f@ structure, provided that
    -- @f@ satisfies the necessary constraints.  If it doesn't, it needs to
    -- be properly 'interpret'ed out.
    retract :: C t f => t f ~> f
    retract = interpret id

    -- | Given an "interpeting function" from @f@ to @g@, interpret the @f@
    -- out of the @t f@ into a final context @g@.
    interpret :: C t g => (f ~> g) -> t f ~> g
    interpret f = retract . hmap f

    {-# MINIMAL retract | interpret #-}

-- | A convenient flipped version of 'interpret'.
forI
    :: (Interpret t, C t g)
    => t f a
    -> (f ~> g)
    -> g a
forI x f = interpret f x

-- | Useful wrapper over 'interpret' to allow you to directly extract
-- a value @b@ out of the @t f a@, if you can convert @f x@ into @b@.
--
-- Note that depending on the constraints on the interpretation of @t@, you
-- may have extra constraints on @b@.
--
-- *    If @'C' t@ is 'Unconstrained', there are no constraints on @b@
-- *    If @'C' t@ is 'Apply', @b@ needs to be an instance of 'Semigroup'
-- *    If @'C' t@ is 'Applicative', @b@ needs to be an instance of 'Monoid'
--
-- For some constraints (like 'Monad'), this will not be usable.
--
-- @
-- -- get the length of the @Map String@ in the 'Step'.
-- 'collectI' length
--      :: Step (Map String) Bool
--      -> Int
-- @
getI
    :: (Interpret t, C t (Const b))
    => (forall x. f x -> b)
    -> t f a
    -> b
getI f = getConst . interpret (Const . f)

-- | Useful wrapper over 'getI' to allow you to collect a @b@ from all
-- instances of @f@ inside a @t f a@.
--
-- This will work if @'C' t@ is 'Unconstrained', 'Apply', or 'Applicative'.
--
-- @
-- -- get the lengths of all @Map String@s in the 'Ap.Ap'.
-- 'collectI' length
--      :: Ap (Map String) Bool
--      -> [Int]
-- @
collectI
    :: (Interpret t, C t (Const [b]))
    => (forall x. f x -> b)
    -> t f a
    -> [b]
collectI f = getI ((:[]) . f)

-- | A free 'Functor'
instance Interpret Coyoneda where
    type C Coyoneda = Functor

    retract                    = lowerCoyoneda
    interpret f (Coyoneda g x) = g <$> f x

-- | A free 'Applicative'
instance Interpret Ap.Ap where
    type C Ap.Ap = Applicative

    retract   = \case
      Ap.Pure x  -> pure x
      Ap.Ap x xs -> x <**> retract xs
    interpret = Ap.runAp

-- | A free 'Plus'
instance Interpret ListF where
    type C ListF = Plus

    retract     = foldr (<!>) zero . runListF
    interpret f = foldr ((<!>) . f) zero . runListF

-- | A free 'Alt'
instance Interpret NonEmptyF where
    type C NonEmptyF = Alt

    retract     = asum1 . runNonEmptyF
    interpret f = asum1 . fmap f . runNonEmptyF

-- | Technically, 'C' is over-constrained: we only need @'zero' :: f a@,
-- but we don't really have that typeclass in any standard hierarchies.  We
-- use 'Plus' here instead, but we never use '<!>'.  This would only go
-- wrong in situations where your type supports 'zero' but not '<!>', like
-- instances of 'Control.Monad.Fail.MonadFail' without
-- 'Control.Monad.MonadPlus'.
instance Interpret MaybeF where
    type C MaybeF = Plus

    retract     = fromMaybe zero . runMaybeF
    interpret f = maybe zero f . runMaybeF

instance Interpret Step where
    type C Step = Unconstrained

    retract (Step _ x)     = x
    interpret f (Step _ x) = f x

instance Interpret Steps where
    type C Steps = Alt

    retract     = asum1 . getSteps
    interpret f = asum1 . NEM.map f . getSteps

-- | A free 'Alternative'
instance Interpret Alt.Alt where
    type C Alt.Alt = Alternative

    interpret = Alt.runAlt

-- | A free 'Monad'
instance Interpret Free where
    type C Free = Monad

    retract   = retractFree
    interpret = interpretFree

-- | A free 'Bind'
instance Interpret Free1 where
    type C Free1 = Bind

    retract   = retractFree1
    interpret = interpretFree1

-- | A free 'Applicative'
instance Interpret FA.Ap where
    type C FA.Ap = Applicative

    retract   = FA.retractAp
    interpret = FA.runAp

-- | A free 'Applicative'
instance Interpret FAF.Ap where
    type C FAF.Ap = Applicative

    retract   = FAF.retractAp
    interpret = FAF.runAp

-- | A free 'Unconstrained'
instance Interpret IdentityT where
    type C IdentityT = Unconstrained

    retract = coerce
    interpret f = f . runIdentityT

-- | A free 'Pointed'
instance Interpret Lift where
    type C Lift = Pointed

    retract   = elimLift point id
    interpret = elimLift point

-- | A free 'Pointed'
instance Interpret MaybeApply where
    type C MaybeApply = Pointed

    retract     = either id point . runMaybeApply
    interpret f = either f point . runMaybeApply

instance Interpret Backwards where
    type C Backwards = Unconstrained

    retract     = forwards
    interpret f = f . forwards

instance Interpret WrappedApplicative where
    type C WrappedApplicative = Unconstrained

    retract     = unwrapApplicative
    interpret f = f . unwrapApplicative

-- | A free 'MonadReader', but only when applied to a 'Monad'.
instance Interpret (ReaderT r) where
    type C (ReaderT r) = MonadReader r

    retract     x = runReaderT x =<< ask
    interpret f x = f . runReaderT x =<< ask

instance Interpret Reverse where
    type C Reverse = Unconstrained

    retract     = getReverse
    interpret f = f . getReverse

-- | A constraint on @a@ for both @c a@ and @d a@.  Requiring @'AndC'
-- 'Show' 'Eq' a@ is the same as requiring @('Show' a, 'Eq' a)@.
class (c a, d a) => AndC c d a
instance (c a, d a) => AndC c d a

instance (Interpret s, Interpret t) => Interpret (ComposeT s t) where
    type C (ComposeT s t) = AndC (C s) (C t)

    retract     = interpret retract . getComposeT
    interpret f = interpret (interpret f) . getComposeT

-- | Never uses 'inject'
instance Interpret t => Interpret (HLift t) where
    type C (HLift t) = C t
    retract = \case
      HPure  x -> x
      HOther x -> retract x
    interpret f = \case
      HPure  x -> f x
      HOther x -> interpret f x

-- | Never uses 'inject'
instance Interpret t => Interpret (HFree t) where
    type C (HFree t) = C t
    retract = \case
      HReturn x -> x
      HJoin   x -> interpret retract x
