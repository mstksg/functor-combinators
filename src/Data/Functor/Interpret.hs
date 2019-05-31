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
module Data.Functor.Interpret (
    HFunctor(..)
  , Interpret(..), interpretFor
  , extractI
  , getI
  , collectI
  , AndC
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards
import           Control.Applicative.Free
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
import           Data.Copointed
import           Data.Functor.Bind
import           Data.Functor.Coyoneda
import           Data.Functor.HFunctor.Internal
import           Data.Functor.Plus
import           Data.Functor.Reverse
import           Data.Kind
import           Data.List.NonEmpty             (NonEmpty(..))
import           Data.Maybe
import           Data.Pointed
import           Data.Semigroup.Foldable
import qualified Control.Alternative.Free       as Alt
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
class HFunctor t => Interpret t where
    -- | The constraint on the target context of 'interpret'.
    type C t :: (Type -> Type) -> Constraint

    -- | Lift an @f@ into the enhanced @t f@ structure.
    -- Analogous to 'lift' from 'MonadTrans'.
    inject  :: f ~> t f

    -- | Remove the @f@ out of the enhanced @t f@ structure, provided that
    -- @f@ satisfies the necessary constraints.  If it doesn't, it needs to
    -- be properly 'interpret'ed out.
    retract :: C t f => t f ~> f
    retract = interpret id

    -- | Given an "interpeting function" from @f@ to @g@, interpret the @f@
    -- out of the @t f@ into a final context @g@.
    interpret :: C t g => (f ~> g) -> t f ~> g
    interpret f = retract . hmap f

    {-# MINIMAL inject, (retract | interpret) #-}

-- | A convenient flipped version of 'interpret'.
interpretFor
    :: (Interpret t, C t g)
    => t f a
    -> (f ~> g)
    -> g a
interpretFor x f = interpret f x

-- | Useful wrapper over 'retract' to allow you to directly extract an @a@
-- from a @t f a@, if @f@ is a valid retraction from @t@, and @f@ is an
-- instance of 'Copointed'.
--
-- Useful @f@s include 'Data.Functor.Identity' or related newtype wrappers from
-- base:
--
-- @
-- 'extractI'
--     :: ('Interpret' t, 'C' t 'Data.Functor.Identity')
--     => t 'Data.Functor.Identity' a
--     -> a
-- @
extractI :: (Interpret t, C t f, Copointed f) => t f a -> a
extractI = copoint . retract

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
--      -> [Int]
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
-- -- get the lengths of all @Map String@s in the 'Ap'.
-- 'collectI' length
--      :: Ap (Map String) Bool
--      -> [Int]
-- @
collectI
    :: (Interpret t, C t (Const [b]))
    => (forall x. f x -> b)
    -> t f a
    -> [b]
collectI f = getConst . interpret (Const . (:[]) . f)

-- | A free 'Functor'
instance Interpret Coyoneda where
    type C Coyoneda = Functor
    inject  = liftCoyoneda
    retract = lowerCoyoneda
    interpret f (Coyoneda g x) = g <$> f x

-- | A free 'Applicative'
instance Interpret Ap where
    type C Ap = Applicative
    inject    = liftAp
    interpret = runAp

-- | A free 'Plus'
instance Interpret ListF where
    type C ListF = Plus
    inject = ListF . (:[])
    retract = foldr (<!>) zero . runListF
    interpret f = foldr ((<!>) . f) zero . runListF

-- | A free 'Alt'
instance Interpret NonEmptyF where
    type C NonEmptyF = Alt
    inject = NonEmptyF . (:| [])
    retract = asum1 . runNonEmptyF
    interpret f = asum1 . fmap f . runNonEmptyF

-- | Technically, 'C' is over-constrained: we only need @'zero' :: f a@,
-- but we don't really have that typeclass in any standard hierarchies.  We
-- use 'Plus' here instead, but we never use '<!>'.  This would only go
-- wrong in situations where your type supports 'zero' but not '<!>', like
-- instances of 'Control.Monad.Fail.MonadFail' without
-- 'Control.Monad.MonadPlus'.
instance Interpret MaybeF where
    type C MaybeF = Plus
    inject = MaybeF . Just
    retract = fromMaybe zero . runMaybeF
    interpret f = maybe zero f . runMaybeF

instance Interpret Step where
    type C Step = Unconstrained
    inject = Step 0
    retract (Step _ x)     = x
    interpret f (Step _ x) = f x

instance Interpret Steps where
    type C Steps = Alt
    inject      = Steps . NEM.singleton 0
    retract     = asum1 . getSteps
    interpret f = asum1 . NEM.map f . getSteps

-- | A free 'Alternative'
instance Interpret Alt.Alt where
    type C Alt.Alt = Alternative
    inject = Alt.liftAlt
    interpret = Alt.runAlt

-- | A free 'Monad'
instance Interpret Free where
    type C Free = Monad

    inject    = liftFree
    retract   = retractFree
    interpret = interpretFree

-- | A free 'Bind'
instance Interpret Free1 where
    type C Free1 = Bind

    inject    = liftFree1
    retract   = retractFree1
    interpret = interpretFree1
    -- inject = (`Free1` pure)
    -- retract f1@(Free1 x _) = case fromFree (toFree f1) of
    --   L1 (Identity y) -> y <$ x
    --   R1 y            -> retract y
    -- interpret f = go
    --   where
    --     go f1@(Free1 x _) = case fromFree (toFree f1) of
    --       L1 (Identity y) -> y <$ f x
    --       R1 y            -> go y

-- | A free 'Applicative'
instance Interpret FA.Ap where
    type C FA.Ap = Applicative
    inject = FA.liftAp
    retract = FA.retractAp
    interpret = FA.runAp

-- | A free 'Applicative'
instance Interpret FAF.Ap where
    type C FAF.Ap = Applicative
    inject = FAF.liftAp
    retract = FAF.retractAp
    interpret = FAF.runAp

-- | A free 'Unconstrained'
instance Interpret IdentityT where
    type C IdentityT = Unconstrained
    inject = coerce
    retract = coerce
    interpret f = f . runIdentityT

-- | A free 'Pointed'
instance Interpret Lift where
    type C Lift = Pointed
    inject = Other
    retract = elimLift point id
    interpret f = elimLift point f

-- | A free 'Pointed'
instance Interpret MaybeApply where
    type C MaybeApply = Pointed
    inject = MaybeApply . Left
    retract = either id point . runMaybeApply
    interpret f = either f point . runMaybeApply

instance Interpret Backwards where
    type C Backwards = Unconstrained
    inject = Backwards
    retract = forwards
    interpret f = f . forwards

instance Interpret WrappedApplicative where
    type C WrappedApplicative = Unconstrained
    inject = WrapApplicative
    retract = unwrapApplicative
    interpret f = f . unwrapApplicative

-- | A free 'MonadReader', but only when applied to a 'Monad'.
instance Interpret (ReaderT r) where
    type C (ReaderT r) = MonadReader r
    inject = ReaderT . const
    retract x = runReaderT x =<< ask
    interpret f x = f . runReaderT x =<< ask

instance Interpret Reverse where
    type C Reverse = Unconstrained
    inject = Reverse
    retract = getReverse
    interpret f = f . getReverse

-- | A constraint on @a@ for both @c a@ and @d a@.  Requiring @'AndC'
-- 'Show' 'Eq' a@ is the same as requiring @('Show' a, 'Eq' a)@.
class (c a, d a) => AndC c d a
instance (c a, d a) => AndC c d a

instance (Interpret s, Interpret t) => Interpret (ComposeT s t) where
    type C (ComposeT s t) = AndC (C s) (C t)
    inject = ComposeT . inject . inject
    retract = interpret retract . getComposeT
    interpret f = interpret (interpret f) . getComposeT
