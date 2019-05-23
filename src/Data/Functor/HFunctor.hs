{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableSuperClasses #-}

module Data.Functor.HFunctor (
    HFunctor(..)
  , Interpret(..)
  , Trivial
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
import           Data.Functor.Coyoneda
import           Data.Functor.HFunctor.Internal
import           Data.Functor.Plus
import           Data.Functor.Reverse
import           Data.Kind
import           Data.Pointed
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

instance Interpret Coyoneda where
    type C Coyoneda = Functor
    inject  = liftCoyoneda
    retract = lowerCoyoneda
    interpret f (Coyoneda g x) = g <$> f x

instance Interpret Ap where
    type C Ap = Applicative
    inject    = liftAp
    interpret = runAp

instance Interpret ListF where
    type C ListF = Plus
    inject = ListF . (:[])
    retract = foldr (<!>) zero . runListF

instance Interpret Step where
    type C Step = Trivial
    inject = Step 0
    retract (Step _ x)     = x
    interpret f (Step _ x) = f x

instance Interpret Steps where
    type C Steps = Alt
    inject      = Steps . NEM.singleton 0
    retract     = NEM.foldr1 (<!>) . getSteps
    interpret f = NEM.foldr1 (<!>) . NEM.map f . getSteps

instance Interpret Alt.Alt where
    type C Alt.Alt = Alternative
    inject = Alt.liftAlt
    interpret = Alt.runAlt

instance Interpret Free where
    type C Free = Monad

    inject x = Free $ \p b -> b x p
    retract x = runFree x pure (>>=)
    interpret f x = runFree x pure ((>>=) . f)

instance Interpret FA.Ap where
    type C FA.Ap = Applicative
    inject = FA.liftAp
    retract = FA.retractAp
    interpret = FA.runAp

instance Interpret FAF.Ap where
    type C FAF.Ap = Applicative
    inject = FAF.liftAp
    retract = FAF.retractAp
    interpret = FAF.runAp

class Trivial c
instance Trivial c

instance Interpret IdentityT where
    type C IdentityT = Trivial
    inject = coerce
    retract = coerce
    interpret f = f . runIdentityT

instance Interpret Lift where
    type C Lift = Pointed
    inject = Other
    retract = elimLift point id
    interpret f = elimLift point f

instance Interpret Backwards where
    type C Backwards = Trivial
    inject = Backwards
    retract = forwards
    interpret f = f . forwards

instance Interpret (ReaderT r) where
    type C (ReaderT r) = MonadReader r
    inject = ReaderT . const
    retract x = runReaderT x =<< ask
    interpret f x = f . runReaderT x =<< ask

instance Interpret Reverse where
    type C Reverse = Trivial
    inject = Reverse
    retract = getReverse
    interpret f = f . getReverse

class (c a, d a) => AndC c d a
instance (c a, d a) => AndC c d a

instance (Interpret s, Interpret t) => Interpret (ComposeT s t) where
    type C (ComposeT s t) = AndC (C s) (C t)
    inject = ComposeT . inject . inject
    retract = interpret retract . getComposeT
    interpret f = interpret (interpret f) . getComposeT
