{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Data.Functor.HFunctor.Final (
    Final(..)
  , fromFinal, toFinal
  , hoistFinalC
  , liftFinal0
  , liftFinal1
  , liftFinal2
  ) where

import           Control.Applicative
import           Control.Applicative.Step
import           Control.Monad
import           Control.Natural
import           Data.Functor.HFunctor

-- | A simple way to inject/reject into any eventual typeclass.
-- Essentially, @'Final' c@ is the "free c".  @'Final' 'Monad'@ is the free
-- 'Monad', etc.
--
-- Useful for lifting a functor @f@ into arbitrary structure given by
-- a typeclass.
--
-- Note that this doesn't have instances for all the typeclasses; you
-- probably have to define your own if you want to use @'Final' c@ as an
-- /instance/ of @c@ (using 'liftFinal0', 'liftFinal1', 'liftFinal2' for
-- help).  This is mostly meant to be usable as a final 'Interpret', with
--
-- @
-- 'inject'    :: f a -> 'Final' c f a
-- 'interpret' :: (f '~>' g) -> 'Final' c f a -> g a
-- @
newtype Final c f a = Final
    { runFinal :: forall g. c g => (forall x. f x -> g x) -> g a }

liftFinal0
    :: (forall g. c g => g a)
    -> Final c f a
liftFinal0 x = Final $ \_ -> x

liftFinal1
    :: (forall g. c g => g a -> g b)
    -> Final c f a
    -> Final c f b
liftFinal1 f x = Final $ \r -> f (runFinal x r)

liftFinal2
    :: (forall g. c g => g a -> g b -> g d)
    -> Final c f a
    -> Final c f b
    -> Final c f d
liftFinal2 f x y = Final $ \r -> f (runFinal x r) (runFinal y r)

instance Functor (Final Functor f) where
    fmap f = liftFinal1 (fmap f)

instance Functor (Final Applicative f) where
    fmap f = liftFinal1 (fmap f)

instance Applicative (Final Applicative f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)

instance Functor (Final Alternative f) where
    fmap f = liftFinal1 (fmap f)

instance Applicative (Final Alternative f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)

instance Alternative (Final Alternative f) where
    empty = liftFinal0 empty
    (<|>) = liftFinal2 (<|>)

instance Functor (Final Monad f) where
    fmap f = liftFinal1 (fmap f)

instance Applicative (Final Monad f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)

instance Monad (Final Monad f) where
    return x = liftFinal0 (return x)
    x >>= f  = Final $ \r -> do
      y <- runFinal x r
      runFinal (f y) r

instance Functor (Final MonadPlus f) where
    fmap f = liftFinal1 (fmap f)

instance Applicative (Final MonadPlus f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)

instance Monad (Final MonadPlus f) where
    return x = liftFinal0 (return x)
    x >>= f  = Final $ \r -> do
      y <- runFinal x r
      runFinal (f y) r

instance Alternative (Final MonadPlus f) where
    empty = liftFinal0 empty
    (<|>) = liftFinal2 (<|>)

instance MonadPlus (Final MonadPlus f) where
    mzero = liftFinal0 mzero
    mplus = liftFinal2 mplus

instance Functor (Final AccumNat f) where
    fmap f = liftFinal1 (fmap f)

instance Applicative (Final AccumNat f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)

instance AccumNat (Final AccumNat f) where
    stepWith n x = liftFinal0 (stepWith n x)
    step n = liftFinal0 (step n)

hoistFinalC
    :: (forall g x. (c g => g x) -> (d g => g x))
    -> Final c f a
    -> Final d f a
hoistFinalC f (Final x) = Final $ \r -> f (x (\y -> f (r y)))

instance HFunctor (Final c) where
    hmap f x = Final $ \r -> runFinal x (r . f)

instance Interpret (Final c) where
    type C (Final c) = c

    inject x = Final ($ x)
    retract x = runFinal x id
    interpret f x = runFinal x f

-- | "Finalize" an 'Interpret' instance.
--
-- @
-- toFinal :: 'Coyoneda' f '~>' 'Final' 'Functor' f
-- toFinal :: 'Ap' f '~>' 'Final' 'Applicative' f
-- toFinal :: 'Alt' f '~>' 'Final' 'Alternative' f
-- toFinal :: 'Control.Monad.Freer.Church.Free' f '~>' 'Final' 'Monad' f
-- @
--
-- Note that the instance of @c@ for @'Final' c@ must be defined.
--
-- Should form an isomorphism with 'fromFinal'
toFinal :: (Interpret t, C t (Final c f)) => t f ~> Final c f
toFinal = interpret inject

-- | "Concretize" a 'Final'.

-- @
-- toFinal :: 'Final' 'Functor' f '~>' 'Coyoneda' f
-- toFinal :: 'Final' 'Applicative' f '~>' 'Ap' f
-- toFinal :: 'Final' 'Alternative' f '~>' 'Alt' f
-- toFinal :: 'Final' 'Monad' f '~>' 'Control.Monad.Freer.Church.Free' f
-- @
--
-- Should form an isomorphism with 'toFinal'
fromFinal :: (Interpret t, c (t f)) => Final c f ~> t f
fromFinal = interpret inject