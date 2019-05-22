{-# LANGUAGE ConstraintKinds   #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE TypeFamilies      #-}

module Data.Functor.Combinator.Final (
    Final(..)
  , hoistFinalC
  , liftFinal0
  , liftFinal1
  , liftFinal2
  ) where

import           Control.Applicative
import           Control.Monad
import           Data.Functor.Combinator.Class

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
