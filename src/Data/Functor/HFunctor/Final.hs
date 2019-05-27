{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DefaultSignatures      #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}

module Data.Functor.HFunctor.Final (
    Final(..)
  , fromFinal, toFinal
  , FreeOf(..)
  , hoistFinalC
  , liftFinal0
  , liftFinal1
  , liftFinal2
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Monad
import           Control.Monad.Freer.Church
import           Control.Monad.Reader
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Data.Constraint.Trivial
import           Data.Functor.Coyoneda
import           Data.Functor.HFunctor
import           Data.Functor.Plus
import           Data.Pointed
import qualified Control.Alternative.Free      as Alt
import qualified Control.Applicative.Free.Fast as FAF

-- | A simple way to inject/reject into any eventual typeclass.
--
-- In a way, this is the "ultimate" 'Interpret' instance.  You can use this
-- to inject an @f@ into a free structure of any typeclass.  If you want
-- @f@ to have a 'Monad' instance, for example, just use
--
-- @
-- 'inject' :: f a -> 'Final' 'Monad' f a
-- @
--
-- When you want to eventually interpret out the data, use:
--
-- @
-- 'interpret' :: (f '~>' g) -> 'Final' c f a -> g a
-- @
--
-- Essentially, @'Final' c@ is the "free c".  @'Final' 'Monad'@ is the free
-- 'Monad', etc.
--
-- Note that this doesn't have instances for /all/ the typeclasses you
-- could lift things into; you probably have to define your own if you want
-- to use @'Final' c@ as an /instance/ of @c@ (using 'liftFinal0',
-- 'liftFinal1', 'liftFinal2' for help).
newtype Final c f a = Final
    { runFinal :: forall g. c g => (forall x. f x -> g x) -> g a }

-- | Lift an action into a 'Final'.
liftFinal0
    :: (forall g. c g => g a)
    -> Final c f a
liftFinal0 x = Final $ \_ -> x

-- | Map the action in a 'Final'.
liftFinal1
    :: (forall g. c g => g a -> g b)
    -> Final c f a
    -> Final c f b
liftFinal1 f x = Final $ \r -> f (runFinal x r)

-- | Merge two 'Final' actions.
liftFinal2
    :: (forall g. c g => g a -> g b -> g d)
    -> Final c f a
    -> Final c f b
    -> Final c f d
liftFinal2 f x y = Final $ \r -> f (runFinal x r) (runFinal y r)

instance Functor (Final Functor f) where
    fmap f = liftFinal1 (fmap f)

instance Functor (Final Apply f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Apply f) where
    (<.>) = liftFinal2 (<.>)
    liftF2 f = liftFinal2 (liftF2 f)

instance Functor (Final Applicative f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Applicative f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
instance Applicative (Final Applicative f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)

instance Functor (Final Alternative f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Alternative f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
instance Applicative (Final Alternative f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)
instance Alternative (Final Alternative f) where
    empty = liftFinal0 empty
    (<|>) = liftFinal2 (<|>)

instance Functor (Final Monad f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Monad f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
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

instance Pointed (Final Pointed f) where
    point x = liftFinal0 (point x)

instance Functor (Final (MonadReader r) f) where
    fmap f = liftFinal1 (fmap f)
instance Applicative (Final (MonadReader r) f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)
instance Apply (Final (MonadReader r) f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
instance Monad (Final (MonadReader r) f) where
    return x = liftFinal0 (return x)
    x >>= f  = Final $ \r -> do
      y <- runFinal x r
      runFinal (f y) r
instance MonadReader r (Final (MonadReader r) f) where
    ask     = liftFinal0 ask
    local f = liftFinal1 (local f)

instance Functor (Final Alt f) where
    fmap f = liftFinal1 (fmap f)
instance Alt (Final Alt f) where
    (<!>) = liftFinal2 (<!>)

instance Functor (Final Plus f) where
    fmap f = liftFinal1 (fmap f)
instance Alt (Final Plus f) where
    (<!>) = liftFinal2 (<!>)
instance Plus (Final Plus f) where
    zero = liftFinal0 zero

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
-- toFinal :: 'Free' f '~>' 'Final' 'Monad' f
-- toFinal :: 'Lift' f '~>' 'Final' 'Pointed' f
-- toFinal :: 'ListF' f '~>' 'Final' 'Plus' f
-- @
--
-- Note that the instance of @c@ for @'Final' c@ must be defined.
--
-- This operation can potentially /forget/ structure in @t@.  For example,
-- we have:
--
-- @
-- 'toFinal' :: 'Steps' f ~> 'Final' 'Alt' f
-- @
--
-- In this process, we lose the "positional" structure of 'Steps'.
--
-- In the case where 'toFinal' doesn't lose any information, this will form
-- an isomorphism with 'fromFinal', and @t@ is known as the "Free @c@".
-- For such a situation, @t@ will have a 'FreeOf' instance.
toFinal :: (Interpret t, C t (Final c f)) => t f ~> Final c f
toFinal = interpret inject

-- | "Concretize" a 'Final'.

-- @
-- fromFinal :: 'Final' 'Functor' f '~>' 'Coyoneda' f
-- fromFinal :: 'Final' 'Applicative' f '~>' 'Ap' f
-- fromFinal :: 'Final' 'Alternative' f '~>' 'Alt' f
-- fromFinal :: 'Final' 'Monad' f '~>' 'Free' f
-- fromFinal :: 'Final' 'Pointed' f '~>' 'Lift' f
-- fromFinal :: 'Final' 'Plus' f '~>' 'ListF' f
-- @
--
-- This can be useful because 'Final' doesn't have a concrete structure
-- that you can pattern match on and inspect, but @t@ might.
--
-- In the case that this forms an isomorphism with 'toFinal', the @t@ will
-- have an instance of 'FreeOf'.
fromFinal :: (Interpret t, c (t f)) => Final c f ~> t f
fromFinal = interpret inject

-- | A typeclass associating a free structure with the typeclass it is free
-- on.
--
-- This essentially lists instances of 'Interpret' where a "trip" through
-- 'Final' will leave it unchanged.
--
-- @
-- 'fromFree' . 'toFree' == id
-- 'toFree' . 'fromFree' == id
-- @
--
-- This can be useful because 'Final' doesn't have a concrete structure
-- that you can pattern match on and inspect, but @t@ might.  This lets you
-- work on a concrete structure if you desire.
class Interpret t => FreeOf c t | t -> c where
    fromFree :: t f ~> Final c f
    toFree   :: Functor f => Final c f ~> t f

    default fromFree :: C t (Final c f) => t f ~> Final c f
    fromFree = toFinal
    default toFree :: c (t f) => Final c f ~> t f
    toFree = fromFinal

instance FreeOf Functor Coyoneda
instance FreeOf Applicative Ap
instance FreeOf Applicative FAF.Ap
instance FreeOf Alternative Alt.Alt
instance FreeOf Monad Free
instance FreeOf Pointed Lift
instance FreeOf Pointed MaybeApply
instance FreeOf Alt NonEmptyF
instance FreeOf Plus ListF
instance FreeOf Unconstrained IdentityT
