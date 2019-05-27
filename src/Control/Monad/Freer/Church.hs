{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE ViewPatterns              #-}

module Control.Monad.Freer.Church (
    Free(..), reFree
  , Comp(.., Comp, unComp), comp
  ) where

import           Control.Applicative
import           Control.Monad
import           Data.Functor.Classes
import           Text.Read
import qualified Control.Monad.Free             as M

-- | Church-encoded Freer monad
newtype Free f a = Free
    { runFree :: forall r. (a -> r) -> (forall s. f s -> (s -> r) -> r) -> r
    }

instance Functor (Free f) where
    fmap f x = Free $ \p b -> runFree x (p . f) b

instance Applicative (Free f) where
    pure  = return
    (<*>) = ap

instance Monad (Free f) where
    return x = Free $ \p _ -> p x
    x >>= f  = Free $ \p b -> runFree x (\y -> runFree (f y) p b) b

instance M.MonadFree f (Free f) where
    wrap x = Free $ \p b -> b x $ \y -> runFree y p b

instance Foldable f => Foldable (Free f) where
    foldMap f x = runFree x f (flip foldMap)

instance Traversable f => Traversable (Free f) where
    traverse f x = runFree x (fmap pure . f) $ \xs g -> M.wrap <$> traverse g xs

instance (Functor f, Eq1 f) => Eq1 (Free f) where
    liftEq eq x y = liftEq @(M.Free f) eq (reFree x) (reFree y)

instance (Functor f, Ord1 f) => Ord1 (Free f) where
    liftCompare c x y = liftCompare @(M.Free f) c (reFree x) (reFree y)

instance (Functor f, Eq1 f, Eq a) => Eq (Free f a) where
    (==) = eq1

instance (Functor f, Ord1 f, Ord a) => Ord (Free f a) where
    compare = compare1

-- | Convert a @'Free' f@ into any instance of @'MonadFree' f@.
reFree
    :: (M.MonadFree f m, Functor f)
    => Free f a
    -> m a
reFree x = runFree x pure $ \y g -> M.wrap (g <$> y)

-- | A version of ':.:' and 'Data.Functor.Compose.Compose' that allows for
-- an 'HBifunctor' instance.
--
-- It is slightly less performant.  Using 'comp . unComp' every once in
-- a while will concretize a 'Comp' value (if you have @'Functor' f@) and
-- remove some indirection if you have a lot of chained operations.
--
-- The "free monoid" over 'Comp' is 'Free'.
data Comp f g a =
    forall x. f x :>>= (x -> g a)

instance Functor g => Functor (Comp f g) where
    fmap f (x :>>= h) = x :>>= (fmap f . h)

instance (Applicative f, Applicative g) => Applicative (Comp f g) where
    pure x = pure () :>>= (pure . const x)
    (x :>>= f) <*> (y :>>= g) = ((,) <$> x <*> y)
                           :>>= (\(x', y') -> f x' <*> g y')
    liftA2 h (x :>>= f) (y :>>= g)
            = ((,) <$> x <*> y)
         :>>= (\(x', y') -> liftA2 h (f x') (g y'))

instance (Foldable f, Foldable g) => Foldable (Comp f g) where
    foldMap f (x :>>= h) = foldMap (foldMap f . h) x

instance (Traversable f, Traversable g) => Traversable (Comp f g) where
    traverse f (x :>>= h) = (:>>= id)
                        <$> traverse (traverse f . h) x

instance (Alternative f, Alternative g) => Alternative (Comp f g) where
    empty = empty :>>= id
    (x :>>= f) <|> (y :>>= g) = ((f <$> x) <|> (g <$> y)) :>>= id

instance (Functor f, Show1 f, Show1 g) => Show1 (Comp f g) where
    liftShowsPrec sp sl d (Comp x) =
        showsUnaryWith (liftShowsPrec sp' sl') "Comp" d x
      where
        sp' = liftShowsPrec sp sl
        sl' = liftShowList sp sl

instance (Functor f, Show1 f, Show1 g, Show a) => Show (Comp f g a) where
    showsPrec = liftShowsPrec showsPrec showList

instance (Functor f, Read1 f, Read1 g) => Read1 (Comp f g) where
    liftReadPrec rp rl = readData $
        readUnaryWith (liftReadPrec rp' rl') "Comp" Comp
      where
        rp' = liftReadPrec rp rl
        rl' = liftReadListPrec rp rl

instance (Functor f, Read1 f, Read1 g, Read a) => Read (Comp f g a) where
    readPrec = readPrec1
    readListPrec = readListPrecDefault
    readList = readListDefault

instance (Functor f, Eq1 f, Eq1 g) => Eq1 (Comp f g) where
    liftEq eq (Comp x) (Comp y) = liftEq (liftEq eq) x y

instance (Functor f, Ord1 f, Ord1 g) => Ord1 (Comp f g) where
    liftCompare c (Comp x) (Comp y) = liftCompare (liftCompare c) x y

instance (Functor f, Eq1 f, Eq1 g, Eq a) => Eq (Comp f g a) where
    (==) = eq1

instance (Functor f, Ord1 f, Ord1 g, Ord a) => Ord (Comp f g a) where
    compare = compare1

-- | "Smart constructor" for 'Comp' that doesn't require @'Functor' f@.
comp :: f (g a) -> Comp f g a
comp = (:>>= id)

pattern Comp :: Functor f => f (g a) -> Comp f g a
pattern Comp { unComp } <- ((\case x :>>= f -> f <$> x)->unComp)
  where
    Comp x = comp x
{-# COMPLETE Comp #-}
