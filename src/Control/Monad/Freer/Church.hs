{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE FlexibleInstances         #-}
{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE KindSignatures            #-}
{-# LANGUAGE LambdaCase                #-}
{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE PatternSynonyms           #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE ScopedTypeVariables       #-}
{-# LANGUAGE TypeApplications          #-}
{-# LANGUAGE ViewPatterns              #-}

-- |
-- Module      : Control.Monad.Freer.Church
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- The church-encoded "Freer" Monad.  Basically provides the free monad in
-- a way that is compatible with 'Data.Functor.HFunctor.HFunctor' and
-- 'Data.Functor.HFunctor.Interpret', and 'GHC.Generisc.:.:' or
-- 'Data.Functor.Compose' in a way that is compatible with
-- 'Data.Functor.Tensor.HBifunctor' and 'Data.Functor.Tensor.Tensor' and
-- 'Data.Functor.Tensor.Monoidal'.
module Control.Monad.Freer.Church (
    Free(..), reFree
  , Free1(..), toFree, fromFree
  , Comp(.., Comp, unComp), comp
  ) where

import           Control.Applicative
import           Control.Monad
import           Control.Natural
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Identity
import           Data.Kind
import           Data.Semigroup.Foldable
import           Data.Semigroup.Traversable
import           GHC.Generics
import           Text.Read
import qualified Control.Monad.Free         as M

-- | A @'Free' f@ is @f@ enhanced with "sequential binding" capabilities.
-- It allows you to sequence multiple @f@s one after the other, and also to
-- determine "what @f@ to sequence" based on the result of the computation
-- so far.
--
-- Essentially, you can think of this as "giving @f@ a 'Monad' instance",
-- with all that that entails ('return', '>>=', etc.).
--
-- Lift @f@ into it with @'Data.Functor.HFunctor.inject' :: f a -> Free
-- f a@.  When you finally want to "use" it, you can interpret it into any
-- monadic context:
--
-- @
-- 'Data.Functor.HFunctor.interpret'
--     :: 'Monad' g
--     => (forall x. f x -> g x)
--     -> 'Free' f a
--     -> g a
-- @
--
-- Under the hood, this is the Church-encoded Freer monad.  It's
-- 'Control.Monad.Free.Free', or 'Control.Monad.Free.Church.F', but in
-- a way that is compatible with 'Data.Functor.HFunctor.HFunctor' and
-- 'Data.Functor.HFunctor.Interpret'.
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

-- | Convert a @'Free' f@ into any instance of @'M.MonadFree' f@.
reFree
    :: (M.MonadFree f m, Functor f)
    => Free f a
    -> m a
reFree x = runFree x pure $ \y g -> M.wrap (g <$> y)

data Free1 :: (Type -> Type) -> Type -> Type where
    Free1 :: f a -> (a -> Free f b) -> Free1 f b

toFree :: Free1 f ~> Free f
toFree (Free1 x g) = Free $ \p b -> b x $ \y -> runFree (g y) p b

(|+|) :: (f a -> b) -> (g a -> b) -> (f :+: g) a -> b
f |+| g = \case
  L1 x -> f x
  R1 y -> g y
infixr 5 |+|

fromFree :: forall f. Free f ~> (Identity :+: Free1 f)
fromFree x = runFree x (L1 . Identity) $ \y n -> R1 $
        Free1 y ((pure . runIdentity |+| toFree) . n)

instance Functor (Free1 f) where
    fmap f (Free1 x g) = Free1 x (fmap f . g)

instance Apply (Free1 f) where
    (<.>) = apDefault

instance Bind (Free1 f) where
    Free1 x g >>- f = Free1 x (toFree . f <=< g)

instance Foldable f => Foldable (Free1 f) where
    foldMap f (Free1 x g) = foldMap (foldMap f . g) x

instance Traversable f => Traversable (Free1 f) where
    traverse f (Free1 x g) = (`Free1` (pure . runIdentity |+| toFree))
                         <$> traverse (fmap fromFree . traverse f . g) x

instance Foldable1 f => Foldable1 (Free1 f) where
    foldMap1 f (Free1 x g) =
        foldMap1 ( (f . runIdentity |+| foldMap1 f)
                 . fromFree
                 . g
                 ) x

instance Traversable1 f => Traversable1 (Free1 f) where
    traverse1 f (Free1 x g) = (`Free1` id) <$> traverse1 (q . fromFree . g) x
      where
        q (L1 (Identity y)) = pure <$> f y
        q (R1 y           ) = fmap toFree . traverse1 f $ y

instance (Functor f, Eq1 f) => Eq1 (Free1 f) where
    liftEq eq x y = liftEq @(Free f) eq (toFree x) (toFree y)

instance (Functor f, Ord1 f) => Ord1 (Free1 f) where
    liftCompare c x y = liftCompare @(Free f) c (toFree x) (toFree y)

instance (Functor f, Eq1 f, Eq a) => Eq (Free1 f a) where
    (==) = eq1

instance (Functor f, Ord1 f, Ord a) => Ord (Free1 f a) where
    compare = compare1

-- | Functor composition.  @'Comp' f g a@ is equivalent to @f (g a)@, and
-- the 'Comp' pattern synonym is a way of getting the @f (g a)@ in
-- a @'Comp' f g a@.
--
-- For example, @'Maybe' ('IO' 'Bool')@ is @'Comp' 'Maybe' 'IO' 'Bool'@.
--
-- This is mostly useful for its typeclass instances: in particular,
-- 'Functor', 'Applicative', 'Data.Functor.Tensor.HBifunctor', and
-- 'Data.Functor.Tensor.Monoidal'.
--
-- This is essentially a version of 'GHC.Generics.:.:' and
-- 'Data.Functor.Compose.Compose' that allows for an
-- 'Data.Functor.Tensor.HBifunctor' instance.
--
-- It is slightly less performant.  Using @'comp' . 'unComp'@ every once in
-- a while will concretize a 'Comp' value (if you have @'Functor' f@)
-- and remove some indirection if you have a lot of chained operations.
--
-- The "free monoid" over 'Comp' is 'Free', and the "free semigroup" over
-- 'Comp' is 'Free1'.
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

-- | Pattern match on and construct a @'Comp' f g a@ as if it were @f
-- (g a)@.
pattern Comp :: Functor f => f (g a) -> Comp f g a
pattern Comp { unComp } <- ((\case x :>>= f -> f <$> x)->unComp)
  where
    Comp x = comp x
{-# COMPLETE Comp #-}
