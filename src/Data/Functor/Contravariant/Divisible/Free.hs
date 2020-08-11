-- |
-- Module      : Data.Functor.Contravariant.Divisible.Free
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides free structures for the various typeclasses of the 'Divisible'
-- hierarchy.
--
-- @since 0.3.0.0
module Data.Functor.Contravariant.Divisible.Free (
    Div(..)
  , hoistDiv, liftDiv, runDiv
  , divListF, listFDiv
  , Div1(..)
  , hoistDiv1, liftDiv1, toDiv, runDiv1
  , div1NonEmptyF, nonEmptyFDiv1
  , Dec(..)
  , hoistDec, liftDec, runDec
  , Dec1(..)
  , hoistDec1, liftDec1, toDec, runDec1
  ) where

import           Control.Applicative.ListF
import           Control.Natural
import           Data.Bifunctor
import           Data.Bifunctor.Assoc
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Coyoneda
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Invariant
import           Data.HFunctor
import           Data.HFunctor.Interpret
import           Data.Kind
import           Data.List.NonEmpty                   (NonEmpty(..))
import           Data.Void

-- | The free 'Divisible'.  Used to sequence multiple contravariant
-- consumers, splitting out the input across all consumers.
newtype Div f a = Div { unDiv :: ListF (Coyoneda f) a }

instance Contravariant (Div f) where
    contramap f (Div xs) = Div (contramap f xs)
instance Invariant (Div f) where
    invmap _ = contramap

instance Divise (Div f) where
    divise f (Div xs) (Div ys) = Div (divise f xs ys)
instance Divisible (Div f) where
    conquer = Div conquer
    divide  = divise

-- | 'Div' is isomorphic to 'ListF' for contravariant @f@.  This witnesses
-- one way of that isomorphism.
divListF :: forall f. Contravariant f => Div f ~> ListF f
divListF = mapListF (map lowerCoyoneda) . unDiv

-- | 'Div' is isomorphic to 'ListF' for contravariant @f@.  This witnesses
-- one way of that isomorphism.
listFDiv :: ListF f ~> Div f
listFDiv = Div . mapListF (map liftCoyoneda)

-- | Map over the undering context in a 'Div'.
hoistDiv :: forall f g. (f ~> g) -> Div f ~> Div g
hoistDiv f (Div (ListF xs)) = Div (ListF (map hc xs))
  where
    hc (Coyoneda g x) = Coyoneda g (f x)

-- | Inject a single action in @f@ into a @'Div' f@.
liftDiv :: f ~> Div f
liftDiv x = Div (ListF [liftCoyoneda x])

-- | Interpret a 'Div' into a context @g@, provided @g@ is 'Divisible'.
runDiv :: forall f g. Divisible g => (f ~> g) -> Div f ~> g
runDiv f = foldr go conquer . runListF . unDiv
  where
    go (Coyoneda g x) = divide (\y -> (y,y)) (contramap g (f x))

instance HFunctor Div where
    hmap = hoistDiv
instance Inject Div where
    inject = liftDiv
instance Divisible f => Interpret Div f where
    interpret = runDiv

-- | The free 'Divise': a non-empty version of 'Div'.
--
-- Note that @'Div1' f@ is essentially @'NonEmptyF'
-- ('Data.Functor.Contravariant.Coyoneda' f)@, or just @'NonEmptyF' f@ in the
-- case that @f@ is already contravariant.  However, it can be more
-- convenient to use if you are working with an intermediate @f@ that isn't
-- 'Contravariant'.
newtype Div1 f a = Div1 { unDiv1 :: NonEmptyF (Coyoneda f) a }

instance Contravariant (Div1 f) where
    contramap f (Div1 xs) = Div1 (contramap f xs)
instance Invariant (Div1 f) where
    invmap _ = contramap
instance Divise (Div1 f) where
    divise f (Div1 xs) (Div1 ys) = Div1 (divise f xs ys)

instance HFunctor Div1 where
    hmap = hoistDiv1
instance Inject Div1 where
    inject = liftDiv1
instance Divise f => Interpret Div1 f where
    interpret = runDiv1

-- | A 'Div1' is a "non-empty" 'Div'; this function "forgets" the non-empty
-- property and turns it back into a normal 'Div'.
toDiv :: Div1 f ~> Div f
toDiv = Div . toListF . unDiv1

-- | Map over the underlying context in a 'Div1'.
hoistDiv1 :: (f ~> g) -> Div1 f ~> Div1 g
hoistDiv1 f (Div1 xs) = Div1 (mapNonEmptyF (fmap hc) xs)
  where
    hc (Coyoneda g x) = Coyoneda g (f x)

-- | Inject a single action in @f@ into a @'Div' f@.
liftDiv1 :: f ~> Div1 f
liftDiv1 x = Div1 (NonEmptyF (liftCoyoneda x :| []))

-- | Interpret a 'Div1' into a context @g@, provided @g@ is 'Divise'.
runDiv1 :: Divise g => (f ~> g) -> Div1 f ~> g
runDiv1 f = foldr1 (divise (\y->(y,y))) . fmap go . runNonEmptyF . unDiv1
  where
    go (Coyoneda g x) = contramap g (f x)

-- | 'Div1' is isomorphic to 'NonEmptyF' for contravariant @f@.  This
-- witnesses one way of that isomorphism.
--
-- Be aware that this is essentially O(n^2).
div1NonEmptyF :: Contravariant f => Div1 f ~> NonEmptyF f
div1NonEmptyF = mapNonEmptyF (fmap lowerCoyoneda) . unDiv1

-- | 'Div1' is isomorphic to 'NonEmptyF' for contravariant @f@.  This
-- witnesses one way of that isomorphism.
--
-- This direction is O(n), unlike 'div1NonEmptyF'.
nonEmptyFDiv1 :: NonEmptyF f ~> Div1 f
nonEmptyFDiv1 = Div1 . mapNonEmptyF (fmap liftCoyoneda)

-- | The free 'Decide'.  Used to aggregate multiple possible consumers,
-- directing the input into an appropriate consumer.
data Dec :: (Type -> Type) -> Type -> Type where
    Lose   :: (a -> Void) -> Dec f a
    Choose :: (a -> Either b c) -> f b -> Dec f c -> Dec f a

instance Contravariant (Dec f) where
    contramap f = \case
      Lose   g      -> Lose   (g . f)
      Choose g x xs -> Choose (g . f) x xs
instance Invariant (Dec f) where
    invmap _ = contramap
instance Decide (Dec f) where
    decide f = \case
      Lose   g      -> contramap (either (absurd . g) id . f)
      Choose g x xs -> Choose (assoc . first g . f) x
                     . decide id xs
instance Conclude (Dec f) where
    conclude = Lose
instance HFunctor Dec where
    hmap = hoistDec
instance Inject Dec where
    inject = liftDec
instance Conclude f => Interpret Dec f where
    interpret = runDec

-- | Map over the underlying context in a 'Dec'.
hoistDec :: forall f g. (f ~> g) -> Dec f ~> Dec g
hoistDec f = go
  where
    go :: Dec f ~> Dec g
    go = \case
      Lose g -> Lose g
      Choose g x xs -> Choose g (f x) (go xs)

-- | Inject a single action in @f@ into a @'Dec' f@.
liftDec :: f ~> Dec f
liftDec x = Choose Left x (Lose id)

-- | Interpret a 'Dec' into a context @g@, provided @g@ is 'Conclude'.
runDec :: forall f g. Conclude g => (f ~> g) -> Dec f ~> g
runDec f = go
  where
    go :: Dec f ~> g
    go = \case
      Lose g -> conclude g
      Choose g x xs -> decide g (f x) (go xs)


-- | The free 'Decide': a non-empty version of 'Dec'.
data Dec1 :: (Type -> Type) -> Type -> Type where
    Dec1 :: (a -> Either b c) -> f b -> Dec f c -> Dec1 f a

-- | A 'Dec1' is a "non-empty" 'Dec'; this function "forgets" the non-empty
-- property and turns it back into a normal 'Dec'.
toDec :: Dec1 f a -> Dec f a
toDec (Dec1 f x xs) = Choose f x xs

instance Contravariant (Dec1 f) where
    contramap f (Dec1 g x xs) = Dec1 (g . f) x xs
instance Invariant (Dec1 f) where
    invmap _ = contramap
instance Decide (Dec1 f) where
    decide f (Dec1 g x xs) = Dec1 (assoc . first g . f) x
                           . decide id xs
                           . toDec
instance HFunctor Dec1 where
    hmap = hoistDec1
instance Inject Dec1 where
    inject = liftDec1
instance Decide f => Interpret Dec1 f where
    interpret = runDec1

-- | Map over the undering context in a 'Dec1'.
hoistDec1 :: forall f g. (f ~> g) -> Dec1 f ~> Dec1 g
hoistDec1 f (Dec1 g x xs) = Dec1 g (f x) (hoistDec f xs)

-- | Inject a single action in @f@ into a @'Dec1' f@.
liftDec1 :: f ~> Dec1 f
liftDec1 x = Dec1 Left x (Lose id)

-- | Interpret a 'Dec1' into a context @g@, provided @g@ is 'Decide'.
runDec1 :: Decide g => (f ~> g) -> Dec1 f ~> g
runDec1 f (Dec1 g x xs) = runDec1_ f g x xs

runDec1_
    :: forall f g a b c. Decide g
    => (f ~> g)
    -> (a -> Either b c)
    -> f b
    -> Dec f c
    -> g a
runDec1_ f = go
  where
    go :: (x -> Either y z) -> f y -> Dec f z -> g x
    go g x = \case
      Lose h        -> contramap (either id (absurd . h) . g) (f x)
      Choose h y ys -> decide g (f x) (go h y ys)
