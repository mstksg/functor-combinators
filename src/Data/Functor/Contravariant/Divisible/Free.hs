{-# LANGUAGE DerivingVia #-}

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
  Div (.., Conquer, Divide),
  hoistDiv,
  liftDiv,
  runDiv,
  divListF,
  listFDiv,
  Div1 (.., Div1_),
  hoistDiv1,
  liftDiv1,
  toDiv,
  runDiv1,
  div1NonEmptyF,
  nonEmptyFDiv1,
  Dec (..),
  hoistDec,
  liftDec,
  runDec,
  Dec1 (..),
  hoistDec1,
  liftDec1,
  toDec,
  runDec1,
) where

import Control.Applicative.ListF
import qualified Control.Monad.Trans.Compose as CT
import Control.Natural
import Data.Bifunctor
import Data.Bifunctor.Assoc
import Data.Foldable
import Data.Functor.Apply
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Conclude
import Data.Functor.Contravariant.Coyoneda
import qualified Data.Functor.Contravariant.Day as CD
import Data.Functor.Contravariant.Decide
import Data.Functor.Contravariant.Divise
import Data.Functor.Contravariant.Divisible
import Data.Functor.Invariant
import Data.Functor.Invariant.Inplicative
import Data.Functor.Invariant.Internative
import Data.HFunctor
import Data.HFunctor.HTraversable
import Data.HFunctor.Interpret
import Data.Kind
import Data.List.NonEmpty (NonEmpty (..))
import Data.Semigroup.Traversable
import Data.Void

-- | The free 'Divisible'.  Used to sequence multiple contravariant
-- consumers, splitting out the input across all consumers.
--
-- This type is essentially 'ListF'; the only reason why it has to exist
-- separately outside of 'ListF' is because the current typeclass hierarchy
-- isn't compatible with both the covariant 'Interpret' instance (requiring
-- 'Plus') and the contravariant 'Interpret' instance (requiring
-- 'Divisible').
--
-- The wrapping in 'Coyoneda' is also to provide a usable
-- 'Data.HBifunctor.Associative.Associative' instance for the contravariant
-- 'CD.Day'.
newtype Div f a = Div {unDiv :: [Coyoneda f a]}
  deriving (Contravariant, Divise, Divisible) via (ListF (Coyoneda f))
  deriving (HFunctor, Inject) via (CT.ComposeT ListF Coyoneda)

instance HTraversable Div where
  htraverse f (Div xs) = Div <$> traverse (htraverse f) xs

instance Invariant (Div f) where
  invmap _ = contramap

deriving via WrappedDivisible (Div f) instance Inply (Div f)
deriving via WrappedDivisible (Div f) instance Inplicative (Div f)

-- | Pattern matching on an empty 'Div'.
--
-- Before v0.3.3.0, this used to be the concrete constructor of 'Div'.
-- After, it is now an abstract pattern.
pattern Conquer :: Div f a
pattern Conquer = Div []

-- | Pattern matching on a non-empty 'Div', exposing the raw @f@ instead of
-- having it wrapped in a 'Coyoneda'.  This is the analogue of
-- 'Control.Applicative.Free.Pure' and essentially treats the "cons" of the
-- 'Div' as a contravariant day convolution.
--
-- Before v0.3.3.0, this used to be the concrete constructor of 'Div'.
-- After, it is now an abstract pattern.
pattern Divide :: (a -> (b, c)) -> f b -> Div f c -> Div f a
pattern Divide f x xs <- (divDay_ -> Just (CD.Day x xs f))
  where
    Divide f x (Div xs) = Div $ Coyoneda (fst . f) x : (map . contramap) (snd . f) xs

{-# COMPLETE Conquer, Divide #-}

divDay_ :: Div f a -> Maybe (CD.Day f (Div f) a)
divDay_ (Div []) = Nothing
divDay_ (Div (Coyoneda f x : xs)) = Just $ CD.Day x (Div xs) (\y -> (f y, y))

-- | 'Div' is isomorphic to 'ListF' for contravariant @f@.  This witnesses
-- one way of that isomorphism.
divListF :: forall f. Contravariant f => Div f ~> ListF f
divListF = ListF . map lowerCoyoneda . unDiv

-- | 'Div' is isomorphic to 'ListF' for contravariant @f@.  This witnesses
-- one way of that isomorphism.
listFDiv :: ListF f ~> Div f
listFDiv = Div . map liftCoyoneda . runListF

-- | Map over the undering context in a 'Div'.
hoistDiv :: forall f g. (f ~> g) -> Div f ~> Div g
hoistDiv = hmap

-- | Inject a single action in @f@ into a @'Div' f@.
liftDiv :: f ~> Div f
liftDiv = inject

-- | Interpret a 'Div' into a context @g@, provided @g@ is 'Divisible'.
runDiv :: forall f g. Divisible g => (f ~> g) -> Div f ~> g
runDiv f = foldr go conquer . unDiv
  where
    go (Coyoneda g x) = divide (\y -> (y, y)) (contramap g (f x))

instance Divisible f => Interpret Div f where
  interpret = runDiv

-- | The free 'Divise': a non-empty version of 'Div'.
--
-- This type is essentially 'NonEmptyF'; the only reason why it has to exist
-- separately outside of 'NonEmptyF' is because the current typeclass
-- hierarchy isn't compatible with both the covariant 'Interpret' instance
-- (requiring 'Plus') and the contravariant 'Interpret' instance (requiring
-- 'Divisible').
--
-- The wrapping in 'Coyoneda' is also to provide a usable
-- 'Data.HBifunctor.Associative.Associative' instance for the contravariant
-- 'CD.Day'.
newtype Div1 f a = Div1 {unDiv1 :: NonEmpty (Coyoneda f a)}
  deriving (Contravariant, Divise) via (NonEmptyF (Coyoneda f))
  deriving (HFunctor, Inject) via (CT.ComposeT NonEmptyF Coyoneda)

instance HTraversable Div1 where
  htraverse f (Div1 xs) = Div1 <$> traverse (htraverse f) xs

instance HTraversable1 Div1 where
  htraverse1 f (Div1 xs) = Div1 <$> traverse1 (htraverse1 f) xs

instance Invariant (Div1 f) where
  invmap _ = contramap

deriving via WrappedDivisible (Div1 f) instance Inply (Div1 f)

instance Divise f => Interpret Div1 f where
  interpret = runDiv1

-- | Pattern matching on a 'Div1', exposing the raw @f@ instead of
-- having it wrapped in a 'Coyoneda'.  This is the analogue of
-- 'Data.Functor.Apply.Ap1' and essentially treats the "cons" of the
-- 'Div1' as a contravariant day convolution.
--
-- Before v0.3.3.0, this used to be the concrete constructor of 'Div1'.
-- After, it is now an abstract pattern.
--
-- @since 0.3.3.0
pattern Div1_ :: (a -> (b, c)) -> f b -> Div f c -> Div1 f a
pattern Div1_ f x xs <- (div1_ -> CD.Day x xs f)
  where
    Div1_ f x (Div xs) = Div1 $ Coyoneda (fst . f) x :| (map . contramap) (snd . f) xs

{-# COMPLETE Div1_ #-}

div1_ :: Div1 f ~> CD.Day f (Div f)
div1_ (Div1 (Coyoneda g x :| xs)) = CD.Day x (Div xs) (\y -> (g y, y))

-- | A 'Div1' is a "non-empty" 'Div'; this function "forgets" the non-empty
-- property and turns it back into a normal 'Div'.
toDiv :: Div1 f ~> Div f
toDiv = Div . toList . unDiv1

-- | Map over the underlying context in a 'Div1'.
hoistDiv1 :: (f ~> g) -> Div1 f ~> Div1 g
hoistDiv1 = hmap

-- | Inject a single action in @f@ into a @'Div' f@.
liftDiv1 :: f ~> Div1 f
liftDiv1 = inject

-- | Interpret a 'Div1' into a context @g@, provided @g@ is 'Divise'.
runDiv1 :: Divise g => (f ~> g) -> Div1 f ~> g
runDiv1 f = foldr1 (divise (\y -> (y, y))) . fmap go . unDiv1
  where
    go (Coyoneda g x) = contramap g (f x)

-- | 'Div1' is isomorphic to 'NonEmptyF' for contravariant @f@.  This
-- witnesses one way of that isomorphism.
div1NonEmptyF :: Contravariant f => Div1 f ~> NonEmptyF f
div1NonEmptyF = NonEmptyF . fmap lowerCoyoneda . unDiv1

-- | 'Div1' is isomorphic to 'NonEmptyF' for contravariant @f@.  This
-- witnesses one way of that isomorphism.
nonEmptyFDiv1 :: NonEmptyF f ~> Div1 f
nonEmptyFDiv1 = Div1 . fmap liftCoyoneda . runNonEmptyF

-- | The free 'Decide'.  Used to aggregate multiple possible consumers,
-- directing the input into an appropriate consumer.
data Dec :: (Type -> Type) -> Type -> Type where
  Lose :: (a -> Void) -> Dec f a
  Choose :: (a -> Either b c) -> f b -> Dec f c -> Dec f a

instance Contravariant (Dec f) where
  contramap f = \case
    Lose g -> Lose (g . f)
    Choose g x xs -> Choose (g . f) x xs
instance Invariant (Dec f) where
  invmap _ = contramap
deriving via WrappedDivisible (Dec f) instance Inalt (Dec f)
deriving via WrappedDivisible (Dec f) instance Inplus (Dec f)
instance Decide (Dec f) where
  decide f = \case
    Lose g -> contramap (either (absurd . g) id . f)
    Choose g x xs ->
      Choose (assoc . first g . f) x
        . decide id xs
instance Conclude (Dec f) where
  conclude = Lose
instance HFunctor Dec where
  hmap = hoistDec
instance Inject Dec where
  inject = liftDec
instance Conclude f => Interpret Dec f where
  interpret = runDec

instance HTraversable Dec where
  htraverse :: forall f g h a. Applicative h => (forall x. f x -> h (g x)) -> Dec f a -> h (Dec g a)
  htraverse f = go
    where
      go :: Dec f b -> h (Dec g b)
      go = \case
        Lose v -> pure (Lose v)
        Choose g x xs -> Choose g <$> f x <*> go xs

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
deriving via WrappedDivisible (Dec1 f) instance Inalt (Dec1 f)
instance Decide (Dec1 f) where
  decide f (Dec1 g x xs) =
    Dec1 (assoc . first g . f) x
      . decide id xs
      . toDec
instance HFunctor Dec1 where
  hmap = hoistDec1
instance Inject Dec1 where
  inject = liftDec1
instance Decide f => Interpret Dec1 f where
  interpret = runDec1

instance HTraversable Dec1 where
  htraverse f (Dec1 g x xs) = Dec1 g <$> f x <*> htraverse f xs

instance HTraversable1 Dec1 where
  htraverse1 f (Dec1 g x xs) = traverseDec1_ f g x xs

-- | Map over the undering context in a 'Dec1'.
hoistDec1 :: forall f g. (f ~> g) -> Dec1 f ~> Dec1 g
hoistDec1 f (Dec1 g x xs) = Dec1 g (f x) (hoistDec f xs)

-- | Inject a single action in @f@ into a @'Dec1' f@.
liftDec1 :: f ~> Dec1 f
liftDec1 x = Dec1 Left x (Lose id)

-- | Interpret a 'Dec1' into a context @g@, provided @g@ is 'Decide'.
runDec1 :: Decide g => (f ~> g) -> Dec1 f ~> g
runDec1 f (Dec1 g x xs) = runDec1_ f g x xs

runDec1_ ::
  forall f g a b c.
  Decide g =>
  (f ~> g) ->
  (a -> Either b c) ->
  f b ->
  Dec f c ->
  g a
runDec1_ f = go
  where
    go :: (x -> Either y z) -> f y -> Dec f z -> g x
    go g x = \case
      Lose h -> contramap (either id (absurd . h) . g) (f x)
      Choose h y ys -> decide g (f x) (go h y ys)

traverseDec1_ ::
  forall f g h a b c.
  Apply h =>
  (forall x. f x -> h (g x)) ->
  (a -> Either b c) ->
  f b ->
  Dec f c ->
  h (Dec1 g a)
traverseDec1_ f = go
  where
    go :: (x -> Either y z) -> f y -> Dec f z -> h (Dec1 g x)
    go g x = \case
      Lose h -> (\x' -> Dec1 g x' (Lose h)) <$> f x
      Choose h y ys -> Dec1 g <$> f x <.> (toDec <$> go h y ys)
