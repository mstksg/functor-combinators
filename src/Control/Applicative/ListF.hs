-- |
-- Module      : Control.Applicative.ListF
-- Copyright   : (c) Justin Le 2025
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides functor combinators that are wrappers over lists or
-- maybes of @f a@s, especially for their
-- 'Data.HFunctor.Interpret.Interpret' instances.
--
-- Each one transforms a functor into some product of itself.  For example,
-- @'NonEmptyF' f@ represents @f ':*:' f@, or @f :*: f :*: f@, or @f :*:
-- f :*: f :*: f@, etc.
module Control.Applicative.ListF (
  -- * 'ListF'
  ListF (..),
  mapListF,

  -- * 'NonEmptyF'
  NonEmptyF (.., ProdNonEmpty, nonEmptyProd),
  mapNonEmptyF,
  toListF,
  fromListF,

  -- * 'MaybeF'
  MaybeF (..),
  mapMaybeF,
  listToMaybeF,
  maybeToListF,

  -- * 'MapF'
  MapF (..),
  NEMapF (..),
) where

import Control.Applicative
import Control.Natural
import Data.Coerce
import Data.Data
import Data.Deriving
import Data.Foldable
import Data.Functor.Bind
import Data.Functor.Classes
import Data.Functor.Contravariant
import Data.Functor.Contravariant.Conclude
import Data.Functor.Contravariant.Decide
import Data.Functor.Contravariant.Divise
import Data.Functor.Contravariant.Divisible
import Data.Functor.Invariant
import Data.Functor.Plus
import Data.List.NonEmpty (NonEmpty (..))
import qualified Data.Map as M
import qualified Data.Map.NonEmpty as NEM
import Data.Maybe
import Data.Pointed
import Data.Semigroup.Foldable
import Data.Semigroup.Traversable
import GHC.Generics

-- | A list of @f a@s.  Can be used to describe a product of many different
-- values of type @f a@.
--
-- This is the Free 'Plus'.
--
-- Incidentally, if used with a 'Contravariant' @f@, this is instead the
-- free 'Divisible'.
newtype ListF f a = ListF {runListF :: [f a]}
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''ListF
deriveRead1 ''ListF
deriveEq1 ''ListF
deriveOrd1 ''ListF

instance Apply f => Apply (ListF f) where
  ListF fs <.> ListF xs = ListF $ liftF2 (<.>) fs xs
instance Applicative f => Applicative (ListF f) where
  pure = ListF . (: []) . pure
  ListF fs <*> ListF xs = ListF $ liftA2 (<*>) fs xs

instance Functor f => Alt (ListF f) where
  (<!>) = (<>)

instance Functor f => Plus (ListF f) where
  zero = mempty

instance Applicative f => Alternative (ListF f) where
  empty = zero
  (<|>) = (<!>)

instance Semigroup (ListF f a) where
  ListF xs <> ListF ys = ListF (xs ++ ys)

instance Monoid (ListF f a) where
  mempty = ListF []

instance Pointed f => Pointed (ListF f) where
  point = ListF . (: []) . point

-- | @since 0.3.0.0
instance Contravariant f => Contravariant (ListF f) where
  contramap f (ListF xs) = ListF ((map . contramap) f xs)

-- | @since 0.3.0.0
instance Invariant f => Invariant (ListF f) where
  invmap f g (ListF xs) = ListF (map (invmap f g) xs)

-- | @since 0.3.0.0
instance Contravariant f => Divise (ListF f) where
  divise f (ListF xs) (ListF ys) =
    ListF $
      (map . contramap) (fst . f) xs
        <> (map . contramap) (snd . f) ys

-- | @since 0.3.0.0
instance Contravariant f => Divisible (ListF f) where
  divide = divise
  conquer = ListF []

-- | @since 0.3.0.0
instance Decide f => Decide (ListF f) where
  decide f (ListF xs) (ListF ys) =
    ListF $
      liftA2 (decide f) xs ys

-- | @since 0.3.0.0
instance Conclude f => Conclude (ListF f) where
  conclude f = ListF [conclude f]

-- | @since 0.3.0.0
instance Decidable f => Decidable (ListF f) where
  lose f = ListF [lose f]
  choose f (ListF xs) (ListF ys) =
    ListF $
      liftA2 (choose f) xs ys

-- | Map a function over the inside of a 'ListF'.
mapListF ::
  ([f a] -> [g b]) ->
  ListF f a ->
  ListF g b
mapListF = coerce

-- | A non-empty list of @f a@s.  Can be used to describe a product between
-- many different possible values of type @f a@.
--
-- Essentially:
--
-- @
-- 'NonEmptyF' f
--     ~ f                          -- one f
--   ':+:' (f ':*:' f)              -- two f's
--   :+: (f :*: f :*: f)            -- three f's
--   :+: (f :*: f :*: f :*: f)      -- four f's
--   :+: ...                        -- etc.
-- @
--
-- This is the Free 'Plus' on any 'Functor' @f@.
--
-- Incidentally, if used with a 'Contravariant' @f@, this is instead the
-- free 'Divise'.
newtype NonEmptyF f a = NonEmptyF {runNonEmptyF :: NonEmpty (f a)}
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''NonEmptyF
deriveRead1 ''NonEmptyF
deriveEq1 ''NonEmptyF
deriveOrd1 ''NonEmptyF

instance Applicative f => Applicative (NonEmptyF f) where
  pure = NonEmptyF . (:| []) . pure
  NonEmptyF fs <*> NonEmptyF xs = NonEmptyF $ liftA2 (<*>) fs xs

instance Functor f => Alt (NonEmptyF f) where
  (<!>) = (<>)

-- | @since 0.3.0.0
instance Contravariant f => Contravariant (NonEmptyF f) where
  contramap f (NonEmptyF xs) = NonEmptyF (fmap (contramap f) xs)

-- | @since 0.3.0.0
instance Invariant f => Invariant (NonEmptyF f) where
  invmap f g (NonEmptyF xs) = NonEmptyF (fmap (invmap f g) xs)

-- | @since 0.3.0.0
instance Contravariant f => Divise (NonEmptyF f) where
  divise f (NonEmptyF xs) (NonEmptyF ys) =
    NonEmptyF $
      (fmap . contramap) (fst . f) xs
        <> (fmap . contramap) (snd . f) ys

-- | @since 0.3.0.0
instance Decide f => Decide (NonEmptyF f) where
  decide f (NonEmptyF xs) (NonEmptyF ys) =
    NonEmptyF $
      decide f <$> xs <*> ys

instance Semigroup (NonEmptyF f a) where
  NonEmptyF xs <> NonEmptyF ys = NonEmptyF (xs <> ys)

instance Pointed f => Pointed (NonEmptyF f) where
  point = NonEmptyF . (:| []) . point

-- | Map a function over the inside of a 'NonEmptyF'.
mapNonEmptyF ::
  (NonEmpty (f a) -> NonEmpty (g b)) ->
  NonEmptyF f a ->
  NonEmptyF g b
mapNonEmptyF = coerce

-- | Convert a 'NonEmptyF' into a 'ListF' with at least one item.
toListF :: NonEmptyF f ~> ListF f
toListF (NonEmptyF xs) = ListF (toList xs)

-- | Convert a 'ListF' either a 'NonEmptyF', or a 'Proxy' in the case that
-- the list was empty.
fromListF :: ListF f ~> (Proxy :+: NonEmptyF f)
fromListF (ListF xs) = case xs of
  [] -> L1 Proxy
  y : ys -> R1 $ NonEmptyF (y :| ys)

-- | Treat a @'NonEmptyF' f@ as a product between an @f@ and a @'ListF' f@.
--
-- 'nonEmptyProd' is the record accessor.
pattern ProdNonEmpty :: (f :*: ListF f) a -> NonEmptyF f a
pattern ProdNonEmpty{nonEmptyProd} <-
  (\case NonEmptyF (x :| xs) -> x :*: ListF xs -> nonEmptyProd)
  where
    ProdNonEmpty (x :*: ListF xs) = NonEmptyF (x :| xs)

{-# COMPLETE ProdNonEmpty #-}

-- | A maybe @f a@.
--
-- Can be useful for describing a "an @f a@ that may or may not be there".
--
-- This is the free structure for a "fail"-like typeclass that would only
-- have @zero :: f a@.
newtype MaybeF f a = MaybeF {runMaybeF :: Maybe (f a)}
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''MaybeF
deriveRead1 ''MaybeF
deriveEq1 ''MaybeF
deriveOrd1 ''MaybeF

instance Applicative f => Applicative (MaybeF f) where
  pure = MaybeF . Just . pure
  MaybeF f <*> MaybeF x = MaybeF $ liftA2 (<*>) f x

instance Functor f => Alt (MaybeF f) where
  (<!>) = (<>)

instance Functor f => Plus (MaybeF f) where
  zero = mempty

instance Applicative f => Alternative (MaybeF f) where
  empty = zero
  (<|>) = (<!>)

-- | @since 0.3.3.0
instance Contravariant f => Contravariant (MaybeF f) where
  contramap f (MaybeF x) = MaybeF $ (fmap . contramap) f x

-- | @since 0.3.3.0
instance Invariant f => Invariant (MaybeF f) where
  invmap f g (MaybeF x) = MaybeF $ fmap (invmap f g) x

-- | @since 0.3.3.0
instance Contravariant f => Divise (MaybeF f) where
  divise f (MaybeF x) (MaybeF y) =
    MaybeF $
      (fmap . contramap) (fst . f) x
        <|> (fmap . contramap) (snd . f) y

-- | @since 0.3.3.0
instance Contravariant f => Divisible (MaybeF f) where
  divide = divise
  conquer = MaybeF Nothing

-- | @since 0.3.3.0
instance Decide f => Decide (MaybeF f) where
  decide f (MaybeF x) (MaybeF y) =
    MaybeF $
      liftA2 (decide f) x y

-- | @since 0.3.3.0
instance Conclude f => Conclude (MaybeF f) where
  conclude f = MaybeF (Just (conclude f))

-- | @since 0.3.3.0
instance Decidable f => Decidable (MaybeF f) where
  choose f (MaybeF x) (MaybeF y) =
    MaybeF $
      liftA2 (choose f) x y
  lose f = MaybeF (Just (lose f))

-- | Picks the first 'Just'.
instance Semigroup (MaybeF f a) where
  MaybeF xs <> MaybeF ys = MaybeF (xs <!> ys)

instance Monoid (MaybeF f a) where
  mempty = MaybeF Nothing

instance Pointed f => Pointed (MaybeF f) where
  point = MaybeF . Just . point

-- | Map a function over the inside of a 'MaybeF'.
mapMaybeF ::
  (Maybe (f a) -> Maybe (g b)) ->
  MaybeF f a ->
  MaybeF g b
mapMaybeF = coerce

-- | Convert a 'MaybeF' into a 'ListF' with zero or one items.
maybeToListF :: MaybeF f ~> ListF f
maybeToListF (MaybeF x) = ListF (maybeToList x)

-- | Convert a 'ListF' into a 'MaybeF' containing the first @f a@ in the
-- list, if it exists.
listToMaybeF :: ListF f ~> MaybeF f
listToMaybeF (ListF xs) = MaybeF (listToMaybe xs)

-- | A map of @f a@s, indexed by keys of type @k@.  It can be useful for
-- represeting a product of many different values of type @f a@, each "at"
-- a different @k@ location.
--
-- Can be considered a combination of 'Control.Comonad.Trans.Env.EnvT' and
-- 'ListF', in a way --- a @'MapF' k f a@ is like a @'ListF'
-- ('Control.Comonad.Trans.Env.EnvT' k f) a@ with unique (and ordered)
-- keys.
--
-- One use case might be to extend a schema with many "options", indexed by
-- some string.
--
-- For example, if you had a command line argument parser for a single
-- command
--
-- @
-- data Command a
-- @
--
-- Then you can represent a command line argument parser for /multiple/
-- named commands with
--
-- @
-- type Commands = 'MapF' 'String' Command
-- @
--
-- See 'NEMapF' for a non-empty variant, if you want to enforce that your
-- bag has at least one @f a@.
newtype MapF k f a = MapF {runMapF :: M.Map k (f a)}
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''MapF
deriveEq1 ''MapF
deriveOrd1 ''MapF

instance (Ord k, Read k, Read1 f) => Read1 (MapF k f) where
  liftReadsPrec = $(makeLiftReadsPrec ''MapF)

-- | A union, combining matching keys with '<!>'.
instance (Ord k, Alt f) => Semigroup (MapF k f a) where
  MapF xs <> MapF ys = MapF $ M.unionWith (<!>) xs ys

instance (Ord k, Alt f) => Monoid (MapF k f a) where
  mempty = MapF M.empty

-- | Left-biased union
instance (Functor f, Ord k) => Alt (MapF k f) where
  MapF xs <!> MapF ys = MapF $ M.union xs ys

instance (Functor f, Ord k) => Plus (MapF k f) where
  zero = MapF M.empty

instance (Monoid k, Pointed f) => Pointed (MapF k f) where
  point = MapF . M.singleton mempty . point

-- | A non-empty map of @f a@s, indexed by keys of type @k@.  It can be
-- useful for represeting a product of many different values of type @f a@,
-- each "at" a different @k@ location, where you need to have at least one
-- @f a@ at all times.
--
-- Can be considered a combination of 'Control.Comonad.Trans.Env.EnvT' and
-- 'NonEmptyF', in a way --- an @'NEMapF' k f a@ is like a @'NonEmptyF'
-- ('Control.Comonad.Trans.Env.EnvT' k f) a@ with unique (and ordered)
-- keys.
--
-- See 'MapF' for some use cases.
newtype NEMapF k f a = NEMapF {runNEMapF :: NEM.NEMap k (f a)}
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''NEMapF
deriveEq1 ''NEMapF
deriveOrd1 ''NEMapF

instance (Ord k, Read k, Read1 f) => Read1 (NEMapF k f) where
  liftReadsPrec = $(makeLiftReadsPrec ''NEMapF)

instance Foldable1 f => Foldable1 (NEMapF k f) where
  fold1 = foldMap1 fold1 . runNEMapF
  foldMap1 f = (foldMap1 . foldMap1) f . runNEMapF
  toNonEmpty = foldMap1 toNonEmpty . runNEMapF

instance Traversable1 f => Traversable1 (NEMapF k f) where
  traverse1 f = fmap NEMapF . (traverse1 . traverse1) f . runNEMapF
  sequence1 = fmap NEMapF . traverse1 sequence1 . runNEMapF

-- | A union, combining matching keys with '<!>'.
instance (Ord k, Alt f) => Semigroup (NEMapF k f a) where
  NEMapF xs <> NEMapF ys = NEMapF $ NEM.unionWith (<!>) xs ys

-- | Left-biased union
instance (Functor f, Ord k) => Alt (NEMapF k f) where
  NEMapF xs <!> NEMapF ys = NEMapF $ NEM.union xs ys

instance (Monoid k, Pointed f) => Pointed (NEMapF k f) where
  point = NEMapF . NEM.singleton mempty . point
