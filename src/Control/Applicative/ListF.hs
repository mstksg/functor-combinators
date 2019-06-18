{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE PatternSynonyms    #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeOperators      #-}
{-# LANGUAGE ViewPatterns       #-}

-- |
-- Module      : Control.Applicative.ListF
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides functor combinators that are wrappers over lists or
-- maybes of @f a@s, especially for their 'Data.Functor.HFunctor.Interpret'
-- instances.
--
-- Each one transforms a functor into some product of itself.  For example,
-- @'NonEmptyF' f@ represents @f ':*:' f@, or @f :*: f :*: f@, or @f :*:
-- f :*: f :*: f@, etc.
module Control.Applicative.ListF (
  -- * 'ListF'
    ListF(..), mapListF
  -- * 'NonEmptyF'
  , NonEmptyF(.., ProdNonEmpty, nonEmptyProd), mapNonEmptyF
  , toListF, fromListF
  -- * 'MaybeF'
  , MaybeF(..), mapMaybeF
  , listToMaybeF, maybeToListF
  ) where

import           Control.Applicative
import           Control.Natural
import           Data.Coerce
import           Data.Data
import           Data.Deriving
import           Data.Foldable
import           Data.Functor.Bind
import           Data.Functor.Plus
import           Data.List.NonEmpty  (NonEmpty(..))
import           Data.Maybe
import           GHC.Generics

-- | A list of @f a@s.  Can be used to describe a product of many different
-- values of type @f a@.
--
-- This is the Free 'Plus'.
newtype ListF f a = ListF { runListF :: [f a] }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''ListF
deriveRead1 ''ListF
deriveEq1 ''ListF
deriveOrd1 ''ListF

instance Apply f => Apply (ListF f) where
    ListF fs <.> ListF xs = ListF $ liftF2 (<.>) fs xs
instance Applicative f => Applicative (ListF f) where
    pure  = ListF . (:[]) . pure
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

-- | Map a function over the inside of a 'ListF'.
mapListF
    :: ([f a] -> [g b])
    -> ListF f a
    -> ListF g b
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
-- This is the Free 'Plus'.
newtype NonEmptyF f a = NonEmptyF { runNonEmptyF :: NonEmpty (f a) }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''NonEmptyF
deriveRead1 ''NonEmptyF
deriveEq1 ''NonEmptyF
deriveOrd1 ''NonEmptyF

instance Applicative f => Applicative (NonEmptyF f) where
    pure  = NonEmptyF . (:| []) . pure
    NonEmptyF fs <*> NonEmptyF xs = NonEmptyF $ liftA2 (<*>) fs xs

instance Functor f => Alt (NonEmptyF f) where
    (<!>) = (<>)

instance Semigroup (NonEmptyF f a) where
    NonEmptyF xs <> NonEmptyF ys = NonEmptyF (xs <> ys)

-- | Map a function over the inside of a 'NonEmptyF'.
mapNonEmptyF
    :: (NonEmpty (f a) -> NonEmpty (g b))
    -> NonEmptyF f a
    -> NonEmptyF g b
mapNonEmptyF = coerce

-- | Convert a 'NonEmptyF' into a 'ListF' with at least one item.
toListF :: NonEmptyF f ~> ListF f
toListF (NonEmptyF xs) = ListF (toList xs)

-- | Convert a 'ListF' either a 'NonEmptyF', or a 'Proxy' in the case that
-- the list was empty.
fromListF :: ListF f ~> (Proxy :+: NonEmptyF f)
fromListF (ListF xs) = case xs of
    []   -> L1 Proxy
    y:ys -> R1 $ NonEmptyF (y :| ys)

-- | Treat a @'NonEmptyF' f@ as a product between an @f@ and a @'ListF' f@.
--
-- 'nonEmptyProd' is the record accessor.
pattern ProdNonEmpty :: (f :*: ListF f) a -> NonEmptyF f a
pattern ProdNonEmpty { nonEmptyProd
                     }
            <- ((\case NonEmptyF (x :| xs) -> x :*: ListF xs) -> nonEmptyProd)
  where
    ProdNonEmpty (x :*: ListF xs) = NonEmptyF (x :| xs)
{-# COMPLETE ProdNonEmpty #-}

-- | A maybe @f a@.
--
-- Can be useful for describing a "an @f a@ that may or may not be there".
--
-- This is the free structure for a "fail"-like typeclass that would only
-- have @zero :: f a@.
--
-- Equivalent to @'ProxyF' ':+:' 'IdentityT'@
newtype MaybeF f a = MaybeF { runMaybeF :: Maybe (f a) }
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

-- | Picks the first 'Just'.
instance Semigroup (MaybeF f a) where
    MaybeF xs <> MaybeF ys = MaybeF (xs <!> ys)

instance Monoid (MaybeF f a) where
    mempty = MaybeF Nothing

-- | Map a function over the inside of a 'MaybeF'.
mapMaybeF
    :: (Maybe (f a) -> Maybe (g b))
    -> MaybeF f a
    -> MaybeF g b
mapMaybeF = coerce

-- | Convert a 'MaybeF' into a 'ListF' with zero or one items.
maybeToListF :: MaybeF f ~> ListF f
maybeToListF (MaybeF x) = ListF (maybeToList x)

-- | Convert a 'ListF' into a 'MaybeF' containing the first @f a@ in the
-- list, if it exists.
listToMaybeF :: ListF f ~> MaybeF f
listToMaybeF (ListF xs) = MaybeF (listToMaybe xs)
