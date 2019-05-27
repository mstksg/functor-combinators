{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE TemplateHaskell    #-}

module Control.Applicative.ListF (
    ListF(..)
  , NonEmptyF(..)
  , MaybeF(..)
  ) where

import           Control.Applicative
import           Data.Data
import           Data.Deriving
import           Data.Functor.Plus
import           Data.List.NonEmpty  (NonEmpty(..))
import           GHC.Generics

-- | A list of @f a@s.
--
-- This is the Free 'Plus'.
newtype ListF f a = ListF { runListF :: [f a] }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''ListF
deriveRead1 ''ListF
deriveEq1 ''ListF
deriveOrd1 ''ListF

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

-- | A non-empty list of @f a@s.
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

-- | A maybe @f a@.  This is the free structure for a "fail"-like typeclass
-- that only has @zero :: f a@.
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

instance Semigroup (MaybeF f a) where
    MaybeF xs <> MaybeF ys = MaybeF (xs <!> ys)

instance Monoid (MaybeF f a) where
    mempty = MaybeF Nothing
