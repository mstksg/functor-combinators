{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveFoldable     #-}
{-# LANGUAGE DeriveFunctor      #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE TemplateHaskell    #-}

module Control.Applicative.ListF (
    ListF(..)
  , NonEmptyF(..)
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
    ListF xs <!> ListF ys = ListF (xs ++ ys)

instance Functor f => Plus (ListF f) where
    zero = ListF []

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
    NonEmptyF xs <!> NonEmptyF ys = NonEmptyF (xs <> ys)

