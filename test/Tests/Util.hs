{-# LANGUAGE FlexibleInstances  #-}
{-# LANGUAGE GADTs              #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE RankNTypes         #-}
{-# LANGUAGE RecordWildCards    #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications   #-}
{-# LANGUAGE TypeInType         #-}
{-# LANGUAGE TypeOperators      #-}
{-# OPTIONS_GHC -Wno-orphans    #-}

module Tests.Util (
    isoProp
  , sumGen
  , intGen
  , listGen
  , groupTree
  ) where

import           Control.Applicative
import           Control.Natural.IsoF
import           Data.Function
import           Data.Functor.Classes
import           Data.Functor.Combinator
import           Data.GADT.Show
import           Data.HBifunctor.Tensor
import           Data.Semigroup             (Any(..))
import           Hedgehog
import           Hedgehog.Internal.Property
import           Test.Tasty
import           Test.Tasty.Hedgehog
import qualified Control.Applicative.Free   as Ap
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range


isoProp
    :: (Show (f a), Show (g a), Eq (f a), Eq (g a), Monad m)
    => (f <~> g)
    -> Gen (f a)
    -> Gen (g a)
    -> PropertyT m ()
isoProp i gx gy = do
    x <- forAll gx
    y <- forAll gy
    tripping x (viewF   i) (Just . reviewF i)
    tripping y (reviewF i) (Just . viewF   i)

sumGen :: MonadGen m => m (f a) -> m (g a) -> m ((f :+: g) a)
sumGen gx gy = Gen.bool >>= \case
    False -> L1 <$> gx
    True  -> R1 <$> gy

intGen :: MonadGen m => m Int
intGen = Gen.integral (Range.linear 0 100)

listGen :: MonadGen m => m [Int]
listGen = Gen.list (Range.linear 0 100) intGen

groupTree :: Group -> TestTree
groupTree Group{..} = testGroup (unGroupName groupName)
                                (map (uncurry go) groupProperties)
  where
    go :: PropertyName -> Property -> TestTree
    go n = testProperty (mkName (unPropertyName n))
    mkName = map deUnderscore . drop (length @[] @Char "prop_")
    deUnderscore '_' = ' '
    deUnderscore c   = c

instance (GShow f, GShow g) => Eq (Day f g a) where
    (==) = (==) `on` show

instance Show c => GShow (Const c) where
    gshowsPrec = showsPrec

instance (GShow f, GShow g) => GShow (Day f g) where
    gshowsPrec d (Day x y _) =
      showsBinaryWith gshowsPrec gshowsPrec "Day" d x y

instance (GShow f, GShow g) => Show (Day f g a) where
    showsPrec = gshowsPrec

instance GShow f => GShow (Ap1 f) where
    gshowsPrec d (Ap1 x y) = case matchMF @Day y of
      L1 _  -> showsUnaryWith gshowsPrec "inject" d x
      R1 ys -> showsBinaryWith gshowsPrec gshowsPrec "Ap1" d x ys

instance GShow f => Eq (Ap1 f a) where
    (==) = (==) `on` show

instance GShow f => Show (Ap1 f a) where
    showsPrec = gshowsPrec

instance GShow f => GShow (Ap f) where
    gshowsPrec d = \case
      Ap.Pure _  -> showString "<pure>"
      Ap.Ap x xs -> showsBinaryWith gshowsPrec gshowsPrec "Ap" d x xs

instance GShow f => Show (Ap f a) where
    showsPrec = gshowsPrec

instance GShow f => Eq (Ap f a) where
    (==) = (==) `on` show

deriving instance (Show e, Show (f a)) => Show (EnvT e f a)
deriving instance (Eq e, Eq (f a)) => Eq (EnvT e f a)

instance Enum Any where
    toEnum   = Any . toEnum
    fromEnum = fromEnum . getAny
