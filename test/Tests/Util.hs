{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE RankNTypes        #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TypeApplications  #-}
{-# LANGUAGE TypeOperators     #-}

module Tests.Util (
    isoProp
  , sumGen
  , intGen
  , listGen
  , groupTree
  ) where

-- import           Type.Reflection
import           Control.Applicative
import           Control.Natural.IsoF
import           Data.Functor.Classes
import           Data.Functor.Combinator
import           Data.Functor.Day
import           Data.GADT.Compare
import           Data.GADT.Show
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.Maybe
import           Hedgehog
import           Hedgehog.Internal.Property
import           Hedgehog.Main
import           Test.Tasty
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Type.Reflection
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range


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

-- instance (GEq f, GEq g) => Eq (Day f g a) where
--     (==) (Day x1 y1 _) (Day x2 y2 _) = isJust $ do
--       _ <- geq x1 x2
--       _ <- geq y1 y2
--       pure ()

-- instance Show c => GShow (Const c) where
--     gshowsPrec = showsPrec

-- instance (GShow f, GShow g) => GShow (Day f g) where
--     gshowsPrec d (Day x y _) =
--       showsBinaryWith gshowsPrec gshowsPrec "Day" d x y

-- instance (GShow f, GShow g) => Show (Day f g a) where
--     showsPrec = gshowsPrec

-- instance (Show x, Show y) => Show1 (Day (Const x) (Const y)) where
--     liftShowsPrec _ _ d (Day x y _)
--       = showsBinaryWith showsPrec showsPrec "Day" d x y

-- instance (Show x, Show y, Show a) => Show (Day (Const x) (Const y) a) where
--     showsPrec = liftShowsPrec showsPrec showList
