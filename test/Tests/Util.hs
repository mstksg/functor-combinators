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

-- import           Control.Applicative
-- import           Data.HBifunctor.Associative
-- import           Data.HBifunctor.Tensor
-- import           Hedgehog.Main
-- import           Test.Tasty
-- import           Type.Reflection
import           Control.Monad
import           Control.Natural.IsoF
import           Data.Functor.Classes
import           Data.Functor.Combinator
import           Data.Functor.Day
import           Data.Functor.Identity
import           Data.GADT.Compare
import           Data.GADT.Show
import           Data.HBifunctor.Tensor
import           Data.Kind
import           Data.Maybe
import           Data.Semigroup                 (Any(..))
import           Hedgehog
import           Hedgehog.Internal.Property
import           Test.Tasty
import           Test.Tasty.Hedgehog
import qualified Control.Applicative.Free       as Ap
import qualified Hedgehog.Gen                   as Gen
import qualified Hedgehog.Range                 as Range


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

instance (GEq f, GEq g) => Eq (Day f g a) where
    (==) (Day x1 y1 _) (Day x2 y2 _) =
        isJust (geq x1 x2 *> geq y1 y2)

data ConstUnit :: Type -> Type -> Type where
    ConstUnit :: e -> ConstUnit e ()

deriving instance Eq e => Eq (ConstUnit e b)
deriving instance Show e => Show (ConstUnit e b)

instance Eq e => GEq (ConstUnit e) where
    geq = \case
      ConstUnit x -> \case
        ConstUnit y -> Refl <$ guard (x == y)

instance Show e => GShow (ConstUnit e) where
    gshowsPrec = showsPrec


-- data SBool :: Bool -> Type  where
--     SFalse :: SBool 'False
--     STrue  :: SBool 'True

-- deriving instance Eq (SBool b)
-- deriving instance Show (SBool b)

-- instance GEq SBool where
--     geq = \case
--       SFalse -> \case
--         SFalse -> Just Refl
--         STrue  -> Nothing
--       STrue  -> \case
--         SFalse -> Nothing
--         STrue  -> Just Refl

-- instance GShow SBool where
--     gshowsPrec = showsPrec

-- instance Show c => GShow (Const c) where
--     gshowsPrec = showsPrec

instance (GShow f, GShow g) => GShow (Day f g) where
    gshowsPrec d (Day x y _) =
      showsBinaryWith gshowsPrec gshowsPrec "Day" d x y

instance (GShow f, GShow g) => Show (Day f g a) where
    showsPrec = gshowsPrec

instance GShow f => GShow (Ap1 f) where
    gshowsPrec d (Ap1 x y) = case matchMF @Day y of
      L1 _  -> showsUnaryWith gshowsPrec "inject" d x
      R1 ys -> showsBinaryWith gshowsPrec gshowsPrec "Ap1" d x ys

-- instance (GEq f) => Eq (Ap1 f a) where
--     (==) (Ap1 x1 y1) (Ap1 x2 y2) =
--       isJust (geq x1 x2) && case matchMF @Day y1 of
--         L1 _   -> case matchMF @Day y2 of
--           L1 _ -> True
--           R1 _ -> False
--         R1 ys1 -> case matchMF @Day y2 of
--           L1 _   -> False
--           R1 ys2 -> ys1 == ys2
      
    -- (==) (Day x1 y1 _) (Day x2 y2 _) =
    --     isJust (geq x1 x2 *> geq y1 y2)

--       Ap.Pure x -> showsUnaryWith gshowsPrec "Pure" d x
    -- showsPrec = gshowsPrec

instance GShow f => Show (Ap1 f a) where
    showsPrec = gshowsPrec

deriving instance (Show e, Show (f a)) => Show (EnvT e f a)
deriving instance (Eq e, Eq (f a)) => Eq (EnvT e f a)

instance Enum Any where
    toEnum   = Any . toEnum
    fromEnum = fromEnum . getAny
