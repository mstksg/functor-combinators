{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.HBifunctor (
    hbifunctorTests
  ) where

import           Control.Applicative
import           Control.Monad.Freer.Church
import           Data.Functor
import           Data.Functor.Combinator
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Functor.Sum
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.Proxy
import           Hedgehog
import           Test.Tasty
import           Tests.HFunctor
import           Tests.Util
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range

hbifunctorTests :: TestTree
hbifunctorTests = groupTree $$(discover)

associatingProp
    :: forall t f g h m a.
     ( Associative t
     , Monad m
     , Functor f, Functor g, Functor h
     , Show (t f (t g h) a)
     , Show (t (t f g) h a)
     , Eq (t f (t g h) a)
     , Eq (t (t f g) h a)
     )
    => Gen (t f (t g h) a)
    -> Gen (t (t f g) h a)
    -> PropertyT m ()
associatingProp = isoProp (associating @t)

matchingSFProp
    :: forall t f m a.
     ( Semigroupoidal t
     , Monad m
     , Functor f
     , Show (f a), Eq (f a)
     , Show (SF t f a), Eq (SF t f a)
     , Show (t f (SF t f) a), Eq (t f (SF t f) a)
     )
    => Gen (SF t f a)
    -> Gen (f a)
    -> Gen (t f (SF t f) a)
    -> PropertyT m ()
matchingSFProp gx gy gz = isoProp (matchingSF @t) gx (sumGen gy gz)

splittingMFProp
    :: forall t f m a.
     ( Monoidal t
     , Monad m
     , Show (I t a), Eq (I t a)
     , Show (MF t f a), Eq (MF t f a)
     , Show (t f (MF t f) a), Eq (t f (MF t f) a)
     )
    => Gen (MF t f a)
    -> Gen ((I t :+: t f (MF t f)) a)
    -> PropertyT m ()
splittingMFProp = isoProp (splittingMF @t)

splittingSFProp
    :: forall t f m a.
     ( Matchable t
     , Monad m
     , Show (SF t f a), Eq (SF t f a)
     , Show (t f (MF t f) a), Eq (t f (MF t f) a)
     )
    => Gen (SF t f a)
    -> Gen (t f (MF t f) a)
    -> PropertyT m ()
splittingSFProp = isoProp (splittingSF @t)

matchingMFProp
    :: forall t f m a.
     ( Matchable t
     , Monad m
     , Show (I t a), Eq (I t a)
     , Show (MF t f a), Eq (MF t f a)
     , Show (SF t f a), Eq (SF t f a)
     )
    => Gen (MF t f a)
    -> Gen ((I t :+: SF t f) a)
    -> PropertyT m ()
matchingMFProp = isoProp (matchingMF @t)

class HBifunctor t => TestHBifunctor t where
    genHB
        :: MonadGen m
        => m (f a)
        -> m (g a)
        -> m (t f g a)

instance TestHBifunctor (:+:) where
    genHB = sumGen

instance TestHBifunctor Sum where
    genHB gx gy = sumGen gx gy <&> \case
      L1 x -> InL x
      R1 y -> InR y

instance TestHBifunctor (:*:) where
    genHB gx gy = (:*:) <$> gx <*> gy

instance TestHBifunctor Product where
    genHB gx gy = Pair <$> gx <*> gy

instance TestHBifunctor Day where
    genHB gx gy = do
      f <- Gen.bool <&> \case
        False -> const
        True  -> flip const
      Day <$> gx <*> gy <*> pure f

instance TestHBifunctor These1 where
    genHB gx gy = Gen.enumBounded >>= \case
      LT -> This1 <$> gx
      EQ -> That1 <$> gy
      GT -> These1 <$> gx <*> gy

instance TestHBifunctor Comp where
    genHB gx gy = (:>>=) <$> gx <*> fmap const gy

instance TestHBifunctor LeftF where
    genHB gx _ = LeftF <$> gx

instance TestHBifunctor RightF where
    genHB _ gy = RightF <$> gy

associatingProp_
    :: forall t m f g h a.
     ( Associative t
     , TestHBifunctor t
     , Monad m
     , Functor f, Functor g, Functor h
     , Show (t f (t g h) a), Eq (t f (t g h) a)
     , Show (t (t f g) h a), Eq (t (t f g) h a)
     )
    => Gen (f a)
    -> Gen (g a)
    -> Gen (h a)
    -> PropertyT m ()
associatingProp_ gx gy gz = associatingProp @t
      (genHB gx (genHB gy gz))
      (genHB (genHB gx gy) gz)

matchingSFProp_
    :: forall t m f a.
     ( Semigroupoidal t
     , TestHBifunctor t
     , TestHFunctor (SF t)
     , Monad m
     , Functor f
     , Show (f a), Eq (f a)
     , Show (SF t f a), Eq (SF t f a)
     , Show (t f (SF t f) a), Eq (t f (SF t f) a)
     )
    => Gen (f a)
    -> PropertyT m ()
matchingSFProp_ gx = matchingSFProp @t
      (genHF gx)
      gx
      (genHB gx (genHF gx))

splittingMFProp_
    :: forall t f m a.
     ( Monoidal t
     , TestHBifunctor t
     , TestHFunctor (MF t)
     , Show (I t a), Eq (I t a)
     , Show (MF t f a), Eq (MF t f a)
     , Show (t f (MF t f) a), Eq (t f (MF t f) a)
     , Monad m
     )
    => Gen (f a)
    -> Maybe (Gen (I t a))
    -> PropertyT m ()
splittingMFProp_ gx gy = splittingMFProp @t
    (genHF gx)
    (case gy of
       Nothing  -> R1 <$> genHB gx (genHF gx)
       Just gy' -> sumGen gy' (genHB gx (genHF gx))
    )

splittingSFProp_
    :: forall t f m a.
     ( Matchable t
     , TestHBifunctor t
     , TestHFunctor (SF t)
     , TestHFunctor (MF t)
     , Monad m
     , Show (SF t f a), Eq (SF t f a)
     , Show (t f (MF t f) a), Eq (t f (MF t f) a)
     )
    => Gen (f a)
    -> PropertyT m ()
splittingSFProp_ gx = splittingSFProp @t
    (genHF gx)
    (genHB gx (genHF gx))

matchingMFProp_
    :: forall t f m a.
     ( Matchable t
     , TestHFunctor (MF t)
     , TestHFunctor (SF t)
     , Monad m
     , Show (I t a), Eq (I t a)
     , Show (MF t f a), Eq (MF t f a)
     , Show (SF t f a), Eq (SF t f a)
     )
    => Gen (f a)
    -> Maybe (Gen (I t a))
    -> PropertyT m ()
matchingMFProp_ gx gy = matchingMFProp @t
    (genHF gx)
    (case gy of
       Nothing  -> R1 <$> genHF gx
       Just gy' -> sumGen gy' (genHF gx)
    )

prop_associating_Sum :: Property
prop_associating_Sum = property $
    associatingProp_ @(:+:) listGen listGen listGen

prop_associating_Sum' :: Property
prop_associating_Sum' = property $
    associatingProp_ @Sum listGen listGen listGen

prop_associating_Prod :: Property
prop_associating_Prod = property $
    associatingProp_ @(:*:) listGen listGen listGen

prop_associating_Prod' :: Property
prop_associating_Prod' = property $
    associatingProp_ @Product listGen listGen listGen

prop_associating_These :: Property
prop_associating_These = property $
    associatingProp_ @These1 listGen listGen listGen

prop_associating_Day :: Property
prop_associating_Day = property $
    associatingProp_ @Day
      (Const <$> intGen)
      (Const <$> intGen)
      (Const <$> intGen)

prop_associating_Comp :: Property
prop_associating_Comp = property $
    associatingProp_ @Comp
      (Gen.list (Range.linear 0 3) intGen)
      (Gen.list (Range.linear 0 3) intGen)
      (Gen.list (Range.linear 0 3) intGen)

prop_associating_LeftF :: Property
prop_associating_LeftF = property $
    associatingProp_ @LeftF listGen listGen listGen

prop_associating_RightF :: Property
prop_associating_RightF = property $
    associatingProp_ @LeftF listGen listGen listGen





prop_matchingSF_Sum :: Property
prop_matchingSF_Sum = property $
    matchingSFProp_ @(:+:) listGen

prop_matchingSF_Sum' :: Property
prop_matchingSF_Sum' = property $
    matchingSFProp_ @Sum listGen

prop_matchingSF_Prod :: Property
prop_matchingSF_Prod = property $
    matchingSFProp_ @(:*:) listGen

prop_matchingSF_Prod' :: Property
prop_matchingSF_Prod' = property $
    matchingSFProp_ @Product listGen

prop_matchingSF_These :: Property
prop_matchingSF_These = property $
    matchingSFProp_ @These1 listGen

prop_matchingSF_Day :: Property
prop_matchingSF_Day = property $
    matchingSFProp_ @Day $ (Const <$> intGen)

prop_matchingSF_Comp :: Property
prop_matchingSF_Comp = property $
    matchingSFProp_ @Comp $
      Gen.list (Range.linear 0 3) intGen

prop_matchingSF_LeftF :: Property
prop_matchingSF_LeftF = property $
    matchingSFProp_ @LeftF listGen

prop_matchingSF_RightF :: Property
prop_matchingSF_RightF = property $
    matchingSFProp_ @RightF listGen







prop_splittingMF_Sum :: Property
prop_splittingMF_Sum = property $
    splittingMFProp_ @(:+:) listGen Nothing

prop_splittingMF_Sum' :: Property
prop_splittingMF_Sum' = property $
    splittingMFProp_ @Sum listGen Nothing

prop_splittingMF_Prod :: Property
prop_splittingMF_Prod = property $
    splittingMFProp_ @(:*:) listGen (Just (pure Proxy))

prop_splittingMF_Prod' :: Property
prop_splittingMF_Prod' = property $
    splittingMFProp_ @Product listGen (Just (pure Proxy))

prop_splittingMF_Day :: Property
prop_splittingMF_Day = property $
    splittingMFProp_ @Day
      (Const <$> intGen)
      (Just (Identity <$> intGen))

prop_splittingMF_Comp :: Property
prop_splittingMF_Comp = property $
    splittingMFProp_ @Comp
      (Gen.list (Range.linear 0 3) intGen)
      (Just (Identity <$> intGen))






prop_splittingSF_Sum :: Property
prop_splittingSF_Sum = property $
    splittingSFProp_ @(:+:) listGen

-- prop_splittingSF_Sum' :: Property
-- prop_splittingSF_Sum' = property $
--     splittingSFProp_ @Sum listGen

prop_splittingSF_Prod :: Property
prop_splittingSF_Prod = property $
    splittingSFProp_ @(:*:) listGen

prop_splittingSF_Prod' :: Property
prop_splittingSF_Prod' = property $
    splittingSFProp_ @Product listGen

prop_splittingSF_Day :: Property
prop_splittingSF_Day = property $
    splittingSFProp_ @Day (Const <$> intGen)






prop_matchingMF_Sum :: Property
prop_matchingMF_Sum = property $
    matchingMFProp_ @(:+:) listGen Nothing

-- prop_matchingMF_Sum' :: Property
-- prop_matchingMF_Sum' = property $
--     matchingMFProp_ @Sum listGen Nothing

prop_matchingMF_Prod :: Property
prop_matchingMF_Prod = property $
    matchingMFProp_ @(:*:) listGen (Just (pure Proxy))

prop_matchingMF_Prod' :: Property
prop_matchingMF_Prod' = property $
    matchingMFProp_ @Product listGen (Just (pure Proxy))

prop_matchingMF_Day :: Property
prop_matchingMF_Day = property $
    matchingMFProp_ @Day
      (Const <$> intGen)
      (Just (Identity <$> intGen))
