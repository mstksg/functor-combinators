{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell     #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.HBifunctor (
    hbifunctorTests
  ) where

import           Control.Applicative
import           Control.Monad.Freer.Church
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Functor
import           Data.Functor.Combinator
import           Data.Functor.Identity
import           Data.Functor.Product
import           Data.Functor.Sum
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor.Chain
import           Data.Maybe
import           Data.Proxy
import           Hedgehog
import           Test.Tasty
import           Test.Tasty.Hedgehog
import           Tests.Util
import qualified Data.Semigroup              as S
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range

-- hbifunctorTests :: TestTree
-- hbifunctorTests = groupTree $$(discover)

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

unrollingSFProp
    :: forall t f m a.
     ( Semigroupoidal t
     , Monad m
     , Functor f
     , Show (SF t f a), Eq (SF t f a)
     , Show (f a), Eq (f a)
     , Show (t f (Chain1 t f) a), Eq (t f (Chain1 t f) a)
     )
    => Gen (SF t f a)
    -> Gen (Chain1 t f a)
    -> PropertyT m ()
unrollingSFProp = isoProp (unrollingSF @t)

consSFProp
    :: forall t f m a.
     ( Semigroupoidal t
     , Monad m
     , Show (t f (SF t f) a)
     , Show (SF t f a), Eq (SF t f a)
     )
    => Gen (t f (SF t f) a)
    -> PropertyT m ()
consSFProp gx = do
    x <- forAll gx
    appendSF (hleft inject x) === consSF x

toSFProp
    :: forall t f m a.
     ( Semigroupoidal t
     , Monad m
     , Show (t f f a)
     , Show (SF t f a), Eq (SF t f a)
     )
    => Gen (t f f a)
    -> PropertyT m ()
toSFProp gx = do
    x <- forAll gx
    appendSF (hbimap inject inject x) === toSF x

biretractProp
    :: forall t f m a.
     ( Semigroupoidal t
     , CS t f
     , Monad m
     , Show (t f f a)
     , Show (f a), Eq (f a)
     )
    => Gen (t f f a)
    -> PropertyT m ()
biretractProp gx = do
    x <- forAll gx
    retract (appendSF (hbimap inject inject x)) === biretract x

binterpretProp
    :: forall t f m a.
     ( Semigroupoidal t
     , CS t f
     , Monad m
     , Show (t f f a)
     , Show (f a), Eq (f a)
     )
    => Gen (t f f a)
    -> PropertyT m ()
binterpretProp gx = do
    x <- forAll gx
    biretract x === binterpret id id x

rightIdentityProp
    :: forall t f m a.
     ( Tensor t
     , Monad m
     , Functor f
     , Show (f a), Eq (f a)
     , Show (t f (I t) a), Eq (t f (I t) a)
     )
    => Gen (f a)
    -> Gen (t f (I t) a)
    -> PropertyT m ()
rightIdentityProp = isoProp (rightIdentity @t)

leftIdentityProp
    :: forall t g m a.
     ( Tensor t
     , Monad m
     , Functor g
     , Show (g a), Eq (g a)
     , Show (t (I t) g a), Eq (t (I t) g a)
     )
    => Gen (g a)
    -> Gen (t (I t) g a)
    -> PropertyT m ()
leftIdentityProp = isoProp (leftIdentity @t)

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

unrollingMFProp
    :: forall t f m a.
     ( Monoidal t
     , Monad m
     , Show (MF t f a), Eq (MF t f a)
     , Show (I t a), Eq (I t a)
     , Show (t f (Chain t (I t) f) a), Eq (t f (Chain t (I t) f) a)
     )
    => Gen (MF t f a)
    -> Gen (Chain t (I t) f a)
    -> PropertyT m ()
unrollingMFProp = isoProp (unrollingMF @t)

toMFProp
    :: forall t f m a.
     ( Monoidal t
     , Monad m
     , Show (t f f a)
     , Show (MF t f a), Eq (MF t f a)
     )
    => Gen (t f f a)
    -> PropertyT m ()
toMFProp gx = do
    x <- forAll gx
    reviewF (splittingMF @t) (R1 (hright (inject @(MF t)) x)) === toMF @t x

fromSFProp
    :: forall t f m a.
     ( Monoidal t
     , Monad m
     , Show (SF t f a)
     , Show (MF t f a), Eq (MF t f a)
     )
    => Gen (SF t f a)
    -> PropertyT m ()
fromSFProp gx = do
    x <- forAll gx
    reviewF (splittingMF @t) (R1 (splitSF @t x)) === fromSF @t x

pureTProp
    :: forall t f m a.
     ( Monoidal t
     , Monad m
     , C (MF t) f
     , Show (I t a)
     , Show (f a), Eq (f a)
     )
    => Gen (I t a)
    -> PropertyT m ()
pureTProp gx = do
    x <- forAll gx
    retract (reviewF (splittingMF @t) (L1 x)) === pureT @t @f x

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

matchingChainProp
    :: forall t f m a.
     ( Matchable t
     , Monad m
     , Functor f
     , Show (f a), Eq (f a)
     , Show (I t a), Eq (I t a)
     , Show (t f (Chain1 t f) a), Eq (t f (Chain1 t f) a)
     , Show (t f (Chain t (I t) f) a), Eq (t f (Chain t (I t) f) a)
     )
    => Gen (Chain t (I t ) f a)
    -> Gen ((I t :+: Chain1 t f) a)
    -> PropertyT m ()
matchingChainProp = isoProp (matchingChain @t)

genChain
    :: forall t f m a. (MonadGen m, TestHBifunctor t)
    => m (f a)
    -> Maybe (m (I t a))
    -> m (Chain t (I t) f a)
genChain gx gy = go
  where
    go = case gy of
      Nothing  -> More <$> genHB @t gx go
      Just gy' -> Gen.bool >>= \case
        False -> Done <$> gy'
        True  -> More <$> genHB @t gx go

maybeSumGen
    :: Maybe (Gen (f a))
    -> Gen (g a)
    -> Gen ((f :+: g) a)
maybeSumGen = maybe (fmap R1) sumGen

semigroupoidalProps
    :: forall t f a.
     ( Semigroupoidal t
     , TestHBifunctor t
     , TestHFunctor (SF t)
     , CS t f
     , Functor f
     , Show (t f (t f f) a)     , Eq (t f (t f f) a)
     , Show (t (t f f) f a)     , Eq (t (t f f) f a)
     , Show (t f f a)
     , Show (t f (SF t f) a)    , Eq (t f (SF t f) a)
     , Show (SF t f a)          , Eq (SF t f a)
     , Show (t f (Chain1 t f) a), Eq (t f (Chain1 t f) a)
     , Show (f a)               , Eq (f a)
     )
    => Gen (f a)
    -> TestTree
semigroupoidalProps gx = testGroup "Semigroupoidal"
                       . map (uncurry testProperty . second property) $
    [ ("associating", associatingProp @t (genHB gx (genHB gx gx)) (genHB (genHB gx gx) gx))
    , ("matchingSF" , matchingSFProp  @t (genHF gx) gx (genHB gx (genHF gx)))
    , ("unrollingSF", unrollingSFProp @t (genHF gx) (genHF gx))
    , ("consSF"     , consSFProp      @t (genHB gx (genHF gx)))
    , ("toSF"       , toSFProp        @t (genHB gx gx))
    , ("biretract"  , biretractProp   @t (genHB gx gx))
    , ("binterpret" , binterpretProp  @t (genHB gx gx))
    ]

monoidalProps
    :: forall t f a.
     ( Monoidal t
     , TestHBifunctor t
     , TestHFunctor (MF t)
     , TestHFunctor (SF t)
     , CM t f
     , Functor f
     , Show (t f (I t) a)            , Eq (t f (I t) a)
     , Show (t (I t) f a)            , Eq (t (I t) f a)
     , Show (t f (MF t f) a)         , Eq (t f (MF t f) a)
     , Show (t f (Chain t (I t) f) a), Eq (t f (Chain t (I t) f) a)
     , Show (t f f a)
     , Show (MF t f a)               , Eq (MF t f a)
     , Show (SF t f a)
     , Show (I t a)                  , Eq (I t a)
     , Show (f a)                    , Eq (f a)
     )
    => Gen (f a)
    -> Maybe (Gen (I t a))
    -> TestTree
monoidalProps gx gy = testGroup "Monoidal"
                    . map (uncurry testProperty . second property)
                    . catMaybes $
    [ gy <&> \y -> ("rightIdentity", rightIdentityProp @t gx (genHB gx y))
    , gy <&> \y -> ("leftIdentity" , leftIdentityProp  @t gx (genHB y gx))
    , Just ("splittingMF", splittingMFProp @t (genHF gx) (maybeSumGen gy (genHB gx (genHF gx))))
    , Just ("unrollingMF", unrollingMFProp @t (genHF gx) (genChain gx gy))
    , Just ("toMF"       , toMFProp        @t (genHB gx gx))
    , Just ("fromSF"     , fromSFProp      @t (genHF gx))
    , gy <&> \y -> ("pureT"        , pureTProp          @t @f y)
    ]

matchableProps
    :: forall t f a.
     ( Matchable t
     , TestHBifunctor t
     , TestHFunctor (MF t)
     , TestHFunctor (SF t)
     , Functor f
     , Show (t f (MF t f) a)         , Eq (t f (MF t f) a)
     , Show (t f (Chain t (I t) f) a), Eq (t f (Chain t (I t) f) a)
     , Show (t f (Chain1 t f) a)     , Eq (t f (Chain1 t f) a)
     , Show (MF t f a)               , Eq (MF t f a)
     , Show (SF t f a)               , Eq (SF t f a)
     , Show (I t a)                  , Eq (I t a)
     , Show (f a)                    , Eq (f a)
     )
    => Gen (f a)
    -> Maybe (Gen (I t a))
    -> TestTree
matchableProps gx gy = testGroup "Matchable"
                     . map (uncurry testProperty . second property) $
    [ ("splittingSF"  , splittingSFProp   @t (genHF gx) (genHB gx (genHF gx)))
    , ("matchingMF"   , matchingMFProp    @t (genHF gx) (maybeSumGen gy (genHF gx)))
    , ("matchingChain", matchingChainProp @t (genChain gx gy) (maybeSumGen gy (genHF gx)))
    ]

monoidalProps_
    :: forall t f a.
     ( Monoidal t
     , TestHBifunctor t
     , TestHFunctor (MF t)
     , TestHFunctor (SF t)
     , CM t f
     , CS t f
     , Functor f
     , Show (t f (t f f) a)          , Eq (t f (t f f) a)
     , Show (t (t f f) f a)          , Eq (t (t f f) f a)
     , Show (t f (I t) a)            , Eq (t f (I t) a)
     , Show (t (I t) f a)            , Eq (t (I t) f a)
     , Show (t f (MF t f) a)         , Eq (t f (MF t f) a)
     , Show (t f (SF t f) a)         , Eq (t f (SF t f) a)
     , Show (t f (Chain t (I t) f) a), Eq (t f (Chain t (I t) f) a)
     , Show (t f (Chain1 t f) a)     , Eq (t f (Chain1 t f) a)
     , Show (t f f a)
     , Show (MF t f a)               , Eq (MF t f a)
     , Show (SF t f a)               , Eq (SF t f a)
     , Show (I t a)                  , Eq (I t a)
     , Show (f a)                    , Eq (f a)
     )
    => Gen (f a)
    -> Maybe (Gen (I t a))
    -> [TestTree]
monoidalProps_ gx gy = [ semigroupoidalProps @t gx, monoidalProps @t gx gy ]

matchableProps_
    :: forall t f a.
     ( Matchable t
     , TestHBifunctor t
     , TestHFunctor (MF t)
     , TestHFunctor (SF t)
     , CM t f
     , CS t f
     , Functor f
     , Show (t f (t f f) a)          , Eq (t f (t f f) a)
     , Show (t (t f f) f a)          , Eq (t (t f f) f a)
     , Show (t f (I t) a)            , Eq (t f (I t) a)
     , Show (t (I t) f a)            , Eq (t (I t) f a)
     , Show (t f (MF t f) a)         , Eq (t f (MF t f) a)
     , Show (t f (SF t f) a)         , Eq (t f (SF t f) a)
     , Show (t f (Chain t (I t) f) a), Eq (t f (Chain t (I t) f) a)
     , Show (t f (Chain1 t f) a)     , Eq (t f (Chain1 t f) a)
     , Show (t f f a)
     , Show (MF t f a)               , Eq (MF t f a)
     , Show (SF t f a)               , Eq (SF t f a)
     , Show (I t a)                  , Eq (I t a)
     , Show (f a)                    , Eq (f a)
     )
    => Gen (f a)
    -> Maybe (Gen (I t a))
    -> [TestTree]
matchableProps_ gx gy = monoidalProps_ @t gx gy ++ [ matchableProps @t gx gy ]

hbifunctorTests :: TestTree
hbifunctorTests = testGroup "HBifunctor"
    [ testGroup "Sum"      $ matchableProps_ @(:+:)   listGen Nothing
    , testGroup "Sum'"     $ matchableProps_ @Sum     listGen Nothing
    , testGroup "Product"  $ matchableProps_ @(:*:)   listGen (Just (pure Proxy))
    , testGroup "Product'" $ matchableProps_ @Product listGen (Just (pure Proxy))
    , testGroup "These1"   $ monoidalProps_  @These1  listGen Nothing
    , testGroup "Day"      $ matchableProps_ @Day     (Const . S.Sum <$> intGen)
                                                      (Just (Identity <$> intGen))
    , testGroup "Comp"     $ monoidalProps_  @Comp    (Gen.list (Range.linear 0 3) intGen)
                                                      (Just (Identity <$> intGen))

    , testGroup "LeftF"    [semigroupoidalProps @LeftF  listGen]
    , testGroup "RightF"   [semigroupoidalProps @RightF listGen]
    ]

-- prop_associating_Day :: Property
-- prop_associating_Day = property $
--     associatingProp_ @Day
--       (Const <$> intGen)
--       (Const <$> intGen)
--       (Const <$> intGen)

-- prop_associating_Comp :: Property
-- prop_associating_Comp = property $
--     associatingProp_ @Comp
--       (Gen.list (Range.linear 0 3) intGen)
--       (Gen.list (Range.linear 0 3) intGen)
--       (Gen.list (Range.linear 0 3) intGen)

-- prop_associating_LeftF :: Property
-- prop_associating_LeftF = property $
--     associatingProp_ @LeftF listGen listGen listGen

-- prop_associating_RightF :: Property
-- prop_associating_RightF = property $
--     associatingProp_ @LeftF listGen listGen listGen





-- prop_matchingSF_Sum :: Property
-- prop_matchingSF_Sum = property $
--     matchingSFProp_ @(:+:) listGen

-- prop_matchingSF_Sum' :: Property
-- prop_matchingSF_Sum' = property $
--     matchingSFProp_ @Sum listGen

-- prop_matchingSF_Prod :: Property
-- prop_matchingSF_Prod = property $
--     matchingSFProp_ @(:*:) listGen

-- prop_matchingSF_Prod' :: Property
-- prop_matchingSF_Prod' = property $
--     matchingSFProp_ @Product listGen

-- prop_matchingSF_These :: Property
-- prop_matchingSF_These = property $
--     matchingSFProp_ @These1 listGen

-- prop_matchingSF_Day :: Property
-- prop_matchingSF_Day = property $
--     matchingSFProp_ @Day $ (Const <$> intGen)

-- prop_matchingSF_Comp :: Property
-- prop_matchingSF_Comp = property $
--     matchingSFProp_ @Comp $
--       Gen.list (Range.linear 0 3) intGen

-- prop_matchingSF_LeftF :: Property
-- prop_matchingSF_LeftF = property $
--     matchingSFProp_ @LeftF listGen

-- prop_matchingSF_RightF :: Property
-- prop_matchingSF_RightF = property $
--     matchingSFProp_ @RightF listGen





-- prop_unrollingSF_Sum :: Property
-- prop_unrollingSF_Sum = property $
--     unrollingSFProp_ @(:+:) listGen

-- prop_unrollingSF_Sum' :: Property
-- prop_unrollingSF_Sum' = property $
--     unrollingSFProp_ @Sum listGen

-- prop_unrollingSF_Prod :: Property
-- prop_unrollingSF_Prod = property $
--     unrollingSFProp_ @(:*:) listGen

-- prop_unrollingSF_Prod' :: Property
-- prop_unrollingSF_Prod' = property $
--     unrollingSFProp_ @Product listGen

-- prop_unrollingSF_These :: Property
-- prop_unrollingSF_These = property $
--     unrollingSFProp_ @These1 listGen

-- prop_unrollingSF_Day :: Property
-- prop_unrollingSF_Day = property $
--     unrollingSFProp_ @Day $ (Const <$> intGen)

-- prop_unrollingSF_Comp :: Property
-- prop_unrollingSF_Comp = property $
--     unrollingSFProp_ @Comp $
--       Gen.list (Range.linear 0 3) intGen

-- prop_unrollingSF_LeftF :: Property
-- prop_unrollingSF_LeftF = property $
--     unrollingSFProp_ @LeftF listGen

-- prop_unrollingSF_RightF :: Property
-- prop_unrollingSF_RightF = property $
--     unrollingSFProp_ @RightF listGen





-- prop_consSF_Sum :: Property
-- prop_consSF_Sum = property $
--     consSFProp_ @(:+:) listGen

-- prop_consSF_Sum' :: Property
-- prop_consSF_Sum' = property $
--     consSFProp_ @Sum listGen

-- prop_consSF_Prod :: Property
-- prop_consSF_Prod = property $
--     consSFProp_ @(:*:) listGen

-- prop_consSF_Prod' :: Property
-- prop_consSF_Prod' = property $
--     consSFProp_ @Product listGen

-- prop_consSF_These :: Property
-- prop_consSF_These = property $
--     consSFProp_ @These1 listGen

-- prop_consSF_Day :: Property
-- prop_consSF_Day = property $
--     consSFProp_ @Day $ (Const <$> intGen)

-- prop_consSF_Comp :: Property
-- prop_consSF_Comp = property $
--     consSFProp_ @Comp $
--       Gen.list (Range.linear 0 3) intGen

-- prop_consSF_LeftF :: Property
-- prop_consSF_LeftF = property $
--     consSFProp_ @LeftF listGen

-- prop_consSF_RightF :: Property
-- prop_consSF_RightF = property $
--     consSFProp_ @RightF listGen






-- prop_toSF_Sum :: Property
-- prop_toSF_Sum = property $
--     toSFProp_ @(:+:) listGen

-- prop_toSF_Sum' :: Property
-- prop_toSF_Sum' = property $
--     toSFProp_ @Sum listGen

-- prop_toSF_Prod :: Property
-- prop_toSF_Prod = property $
--     toSFProp_ @(:*:) listGen

-- prop_toSF_Prod' :: Property
-- prop_toSF_Prod' = property $
--     toSFProp_ @Product listGen

-- prop_toSF_These :: Property
-- prop_toSF_These = property $
--     toSFProp_ @These1 listGen

-- prop_toSF_Day :: Property
-- prop_toSF_Day = property $
--     toSFProp_ @Day $ (Const <$> intGen)

-- prop_toSF_Comp :: Property
-- prop_toSF_Comp = property $
--     toSFProp_ @Comp $
--       Gen.list (Range.linear 0 3) intGen

-- prop_toSF_LeftF :: Property
-- prop_toSF_LeftF = property $
--     toSFProp_ @LeftF listGen

-- prop_toSF_RightF :: Property
-- prop_toSF_RightF = property $
--     toSFProp_ @RightF listGen




-- prop_biretract_Sum :: Property
-- prop_biretract_Sum = property $
--     biretractProp_ @(:+:) listGen

-- prop_biretract_Sum' :: Property
-- prop_biretract_Sum' = property $
--     biretractProp_ @Sum listGen

-- prop_biretract_Prod :: Property
-- prop_biretract_Prod = property $
--     biretractProp_ @(:*:) listGen

-- prop_biretract_Prod' :: Property
-- prop_biretract_Prod' = property $
--     biretractProp_ @Product listGen

-- prop_biretract_These :: Property
-- prop_biretract_These = property $
--     biretractProp_ @These1 listGen

-- prop_biretract_Day :: Property
-- prop_biretract_Day = property $
--     biretractProp_ @Day $ (Const . S.Sum <$> intGen)

-- prop_biretract_Comp :: Property
-- prop_biretract_Comp = property $
--     biretractProp_ @Comp $
--       Gen.list (Range.linear 0 3) intGen

-- prop_biretract_LeftF :: Property
-- prop_biretract_LeftF = property $
--     biretractProp_ @LeftF listGen

-- prop_biretract_RightF :: Property
-- prop_biretract_RightF = property $
--     biretractProp_ @RightF listGen





-- prop_binterpret_Sum :: Property
-- prop_binterpret_Sum = property $
--     binterpretProp_ @(:+:) listGen

-- prop_binterpret_Sum' :: Property
-- prop_binterpret_Sum' = property $
--     binterpretProp_ @Sum listGen

-- prop_binterpret_Prod :: Property
-- prop_binterpret_Prod = property $
--     binterpretProp_ @(:*:) listGen

-- prop_binterpret_Prod' :: Property
-- prop_binterpret_Prod' = property $
--     binterpretProp_ @Product listGen

-- prop_binterpret_These :: Property
-- prop_binterpret_These = property $
--     binterpretProp_ @These1 listGen

-- prop_binterpret_Day :: Property
-- prop_binterpret_Day = property $
--     binterpretProp_ @Day $ (Const . S.Sum <$> intGen)

-- prop_binterpret_Comp :: Property
-- prop_binterpret_Comp = property $
--     binterpretProp_ @Comp $
--       Gen.list (Range.linear 0 3) intGen

-- prop_binterpret_LeftF :: Property
-- prop_binterpret_LeftF = property $
--     binterpretProp_ @LeftF listGen

-- prop_binterpret_RightF :: Property
-- prop_binterpret_RightF = property $
--     binterpretProp_ @RightF listGen







-- prop_rightIdentity_Prod :: Property
-- prop_rightIdentity_Prod = property $
--     rightIdentityProp_ @(:*:) listGen (pure Proxy)

-- prop_rightIdentity_Prod' :: Property
-- prop_rightIdentity_Prod' = property $
--     rightIdentityProp_ @Product listGen (pure Proxy)

-- prop_rightIdentity_Day :: Property
-- prop_rightIdentity_Day = property $
--     rightIdentityProp_ @Day
--       (Const <$> intGen)
--       (Identity <$> intGen)

-- prop_rightIdentity_Comp :: Property
-- prop_rightIdentity_Comp = property $
--     rightIdentityProp_ @Comp
--       (Gen.list (Range.linear 0 3) intGen)
--       (Identity <$> intGen)







-- prop_leftIdentity_Prod :: Property
-- prop_leftIdentity_Prod = property $
--     leftIdentityProp_ @(:*:) listGen (pure Proxy)

-- prop_leftIdentity_Prod' :: Property
-- prop_leftIdentity_Prod' = property $
--     leftIdentityProp_ @Product listGen (pure Proxy)

-- prop_leftIdentity_Day :: Property
-- prop_leftIdentity_Day = property $
--     leftIdentityProp_ @Day
--       (Const <$> intGen)
--       (Identity <$> intGen)

-- prop_leftIdentity_Comp :: Property
-- prop_leftIdentity_Comp = property $
--     leftIdentityProp_ @Comp
--       (Gen.list (Range.linear 0 3) intGen)
--       (Identity <$> intGen)







-- prop_splittingMF_Sum :: Property
-- prop_splittingMF_Sum = property $
--     splittingMFProp_ @(:+:) listGen Nothing

-- prop_splittingMF_Sum' :: Property
-- prop_splittingMF_Sum' = property $
--     splittingMFProp_ @Sum listGen Nothing

-- prop_splittingMF_Prod :: Property
-- prop_splittingMF_Prod = property $
--     splittingMFProp_ @(:*:) listGen (Just (pure Proxy))

-- prop_splittingMF_Prod' :: Property
-- prop_splittingMF_Prod' = property $
--     splittingMFProp_ @Product listGen (Just (pure Proxy))

-- prop_splittingMF_These :: Property
-- prop_splittingMF_These = property $
--     splittingMFProp_ @These1 listGen Nothing

-- prop_splittingMF_Day :: Property
-- prop_splittingMF_Day = property $
--     splittingMFProp_ @Day
--       (Const <$> intGen)
--       (Just (Identity <$> intGen))

-- prop_splittingMF_Comp :: Property
-- prop_splittingMF_Comp = property $
--     splittingMFProp_ @Comp
--       (Gen.list (Range.linear 0 3) intGen)
--       (Just (Identity <$> intGen))





-- prop_unrollingMF_Sum' :: Property
-- prop_unrollingMF_Sum' = property $
--     unrollingMFProp_ @Sum listGen Nothing

-- prop_unrollingMF_Prod :: Property
-- prop_unrollingMF_Prod = property $
--     unrollingMFProp_ @(:*:) listGen (Just (pure Proxy))

-- prop_unrollingMF_Prod' :: Property
-- prop_unrollingMF_Prod' = property $
--     unrollingMFProp_ @Product listGen (Just (pure Proxy))

-- prop_unrollingMF_These :: Property
-- prop_unrollingMF_These = property $
--     unrollingMFProp_ @These1 listGen Nothing

-- prop_unrollingMF_Day :: Property
-- prop_unrollingMF_Day = property $
--     unrollingMFProp_ @Day
--       (Const <$> intGen)
--       (Just (Identity <$> intGen))

-- prop_unrollingMF_Comp :: Property
-- prop_unrollingMF_Comp = property $
--     unrollingMFProp_ @Comp
--       (Gen.list (Range.linear 0 3) intGen)
--       (Just (Identity <$> intGen))





-- prop_toMF_Sum :: Property
-- prop_toMF_Sum = property $
--     toMFProp_ @(:+:) listGen

-- prop_toMF_Sum' :: Property
-- prop_toMF_Sum' = property $
--     toMFProp_ @Sum listGen

-- prop_toMF_Prod :: Property
-- prop_toMF_Prod = property $
--     toMFProp_ @(:*:) listGen

-- prop_toMF_Prod' :: Property
-- prop_toMF_Prod' = property $
--     toMFProp_ @Product listGen

-- prop_toMF_These :: Property
-- prop_toMF_These = property $
--     toMFProp_ @These1 listGen

-- prop_toMF_Day :: Property
-- prop_toMF_Day = property $
--     toMFProp_ @Day (Const <$> intGen)

-- prop_toMF_Comp :: Property
-- prop_toMF_Comp = property $
--     toMFProp_ @Comp (Gen.list (Range.linear 0 3) intGen)





-- prop_fromSF_Sum :: Property
-- prop_fromSF_Sum = property $
--     fromSFProp_ @(:+:) listGen

-- prop_fromSF_Sum' :: Property
-- prop_fromSF_Sum' = property $
--     fromSFProp_ @Sum listGen

-- prop_fromSF_Prod :: Property
-- prop_fromSF_Prod = property $
--     fromSFProp_ @(:*:) listGen

-- prop_fromSF_Prod' :: Property
-- prop_fromSF_Prod' = property $
--     fromSFProp_ @Product listGen

-- prop_fromSF_These :: Property
-- prop_fromSF_These = property $
--     fromSFProp_ @These1 listGen

-- prop_fromSF_Day :: Property
-- prop_fromSF_Day = property $
--     fromSFProp_ @Day (Const <$> intGen)

-- prop_fromSF_Comp :: Property
-- prop_fromSF_Comp = property $
--     fromSFProp_ @Comp (Gen.list (Range.linear 0 3) intGen)







-- prop_pureT_Prod :: Property
-- prop_pureT_Prod = property $
--     pureTProp @(:*:) @[] @_ @Int (pure Proxy)

-- prop_pureT_Prod' :: Property
-- prop_pureT_Prod' = property $
--     pureTProp @Product @[] @_ @Int (pure Proxy)

-- prop_pureT_Day :: Property
-- prop_pureT_Day = property $
--     pureTProp @Day @[] (Identity <$> intGen)

-- prop_pureT_Comp :: Property
-- prop_pureT_Comp = property $
--     pureTProp @Comp @[] (Identity <$> intGen)







-- prop_splittingSF_Sum :: Property
-- prop_splittingSF_Sum = property $
--     splittingSFProp_ @(:+:) listGen

-- prop_splittingSF_Sum' :: Property
-- prop_splittingSF_Sum' = property $
--     splittingSFProp_ @Sum listGen

-- prop_splittingSF_Prod :: Property
-- prop_splittingSF_Prod = property $
--     splittingSFProp_ @(:*:) listGen

-- prop_splittingSF_Prod' :: Property
-- prop_splittingSF_Prod' = property $
--     splittingSFProp_ @Product listGen

-- -- prop_splittingSF_These :: Property
-- -- prop_splittingSF_These = property $
-- --     splittingSFProp_ @These1 listGen

-- prop_splittingSF_Day :: Property
-- prop_splittingSF_Day = property $
--     splittingSFProp_ @Day (Const <$> intGen)







-- prop_matchingMF_Sum :: Property
-- prop_matchingMF_Sum = property $
--     matchingMFProp_ @(:+:) listGen Nothing

-- prop_matchingMF_Sum' :: Property
-- prop_matchingMF_Sum' = property $
--     matchingMFProp_ @Sum listGen Nothing

-- prop_matchingMF_Prod :: Property
-- prop_matchingMF_Prod = property $
--     matchingMFProp_ @(:*:) listGen (Just (pure Proxy))

-- prop_matchingMF_Prod' :: Property
-- prop_matchingMF_Prod' = property $
--     matchingMFProp_ @Product listGen (Just (pure Proxy))

-- -- prop_matchingMF_These :: Property
-- -- prop_matchingMF_These = property $
-- --     matchingMFProp_ @These1 listGen Nothing

-- prop_matchingMF_Day :: Property
-- prop_matchingMF_Day = property $
--     matchingMFProp_ @Day
--       (Const <$> intGen)
--       (Just (Identity <$> intGen))






-- prop_matchingChain_Sum :: Property
-- prop_matchingChain_Sum = property $
--     matchingChainProp_ @(:+:) listGen Nothing

-- prop_matchingChain_Sum' :: Property
-- prop_matchingChain_Sum' = property $
--     matchingChainProp_ @Sum listGen Nothing

-- prop_matchingChain_Prod :: Property
-- prop_matchingChain_Prod = property $
--     matchingChainProp_ @(:*:) listGen (Just (pure Proxy))

-- prop_matchingChain_Prod' :: Property
-- prop_matchingChain_Prod' = property $
--     matchingChainProp_ @Product listGen (Just (pure Proxy))

-- -- prop_matchingChain_These :: Property
-- -- prop_matchingChain_These = property $
-- --     matchingChainProp_ @These1 listGen Nothing

-- prop_matchingChain_Day :: Property
-- prop_matchingChain_Day = property $
--     matchingChainProp_ @Day
--       (Const <$> intGen)
--       (Just (Identity <$> intGen))
