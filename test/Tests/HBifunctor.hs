{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE TypeOperators       #-}

module Tests.HBifunctor (
    hbifunctorTests
  ) where

import           Control.Applicative
import           Control.Monad.Freer.Church
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Bifunctor.Joker
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

hbimapProp
    :: forall t f g m a.
     ( HBifunctor t
     , Monad m
     , Show (t f g a), Eq (t f g a)
     )
    => Gen (t f g a)
    -> PropertyT m ()
hbimapProp gx = do
    x <- forAll gx
    hbimap id id x === x

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

hbifunctorProps
    :: forall t f a.
     ( TestHBifunctor t
     , Show (t f f a), Eq (t f f a)
     )
    => Gen (f a)
    -> TestTree
hbifunctorProps gx = testGroup "HBifunctor"
                       . map (uncurry testProperty . second property) $
    [ ("hbimap", hbimapProp @t (genHB gx gx))
    ]

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

semigroupoidalProps_
    :: forall t f a.
     ( Semigroupoidal t
     , TestHBifunctor t
     , TestHFunctor (SF t)
     , CS t f
     , Functor f
     , Show (t f (t f f) a)     , Eq (t f (t f f) a)
     , Show (t (t f f) f a)     , Eq (t (t f f) f a)
     , Show (t f f a)           , Eq (t f f a)
     , Show (t f (SF t f) a)    , Eq (t f (SF t f) a)
     , Show (SF t f a)          , Eq (SF t f a)
     , Show (t f (Chain1 t f) a), Eq (t f (Chain1 t f) a)
     , Show (f a)               , Eq (f a)
     )
    => Gen (f a)
    -> [TestTree]
semigroupoidalProps_ gx = [ hbifunctorProps @t gx, semigroupoidalProps @t gx ]

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
     , Show (t f f a)                , Eq (t f f a)
     , Show (MF t f a)               , Eq (MF t f a)
     , Show (SF t f a)               , Eq (SF t f a)
     , Show (I t a)                  , Eq (I t a)
     , Show (f a)                    , Eq (f a)
     )
    => Gen (f a)
    -> Maybe (Gen (I t a))
    -> [TestTree]
monoidalProps_ gx gy = semigroupoidalProps_ @t gx ++ [ monoidalProps @t gx gy ]

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
     , Show (t f f a)                , Eq (t f f a)
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
hbifunctorTests = testGroup "HBifunctors"
    [ testGroup "Sum"      $ matchableProps_      @(:+:)   listGen Nothing
    , testGroup "Sum'"     $ matchableProps_      @Sum     listGen Nothing
    , testGroup "Product"  $ matchableProps_      @(:*:)   listGen (Just (pure Proxy))
    , testGroup "Product'" $ matchableProps_      @Product listGen (Just (pure Proxy))
    , testGroup "These1"   $ monoidalProps_       @These1  listGen Nothing
    , testGroup "LeftF"    $ semigroupoidalProps_ @LeftF   listGen
    , testGroup "Joker"    $ semigroupoidalProps_ @Joker   listGen
    , testGroup "RightF"   $ semigroupoidalProps_ @RightF  listGen
    , testGroup "Day"      $ matchableProps_      @Day     (Const . S.Sum <$> intGen)
                                                           (Just (Identity <$> intGen))
    , testGroup "Comp"     $ monoidalProps_       @Comp    (Gen.list (Range.linear 0 3) intGen)
                                                           (Just (Identity <$> intGen))

    ]
