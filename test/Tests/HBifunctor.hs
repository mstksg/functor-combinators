module Tests.HBifunctor (
  hbifunctorTests,
) where

import Control.Applicative
import Control.Monad.Freer.Church
import Control.Natural.IsoF
import Data.Bifunctor
import Data.Bifunctor.Joker
import Data.Functor
import Data.Functor.Combinator
import Data.Functor.Identity
import Data.Functor.Product
import Data.Functor.Sum
import Data.HBifunctor.Associative
import Data.HBifunctor.Tensor
import Data.HFunctor.Chain
import Data.Maybe
import Data.Proxy
import qualified Data.Semigroup as S
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Tests.Util

hbimapProp ::
  forall t f g m a.
  ( HBifunctor t
  , Monad m
  , Show (t f g a)
  , Eq (t f g a)
  ) =>
  Gen (t f g a) ->
  PropertyT m ()
hbimapProp gx = do
  x <- forAll gx
  hbimap id id x === x

associatingProp ::
  forall t f g h m a.
  ( Associative t
  , FunctorBy t f
  , FunctorBy t g
  , FunctorBy t h
  , Monad m
  , Show (t f (t g h) a)
  , Show (t (t f g) h a)
  , Eq (t f (t g h) a)
  , Eq (t (t f g) h a)
  ) =>
  Gen (t f (t g h) a) ->
  Gen (t (t f g) h a) ->
  PropertyT m ()
associatingProp = isoProp (associating @t)

matchingNEProp ::
  forall t f m a.
  ( Associative t
  , FunctorBy t f
  , Monad m
  , Show (f a)
  , Eq (f a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (t f (NonEmptyBy t f) a)
  , Eq (t f (NonEmptyBy t f) a)
  ) =>
  Gen (NonEmptyBy t f a) ->
  Gen (f a) ->
  Gen (t f (NonEmptyBy t f) a) ->
  PropertyT m ()
matchingNEProp gx gy gz = isoProp (matchingNE @t) gx (sumGen gy gz)

unrollingNEProp ::
  forall t f m a.
  ( SemigroupIn t f
  , Monad m
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (f a)
  , Eq (f a)
  , Show (t f (Chain1 t f) a)
  , Eq (t f (Chain1 t f) a)
  ) =>
  Gen (NonEmptyBy t f a) ->
  Gen (Chain1 t f a) ->
  PropertyT m ()
unrollingNEProp = isoProp (unrollingNE @t)

consNEProp ::
  forall t f m a.
  ( Associative t
  , Monad m
  , Show (t f (NonEmptyBy t f) a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  ) =>
  Gen (t f (NonEmptyBy t f) a) ->
  PropertyT m ()
consNEProp gx = do
  x <- forAll gx
  appendNE (hleft inject x) === consNE x

toNonEmptyByProp ::
  forall t f m a.
  ( Associative t
  , Monad m
  , Show (t f f a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  ) =>
  Gen (t f f a) ->
  PropertyT m ()
toNonEmptyByProp gx = do
  x <- forAll gx
  appendNE (hbimap inject inject x) === toNonEmptyBy x

biretractProp ::
  forall t f m a.
  ( SemigroupIn t f
  , Interpret (NonEmptyBy t) f
  , Monad m
  , Show (t f f a)
  , Show (f a)
  , Eq (f a)
  ) =>
  Gen (t f f a) ->
  PropertyT m ()
biretractProp gx = do
  x <- forAll gx
  retract (appendNE (hbimap inject inject x)) === biretract x

binterpretProp ::
  forall t f m a.
  ( SemigroupIn t f
  , Monad m
  , Show (t f f a)
  , Show (f a)
  , Eq (f a)
  ) =>
  Gen (t f f a) ->
  PropertyT m ()
binterpretProp gx = do
  x <- forAll gx
  biretract x === binterpret id id x

rightIdentityProp ::
  forall t i f m a.
  ( Tensor t i
  , FunctorBy t f
  , Monad m
  , Show (f a)
  , Eq (f a)
  , Show (t f i a)
  , Eq (t f i a)
  ) =>
  Gen (f a) ->
  Gen (t f i a) ->
  PropertyT m ()
rightIdentityProp = isoProp (rightIdentity @t)

leftIdentityProp ::
  forall t i g m a.
  ( Tensor t i
  , FunctorBy t g
  , Monad m
  , Show (g a)
  , Eq (g a)
  , Show (t i g a)
  , Eq (t i g a)
  ) =>
  Gen (g a) ->
  Gen (t i g a) ->
  PropertyT m ()
leftIdentityProp = isoProp (leftIdentity @t)

splittingLBProp ::
  forall t i f m a.
  ( Tensor t i
  , Monad m
  , Show (i a)
  , Eq (i a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  , Show (t f (ListBy t f) a)
  , Eq (t f (ListBy t f) a)
  ) =>
  Gen (ListBy t f a) ->
  Gen ((i :+: t f (ListBy t f)) a) ->
  PropertyT m ()
splittingLBProp = isoProp (splittingLB @t)

unrollingProp ::
  forall t i f m a.
  ( MonoidIn t i f
  , Monad m
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  , Show (i a)
  , Eq (i a)
  , Show (t f (Chain t i f) a)
  , Eq (t f (Chain t i f) a)
  ) =>
  Gen (ListBy t f a) ->
  Gen (Chain t i f a) ->
  PropertyT m ()
unrollingProp = isoProp (unrolling @t)

toListByProp ::
  forall t i f m a.
  ( Tensor t i
  , Monad m
  , Show (t f f a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  ) =>
  Gen (t f f a) ->
  PropertyT m ()
toListByProp gx = do
  x <- forAll gx
  reviewF (splittingLB @t) (R1 (hright (inject @(ListBy t)) x)) === toListBy @t x

fromNEProp ::
  forall t i f m a.
  ( Tensor t i
  , Monad m
  , Show (NonEmptyBy t f a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  ) =>
  Gen (NonEmptyBy t f a) ->
  PropertyT m ()
fromNEProp gx = do
  x <- forAll gx
  reviewF (splittingLB @t) (R1 (splitNE @t x)) === fromNE @t x

pureTProp ::
  forall t i f m a.
  ( MonoidIn t i f
  , Interpret (ListBy t) f
  , Monad m
  , Show (i a)
  , Show (f a)
  , Eq (f a)
  ) =>
  Gen (i a) ->
  PropertyT m ()
pureTProp gx = do
  x <- forAll gx
  retract (reviewF (splittingLB @t) (L1 x)) === pureT @t @_ @f x

splittingNEProp ::
  forall t i f m a.
  ( Matchable t i
  , FunctorBy t f
  , Monad m
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (t f (ListBy t f) a)
  , Eq (t f (ListBy t f) a)
  ) =>
  Gen (NonEmptyBy t f a) ->
  Gen (t f (ListBy t f) a) ->
  PropertyT m ()
splittingNEProp = isoProp (splittingNE @t)

matchingLBProp ::
  forall t i f m a.
  ( Matchable t i
  , FunctorBy t f
  , Monad m
  , Show (i a)
  , Eq (i a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  ) =>
  Gen (ListBy t f a) ->
  Gen ((i :+: NonEmptyBy t f) a) ->
  PropertyT m ()
matchingLBProp = isoProp (matchingLB @t)

matchingChainProp ::
  forall t i f m a.
  ( Matchable t i
  , FunctorBy t f
  , Monad m
  , Show (f a)
  , Eq (f a)
  , Show (i a)
  , Eq (i a)
  , Show (t f (Chain1 t f) a)
  , Eq (t f (Chain1 t f) a)
  , Show (t f (Chain t i f) a)
  , Eq (t f (Chain t i f) a)
  ) =>
  Gen (Chain t i f a) ->
  Gen ((i :+: Chain1 t f) a) ->
  PropertyT m ()
matchingChainProp = isoProp (matchingChain @t)

genChain ::
  forall t i f m a.
  (MonadGen m, TestHBifunctor t) =>
  m (f a) ->
  Maybe (m (i a)) ->
  m (Chain t i f a)
genChain gx gy = go
  where
    go = case gy of
      Nothing -> More <$> genHB @t gx go
      Just gy' ->
        Gen.bool >>= \case
          False -> Done <$> gy'
          True -> More <$> genHB @t gx go

maybeSumGen ::
  Maybe (Gen (f a)) ->
  Gen (g a) ->
  Gen ((f :+: g) a)
maybeSumGen = maybe (fmap R1) sumGen

hbifunctorProps ::
  forall t f a.
  ( TestHBifunctor t
  , Show (t f f a)
  , Eq (t f f a)
  ) =>
  Gen (f a) ->
  TestTree
hbifunctorProps gx =
  testGroup
    "HBifunctor"
    [testProperty "hbimap" . property $ hbimapProp @t (genHB gx gx)]

associativeProps ::
  forall t f a.
  ( SemigroupIn t f
  , Interpret (NonEmptyBy t) f
  , TestHBifunctor t
  , TestHFunctor (NonEmptyBy t)
  , Show (t f (t f f) a)
  , Eq (t f (t f f) a)
  , Show (t (t f f) f a)
  , Eq (t (t f f) f a)
  , Show (t f f a)
  , Show (t f (NonEmptyBy t f) a)
  , Eq (t f (NonEmptyBy t f) a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (t f (Chain1 t f) a)
  , Eq (t f (Chain1 t f) a)
  , Show (f a)
  , Eq (f a)
  , TestHFunctorBy (NonEmptyBy t) f
  ) =>
  Gen (f a) ->
  TestTree
associativeProps gx =
  testGroup "Associative"
    . map (uncurry testProperty . second property)
    $ [ ("associating", associatingProp @t (genHB gx (genHB gx gx)) (genHB (genHB gx gx) gx))
      , ("matchingNE", matchingNEProp @t (genHF gx) gx (genHB gx (genHF gx)))
      , ("unrollingNE", unrollingNEProp @t (genHF gx) (genHF gx))
      , ("consNE", consNEProp @t (genHB gx (genHF gx)))
      , ("toNonEmptyBy", toNonEmptyByProp @t (genHB gx gx))
      , ("biretract", biretractProp @t (genHB gx gx))
      , ("binterpret", binterpretProp @t (genHB gx gx))
      ]

tensorProps ::
  forall t i f a.
  ( MonoidIn t i f
  , Interpret (ListBy t) f
  , TestHBifunctor t
  , TestHFunctor (ListBy t)
  , TestHFunctor (NonEmptyBy t)
  , Show (t f i a)
  , Eq (t f i a)
  , Show (t i f a)
  , Eq (t i f a)
  , Show (t f (ListBy t f) a)
  , Eq (t f (ListBy t f) a)
  , Show (t f (Chain t i f) a)
  , Eq (t f (Chain t i f) a)
  , Show (t f f a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  , Show (NonEmptyBy t f a)
  , Show (i a)
  , Eq (i a)
  , Show (f a)
  , Eq (f a)
  , TestHFunctorBy (ListBy t) f
  , TestHFunctorBy (NonEmptyBy t) f
  ) =>
  Gen (f a) ->
  Maybe (Gen (i a)) ->
  TestTree
tensorProps gx gy =
  testGroup "Tensor"
    . map (uncurry testProperty . second property)
    . catMaybes
    $ [ gy <&> \y -> ("rightIdentity", rightIdentityProp @t gx (genHB gx y))
      , gy <&> \y -> ("leftIdentity", leftIdentityProp @t gx (genHB y gx))
      , Just ("splittingLB", splittingLBProp @t (genHF gx) (maybeSumGen gy (genHB gx (genHF gx))))
      , Just ("unrolling", unrollingProp @t (genHF gx) (genChain gx gy))
      , Just ("toListBy", toListByProp @t (genHB gx gx))
      , Just ("fromNE", fromNEProp @t (genHF gx))
      , gy <&> \y -> ("pureT", pureTProp @t @_ @f y)
      ]

matchableProps ::
  forall t i f a.
  ( Matchable t i
  , FunctorBy t f
  , TestHBifunctor t
  , TestHFunctor (ListBy t)
  , TestHFunctor (NonEmptyBy t)
  , Show (t f (ListBy t f) a)
  , Eq (t f (ListBy t f) a)
  , Show (t f (Chain t i f) a)
  , Eq (t f (Chain t i f) a)
  , Show (t f (Chain1 t f) a)
  , Eq (t f (Chain1 t f) a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (i a)
  , Eq (i a)
  , Show (f a)
  , Eq (f a)
  , TestHFunctorBy (ListBy t) f
  , TestHFunctorBy (NonEmptyBy t) f
  ) =>
  Gen (f a) ->
  Maybe (Gen (i a)) ->
  TestTree
matchableProps gx gy =
  testGroup "Matchable"
    . map (uncurry testProperty . second property)
    $ [ ("splittingNE", splittingNEProp @t (genHF gx) (genHB gx (genHF gx)))
      , ("matchingLB", matchingLBProp @t (genHF gx) (maybeSumGen gy (genHF gx)))
      , ("matchingChain", matchingChainProp @t (genChain gx gy) (maybeSumGen gy (genHF gx)))
      ]

associativeProps_ ::
  forall t f a.
  ( SemigroupIn t f
  , Interpret (NonEmptyBy t) f
  , TestHBifunctor t
  , TestHFunctor (NonEmptyBy t)
  , Show (t f (t f f) a)
  , Eq (t f (t f f) a)
  , Show (t (t f f) f a)
  , Eq (t (t f f) f a)
  , Show (t f f a)
  , Eq (t f f a)
  , Show (t f (NonEmptyBy t f) a)
  , Eq (t f (NonEmptyBy t f) a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (t f (Chain1 t f) a)
  , Eq (t f (Chain1 t f) a)
  , Show (f a)
  , Eq (f a)
  , TestHFunctorBy (NonEmptyBy t) f
  ) =>
  Gen (f a) ->
  [TestTree]
associativeProps_ gx = [hbifunctorProps @t gx, associativeProps @t gx]

tensorProps_ ::
  forall t i f a.
  ( MonoidIn t i f
  , Interpret (NonEmptyBy t) f
  , Interpret (ListBy t) f
  , TestHBifunctor t
  , TestHFunctor (ListBy t)
  , TestHFunctor (NonEmptyBy t)
  , Show (t f (t f f) a)
  , Eq (t f (t f f) a)
  , Show (t (t f f) f a)
  , Eq (t (t f f) f a)
  , Show (t f i a)
  , Eq (t f i a)
  , Show (t i f a)
  , Eq (t i f a)
  , Show (t f (ListBy t f) a)
  , Eq (t f (ListBy t f) a)
  , Show (t f (NonEmptyBy t f) a)
  , Eq (t f (NonEmptyBy t f) a)
  , Show (t f (Chain t i f) a)
  , Eq (t f (Chain t i f) a)
  , Show (t f (Chain1 t f) a)
  , Eq (t f (Chain1 t f) a)
  , Show (t f f a)
  , Eq (t f f a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (i a)
  , Eq (i a)
  , Show (f a)
  , Eq (f a)
  , TestHFunctorBy (NonEmptyBy t) f
  , TestHFunctorBy (ListBy t) f
  ) =>
  Gen (f a) ->
  Maybe (Gen (i a)) ->
  [TestTree]
tensorProps_ gx gy = associativeProps_ @t gx ++ [tensorProps @t gx gy]

matchableProps_ ::
  forall t i f a.
  ( Matchable t i
  , Interpret (NonEmptyBy t) f
  , Interpret (ListBy t) f
  , MonoidIn t i f
  , TestHBifunctor t
  , TestHFunctor (ListBy t)
  , TestHFunctor (NonEmptyBy t)
  , Show (t f (t f f) a)
  , Eq (t f (t f f) a)
  , Show (t (t f f) f a)
  , Eq (t (t f f) f a)
  , Show (t f i a)
  , Eq (t f i a)
  , Show (t i f a)
  , Eq (t i f a)
  , Show (t f (ListBy t f) a)
  , Eq (t f (ListBy t f) a)
  , Show (t f (NonEmptyBy t f) a)
  , Eq (t f (NonEmptyBy t f) a)
  , Show (t f (Chain t i f) a)
  , Eq (t f (Chain t i f) a)
  , Show (t f (Chain1 t f) a)
  , Eq (t f (Chain1 t f) a)
  , Show (t f f a)
  , Eq (t f f a)
  , Show (ListBy t f a)
  , Eq (ListBy t f a)
  , Show (NonEmptyBy t f a)
  , Eq (NonEmptyBy t f a)
  , Show (i a)
  , Eq (i a)
  , Show (f a)
  , Eq (f a)
  , TestHFunctorBy (ListBy t) f
  , TestHFunctorBy (NonEmptyBy t) f
  ) =>
  Gen (f a) ->
  Maybe (Gen (i a)) ->
  [TestTree]
matchableProps_ gx gy = tensorProps_ @t gx gy ++ [matchableProps @t gx gy]

hbifunctorTests :: TestTree
hbifunctorTests =
  testGroup
    "HBifunctors"
    [ testGroup "Sum" $ matchableProps_ @(:+:) listGen Nothing
    , testGroup "Sum'" $ matchableProps_ @Sum listGen Nothing
    , testGroup "Product" $ matchableProps_ @(:*:) listGen (Just (pure Proxy))
    , testGroup "Product'" $ matchableProps_ @Product listGen (Just (pure Proxy))
    , testGroup "These1" $ tensorProps_ @These1 listGen Nothing
    , testGroup "LeftF" $ associativeProps_ @LeftF listGen
    , testGroup "Joker" $ associativeProps_ @Joker listGen
    , testGroup "RightF" $ associativeProps_ @RightF listGen
    , testGroup "Day" $
        matchableProps_ @Day
          (Const . S.Sum <$> intGen)
          (Just (Identity <$> intGen))
    , testGroup "Comp" $
        tensorProps_ @Comp
          (Gen.list (Range.linear 0 3) intGen)
          (Just (Identity <$> intGen))
    ]
