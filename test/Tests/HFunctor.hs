module Tests.HFunctor (
  hfunctorTests,
) where

import Control.Applicative
import Control.Applicative.Backwards
import qualified Control.Applicative.Free.Fast as FAF
import qualified Control.Applicative.Free.Final as FA
import Data.Bifunctor
import Data.Functor.Bind
import Data.Functor.Combinator
import Data.Functor.Product
import Data.Functor.Reverse
import Data.Functor.Sum
import Data.HFunctor
import qualified Data.Semigroup as S
import Data.Void
import GHC.Generics (M1 (..), Meta (..))
import Hedgehog
import qualified Hedgehog.Gen as Gen
import qualified Hedgehog.Range as Range
import Test.Tasty
import Test.Tasty.Hedgehog
import Tests.Util

hmapProp ::
  forall t f m a.
  ( HFunctor t
  , Monad m
  , Show (t f a)
  , Eq (t f a)
  ) =>
  Gen (t f a) ->
  PropertyT m ()
hmapProp gx = do
  x <- forAll gx
  hmap id x === x

retractingProp ::
  forall t f m a.
  ( Interpret t f
  , Monad m
  , Show (f a)
  , Show (t f a)
  , Eq (f a)
  ) =>
  Gen (f a) ->
  PropertyT m ()
retractingProp gx = do
  x <- forAll gx
  tripping x (inject @t) (Just . retract)

interpretProp ::
  forall t f m a.
  ( Interpret t f
  , Monad m
  , Show (f a)
  , Show (t f a)
  , Eq (f a)
  ) =>
  Gen (t f a) ->
  PropertyT m ()
interpretProp gx = do
  x <- forAll gx
  retract x === interpret id x

hbindInjectProp ::
  forall t f m a.
  ( HBind t
  , Monad m
  , Show (t f a)
  , Eq (t f a)
  ) =>
  Gen (t f a) ->
  PropertyT m ()
hbindInjectProp gx = do
  x <- forAll gx
  hbind inject x === x

hbindhjoinProp ::
  forall t f m a.
  ( HBind t
  , Monad m
  , Show (t (t f) a)
  , Show (t f a)
  , Eq (t f a)
  ) =>
  Gen (t (t f) a) ->
  PropertyT m ()
hbindhjoinProp gx = do
  x <- forAll gx
  hbind id x === hjoin x

hjoinAssocProp ::
  forall t f m a.
  ( HBind t
  , Monad m
  , Show (t (t (t f)) a)
  , Show (t f a)
  , Eq (t f a)
  ) =>
  Gen (t (t (t f)) a) ->
  PropertyT m ()
hjoinAssocProp gx = do
  x <- forAll gx
  hjoin (hjoin x) === hjoin (hmap hjoin x)

hfunctorProps ::
  forall t f a.
  ( TestHFunctor t
  , Show (t f a)
  , Eq (t f a)
  , TestHFunctorBy t f
  ) =>
  Gen (f a) ->
  TestTree
hfunctorProps gx =
  testGroup
    "HFunctor"
    [testProperty "hmap" . property $ hmapProp @t (genHF gx)]

hbindProps ::
  forall t f a.
  ( HBind t
  , TestHFunctor t
  , Show (t f a)
  , Eq (t f a)
  , Show (t (t f) a)
  , Show (t (t (t f)) a)
  , TestHFunctorBy t (t (t f))
  , TestHFunctorBy t (t f)
  , TestHFunctorBy t f
  ) =>
  Gen (f a) ->
  TestTree
hbindProps gx =
  testGroup "HBind"
    . map (uncurry testProperty . second property)
    $ [ ("hbindInject", hbindInjectProp @t (genHF gx))
      , ("hbindhjoin", hbindhjoinProp @t (genHF (genHF gx)))
      , ("hjoinAssoc", hjoinAssocProp @t (genHF (genHF (genHF gx))))
      ]

interpretProps ::
  forall t f a.
  ( Interpret t f
  , TestHFunctor t
  , Show (f a)
  , Eq (f a)
  , Show (t f a)
  , TestHFunctorBy t f
  ) =>
  Gen (f a) ->
  TestTree
interpretProps gx =
  testGroup "Interpret"
    . map (uncurry testProperty . second property)
    $ [ ("retracting", retractingProp @t gx)
      , ("interpret", interpretProp @t (genHF gx))
      ]

hbindProps_ ::
  forall t f a.
  ( HBind t
  , TestHFunctor t
  , Show (t f a)
  , Eq (t f a)
  , Show (t (t f) a)
  , Show (t (t (t f)) a)
  , TestHFunctorBy t f
  , TestHFunctorBy t (t f)
  , TestHFunctorBy t (t (t f))
  ) =>
  Gen (f a) ->
  [TestTree]
hbindProps_ gx =
  [ hfunctorProps @t gx
  , hbindProps @t gx
  ]

interpretProps_ ::
  forall t f a.
  ( Interpret t f
  , TestHFunctor t
  , Show (f a)
  , Eq (f a)
  , Show (t f a)
  , Eq (t f a)
  , TestHFunctorBy t f
  ) =>
  Gen (f a) ->
  [TestTree]
interpretProps_ gx =
  [ hfunctorProps @t gx
  , interpretProps @t gx
  ]

bindInterpProps_ ::
  forall t f a.
  ( HBind t
  , Interpret t f
  , TestHFunctor t
  , Show (f a)
  , Eq (f a)
  , Show (t f a)
  , Eq (t f a)
  , Show (t (t f) a)
  , Show (t (t (t f)) a)
  , TestHFunctorBy t (t (t f))
  , TestHFunctorBy t (t f)
  , TestHFunctorBy t f
  ) =>
  Gen (f a) ->
  [TestTree]
bindInterpProps_ gx =
  [ hfunctorProps @t gx
  , hbindProps @t gx
  , interpretProps @t gx
  ]

hfunctorTests :: TestTree
hfunctorTests =
  testGroup
    "HFunctors"
    [ testGroup "Ap" $ bindInterpProps_ @Ap @_ @Void (Const . S.Sum <$> intGen)
    , testGroup "Ap'" $ bindInterpProps_ @FA.Ap (Const . S.Sum <$> intGen)
    , testGroup "Ap''" $ bindInterpProps_ @FAF.Ap (Const . S.Sum <$> intGen)
    , -- , testGroup "Alt"  $ bindInterpProps_ @Alt    (Const . S.Sum <$> intGen)  -- TODO
      testGroup "Coyoneda" $ bindInterpProps_ @Coyoneda listGen
    , testGroup "WrappedApplicative" $ bindInterpProps_ @WrappedApplicative listGen
    , testGroup "MaybeApply" $ bindInterpProps_ @MaybeApply listGen
    , testGroup "Lift" $ bindInterpProps_ @Lift listGen
    , testGroup "ListF" $ bindInterpProps_ @ListF (Gen.list (Range.linear 0 3) intGen)
    , testGroup "NonEmptyF" $ bindInterpProps_ @NonEmptyF (Gen.list (Range.linear 0 3) intGen)
    , testGroup "MaybeF" $ bindInterpProps_ @MaybeF listGen
    , testGroup "MapF" $ interpretProps_ @(MapF Ordering) (Gen.list (Range.linear 0 3) intGen)
    , testGroup "NEMapF" $ interpretProps_ @(NEMapF Ordering) (Gen.list (Range.linear 0 3) intGen)
    , testGroup "Free1" $ bindInterpProps_ @Free1 (Gen.list (Range.linear 0 3) intGen)
    , testGroup "Free" $ bindInterpProps_ @Free (Gen.list (Range.linear 0 3) intGen)
    , testGroup "Ap1" $ bindInterpProps_ @Ap1 (Const . S.Sum <$> intGen)
    , testGroup "EnvT" $ bindInterpProps_ @(EnvT Ordering) listGen
    , testGroup "IdentityT" $ bindInterpProps_ @IdentityT listGen
    , -- , testGroup "ReaderT"    [ hfunctorProps @(ReaderT Int) listGen ]    -- no Show
      testGroup "These1" $ bindInterpProps_ @(These1 []) listGen
    , testGroup "Reverse" $ bindInterpProps_ @Reverse listGen
    , testGroup "Backwards" $ bindInterpProps_ @Backwards listGen
    , testGroup "Comp" [hfunctorProps @(Comp []) (Gen.list (Range.linear 0 3) intGen)]
    , testGroup "Comp'" [hfunctorProps @((:*:) []) (Gen.list (Range.linear 0 3) intGen)]
    , testGroup "Step" $ bindInterpProps_ @Step listGen
    , testGroup "Steps" $ interpretProps_ @Steps listGen
    , testGroup "Flagged" $ bindInterpProps_ @Flagged listGen
    , testGroup "M1" $ bindInterpProps_ @(M1 () ('MetaData "" "" "" 'True)) listGen
    , testGroup "Product" $ bindInterpProps_ @((:*:) []) listGen
    , testGroup "Product'" $ bindInterpProps_ @(Product []) listGen
    , testGroup "Sum" $ bindInterpProps_ @((:+:) []) listGen
    , testGroup "Sum'" $ bindInterpProps_ @(Sum []) listGen
    , testGroup "ProxyF" $ hbindProps_ @ProxyF listGen
    , testGroup "RightF" $ hbindProps_ @(RightF []) listGen
    ]
