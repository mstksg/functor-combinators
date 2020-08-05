{-# OPTIONS_GHC -Wno-orphans      #-}

module Tests.Util (
    isoProp
  , sumGen
  , intGen
  , listGen
  , TestHFunctor(..)
  , TestHBifunctor(..)
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards
import           Control.Applicative.Lift
import           Control.Monad.Freer.Church
import           Control.Natural.IsoF
import           Data.Bifunctor.Joker
import           Data.Constraint.Trivial
import           Data.Function
import           Data.Functor
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Combinator
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Reverse
import           Data.Functor.Sum
import           Data.GADT.Show
import           Data.HBifunctor.Tensor
import           Data.HFunctor.Chain
import           Data.Kind
import           Data.Semigroup                 (Any(..))
import           Data.Semigroup.Traversable
import           GHC.Generics                   (M1(..))
import           Hedgehog hiding                (HTraversable(..))
import qualified Control.Applicative.Free       as Ap
import qualified Control.Applicative.Free.Fast  as FAF
import qualified Control.Applicative.Free.Final as FA
import qualified Data.List.NonEmpty             as NE
import qualified Data.Map.NonEmpty              as NEM
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
    tripping x (viewF   i) (Just . reviewF i)
    y <- forAll gy
    tripping y (reviewF i) (Just . viewF   i)

sumGen :: MonadGen m => m (f a) -> m (g a) -> m ((f :+: g) a)
sumGen gx gy = Gen.bool >>= \case
    False -> L1 <$> gx
    True  -> R1 <$> gy

intGen :: MonadGen m => m Int
intGen = Gen.integral (Range.linear 0 100)

listGen :: MonadGen m => m [Int]
listGen = Gen.list (Range.linear 0 100) intGen

instance (GShow f, GShow g) => Eq (Day f g a) where
    (==) = (==) `on` show

instance Show c => GShow (Const c) where
    gshowsPrec = showsPrec

instance (GShow f, GShow g) => GShow (Day f g) where
    gshowsPrec d (Day x y _) =
      showsBinaryWith gshowsPrec gshowsPrec "Day" d x y

instance (GShow f, GShow (t f (Chain1 t f))) => GShow (Chain1 t f) where
    gshowsPrec d = \case
        Done1 x  -> gshowsPrec d x
        More1 xs -> gshowsPrec d xs

instance GShow Identity where
    gshowsPrec _ _ = showString "<Identity>"

instance (GShow i, GShow (t f (Chain t i f))) => GShow (Chain t i f) where
    gshowsPrec d = \case
        Done x  -> gshowsPrec d x
        More xs -> gshowsPrec d xs

instance (GShow f, GShow g) => Show (Day f g a) where
    showsPrec = gshowsPrec

instance (GShow f, Functor f) => GShow (Ap1 f) where
    gshowsPrec d (Ap1 x y) = case matchLB @Day y of
      L1 _  -> showsUnaryWith gshowsPrec "inject" d x
      R1 ys -> showsBinaryWith gshowsPrec gshowsPrec "Ap1" d x ys

instance (GShow f, Functor f) => Eq (Ap1 f a) where
    (==) = (==) `on` show

instance (GShow f, Functor f) => Show (Ap1 f a) where
    showsPrec = gshowsPrec

instance GShow f => GShow (Ap f) where
    gshowsPrec d = \case
      Ap.Pure _  -> showString "<pure>"
      Ap.Ap x xs -> showsBinaryWith gshowsPrec gshowsPrec "Ap" d x xs

instance GShow f => GShow (FA.Ap f) where
    gshowsPrec d = gshowsPrec @(Ap f) d . FA.runAp Ap.liftAp

instance GShow f => GShow (FAF.Ap f) where
    gshowsPrec d = gshowsPrec @(Ap f) d . FAF.runAp Ap.liftAp

instance GShow f => Show (Ap f a) where
    showsPrec = gshowsPrec

instance GShow f => Show (FA.Ap f a) where
    showsPrec = gshowsPrec

instance GShow f => Show (FAF.Ap f a) where
    showsPrec = gshowsPrec

instance GShow f => Eq (Ap f a) where
    (==) = (==) `on` show

instance GShow f => Eq (FA.Ap f a) where
    (==) = (==) `on` show

instance GShow f => Eq (FAF.Ap f a) where
    (==) = (==) `on` show

deriving instance (Show e, Show (f a)) => Show (EnvT e f a)
deriving instance (Eq e, Eq (f a)) => Eq (EnvT e f a)

instance (Show e, Show1 f) => Show1 (EnvT e f) where
    liftShowsPrec sp sl d (EnvT e x) =
      showsBinaryWith showsPrec (liftShowsPrec sp sl) "EnvT" d e x

instance (Eq e, Eq1 f) => Eq1 (EnvT e f) where
    liftEq eq (EnvT e x) (EnvT d y) = e == d && liftEq eq x y

instance Show1 (s (t f)) => Show1 (ComposeT s t f) where
    liftShowsPrec sp sl d (ComposeT x) =
      showsUnaryWith (liftShowsPrec sp sl) "ComposeT" d x

instance Eq1 (s (t f)) => Eq1 (ComposeT s t f) where
    liftEq eq (ComposeT x) (ComposeT y) = liftEq eq x y

instance Enum Any where
    toEnum   = Any . toEnum
    fromEnum = fromEnum . getAny

instance Show1 V1 where
    liftShowsPrec _ _ _ = \case {}

instance Eq1 V1 where
    liftEq _ = \case {}

class HFunctor t => TestHFunctor t where
    type TestHFunctorBy t :: (Type -> Type) -> Constraint
    type TestHFunctorBy t = Unconstrained
    genHF
        :: (MonadGen m, TestHFunctorBy t f)
        => m (f a)
        -> m (t f a)

    default genHF :: (Inject t, MonadGen m) => m (f a) -> m (t f a)
    genHF = fmap inject

class HFunctor t => HTraversable t where
    htraverse :: Applicative h => (forall x. f x -> h (g x)) -> t f a -> h (t g a)

instance TestHFunctor Step where
    genHF gx = Step <$> Gen.integral (Range.linear 0 25) <*> gx

instance TestHFunctor ListF where
    genHF gx = ListF <$> Gen.list (Range.linear 0 25) gx

instance TestHFunctor NonEmptyF where
    genHF gx = NonEmptyF <$> Gen.nonEmpty (Range.linear 1 25) gx

instance (Enum k, Bounded k, Ord k) => TestHFunctor (MapF k) where
    genHF gx = MapF <$> Gen.map (Range.linear 0 10) kv
      where
        kv = (,) <$> Gen.enumBounded
                 <*> gx

instance (Enum k, Bounded k, Ord k) => TestHFunctor (NEMapF k) where
    genHF gx = do
      mp <- Gen.map (Range.linear 0 10) kv
      (k, v) <- kv
      pure . NEMapF $ NEM.insertMap k v mp
      where
        kv = (,) <$> Gen.enumBounded
                 <*> gx

instance TestHFunctor Steps where
    genHF gx = do
      mp     <- Gen.map (Range.linear 0 10) kv
      (k, v) <- kv
      pure . Steps $ NEM.insertMap k v mp
      where
        kv = (,) <$> Gen.integral (Range.linear 0 25)
                 <*> gx

instance TestHFunctor Ap where
    genHF gx = fmap NE.last
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 0 3) gx

instance TestHFunctor FA.Ap where
    genHF gx = fmap NE.last
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 0 3) gx

instance TestHFunctor FAF.Ap where
    genHF gx = fmap NE.last
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 0 3) gx

instance TestHFunctor Ap1 where
    genHF gx = fmap NE.last
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 1 3) gx

instance TestHFunctor Free where
    genHF gx = fmap NE.last
             . sequence
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 0 3) gx

instance TestHFunctor Free1 where
    genHF gx = fmap NE.last
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 1 3) gx

instance TestHFunctor t => TestHFunctor (HLift t) where
    type TestHFunctorBy (HLift t) = TestHFunctorBy t
    genHF gx = Gen.bool >>= \case
      False -> HPure  <$> gx
      True  -> HOther <$> genHF gx

instance (Enum e, Bounded e) => TestHFunctor (EnvT e) where
    genHF gx = EnvT <$> Gen.enumBounded <*> gx

class (c f, d f) => AndC c d f
instance (c f, d f) => AndC c d f

instance (TestHFunctor s, HTraversable s, TestHFunctor t) => TestHFunctor (ComposeT s t) where
    type TestHFunctorBy (ComposeT s t) = AndC (TestHFunctorBy s) (TestHFunctorBy t)
    genHF gx = fmap ComposeT
             . htraverse (genHF @t . pure)
           =<< genHF @s gx

instance TestHFunctor Flagged where
    genHF gx = Flagged <$> Gen.bool <*> gx

instance HTraversable Flagged where
    htraverse f (Flagged b x) = Flagged b <$> f x

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

instance TestHBifunctor Joker where
    genHB gx _ = Joker <$> gx

instance TestHBifunctor RightF where
    genHB _ gy = RightF <$> gy

instance TestHBifunctor t => TestHFunctor (Chain1 t) where
    genHF x = go
      where
        go = Gen.bool >>= \case
          False -> Done1 <$> x
          True  -> More1 <$> genHB x go

deriving instance Eq (f a) => Eq (WrappedApplicative f a)
deriving instance Show (f a) => Show (WrappedApplicative f a)

-- | We cannot test the pure case, huhu
instance TestHFunctor MaybeApply

deriving instance (Eq a, Eq (f a)) => Eq (MaybeApply f a)
deriving instance (Show a, Show (f a)) => Show (MaybeApply f a)

-- | We cannot test the pure case, huhu
instance TestHFunctor Lift

-- | We cannot test the pure case, huhu
instance TestHFunctor (These1 f)

instance TestHFunctor MaybeF where
    genHF gx = Gen.bool >>= \case
      False -> pure $ MaybeF Nothing
      True  -> MaybeF . Just <$> gx

instance TestHFunctor IdentityT where
instance TestHFunctor Coyoneda
instance TestHFunctor WrappedApplicative
instance TestHFunctor Reverse
instance TestHFunctor Backwards
instance Applicative f => TestHFunctor (Comp f :: (Type -> Type) -> Type -> Type)
instance TestHFunctor (M1 i c)
instance Plus f => TestHFunctor ((:*:) f)
instance Plus f => TestHFunctor (Product f)
instance TestHFunctor ((:+:) f)
instance TestHFunctor (Sum f)
instance TestHFunctor ProxyF
instance TestHFunctor (RightF f)
