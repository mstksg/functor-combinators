{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.HFunctor (
    TestHFunctor(..)
  ) where

import           Control.Monad.Freer.Church
import           Data.Functor.Combinator
import           Data.Semigroup.Traversable
import           Hedgehog hiding            (HTraversable(..))
import qualified Data.List.NonEmpty         as NE
import qualified Data.Map.NonEmpty          as NEM
import qualified Hedgehog.Gen               as Gen
import qualified Hedgehog.Range             as Range

class HFunctor t => TestHFunctor t where
    genHF
        :: MonadGen m
        => m (f a)
        -> m (t f a)

class HFunctor t => HTraversable t where
    htraverse :: Applicative h => (forall x. f x -> h (g x)) -> t f a -> h (t g a)


instance TestHFunctor Step where
    genHF gx = Step <$> Gen.integral (Range.linear 0 25) <*> gx

instance TestHFunctor ListF where
    genHF gx = ListF <$> Gen.list (Range.linear 0 100) gx

instance TestHFunctor NonEmptyF where
    genHF gx = NonEmptyF <$> Gen.nonEmpty (Range.linear 1 100) gx

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
    genHF gx = Gen.bool >>= \case
      False -> HPure  <$> gx
      True  -> HOther <$> genHF gx

instance (Enum e, Bounded e) => TestHFunctor (EnvT e) where
    genHF gx = EnvT <$> Gen.enumBounded <*> gx

instance (TestHFunctor s, HTraversable s, TestHFunctor t) => TestHFunctor (ComposeT s t) where
    genHF gx = fmap ComposeT
             . htraverse (genHF @t . pure)
           =<< genHF @s gx

instance TestHFunctor Flagged where
    genHF gx = Flagged <$> Gen.bool <*> gx

instance HTraversable Flagged where
    htraverse f (Flagged b x) = Flagged b <$> f x
