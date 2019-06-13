{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.HFunctor (
    TestHFunctor(..)
  ) where

import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Data.Functor.Combinator
import           Data.Semigroup.Traversable
import           Hedgehog
import qualified Data.List.NonEmpty          as NE
import qualified Data.Map.NonEmpty           as NEM
import qualified Hedgehog.Gen                as Gen
import qualified Hedgehog.Range              as Range

class HFunctor t => TestHFunctor t where
    genHF
        :: MonadGen m
        => m (f a)
        -> m (t f a)

instance TestHFunctor Step where
    genHF gx = Step <$> Gen.integral (Range.linear 0 25) <*> gx

instance TestHFunctor Step2 where
    genHF gx = Step2 <$> Gen.integral (Range.linear 0 25)
                     <*> Gen.integral (Range.linear 0 25)
                     <*> gx

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
    genHF gx = fmap NE.head
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 0 3) gx

instance TestHFunctor Ap1 where
    genHF gx = fmap NE.head
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 1 3) gx

instance TestHFunctor Free where
    genHF gx = fmap NE.head
             . sequence
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 0 3) gx

instance TestHFunctor Free1 where
    genHF gx = fmap NE.head
             . sequence1
             . fmap inject
           <$> Gen.nonEmpty (Range.linear 1 3) gx

instance TestHFunctor t => TestHFunctor (HLift t) where
    genHF gx = Gen.bool >>= \case
      False -> HPure  <$> gx
      True  -> HOther <$> genHF gx

instance (Enum e, Bounded e) => TestHFunctor (EnvT e) where
    genHF gx = EnvT <$> Gen.enumBounded <*> gx

-- | doesn't really do anything with t
instance (TestHFunctor s, Inject t) => TestHFunctor (ComposeT s t) where
    genHF gx = ComposeT . hmap inject <$> genHF @s gx
      -- ss <- genHF @s gx
      -- ts <- genHF @t gx
      -- pure $ ComposeT $ _ ss
        -- ComposeT . hmap inject <$> genHF @s gx
    -- Gen.bool >>= \case
    --   False -> HPure  <$> gx
    --   True  -> HOther <$> genHF gx
