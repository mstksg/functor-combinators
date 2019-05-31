{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DeriveGeneric      #-}
{-# LANGUAGE DeriveTraversable  #-}
{-# LANGUAGE LambdaCase         #-}
{-# LANGUAGE TemplateHaskell    #-}
{-# LANGUAGE TypeFamilies       #-}
{-# LANGUAGE TypeOperators      #-}

module Data.Functor.These (
    These1(..)
  ) where

import           Control.Applicative.Step
import           Control.Natural
import           Data.Data
import           Data.Deriving
import           Data.Functor.Associative
import           Data.Functor.HFunctor.Internal
import           Data.Functor.HFunctor.IsoF
import           Data.Functor.Plus
import           Data.Functor.Tensor
import           Data.List.NonEmpty             (NonEmpty(..))
import           Data.Map.NonEmpty              (NEMap)
import           Data.Semigroup
import           GHC.Generics hiding            (C)
import           GHC.Natural
import qualified Data.Map.NonEmpty              as NEM

-- | A @These f g a@ has either an @f a@, a @g a@, or both.
--
-- This is re-defined here from the /these/ package, to avoid the high
-- dependency footprint.
data These1 f g a
    = This1 (f a)
    | That1 (g a)
    | These1 (f a) (g a)
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''These1
deriveRead1 ''These1
deriveEq1 ''These1
deriveOrd1 ''These1

instance (Semigroup (f a), Semigroup (g a)) => Semigroup (These1 f g a) where
    (<>) = \case
      This1  x   -> \case
        This1  x'    -> This1  (x <> x')
        That1     y' -> These1 x         y'
        These1 x' y' -> These1 (x <> x') y'
      That1    y -> \case
        This1  x'    -> These1 x'        y
        That1     y' -> That1            (y <> y')
        These1 x' y' -> These1 x'        (y <> y')
      These1 x y -> \case
        This1  x'    -> These1 (x <> x') y
        That1     y' -> These1 x         (y <> y')
        These1 x' y' -> These1 (x <> x') (y <> y')

instance HBifunctor These1 where
    hbimap f g = \case
      This1  x   -> This1  (f x)
      That1    y -> That1        (g y)
      These1 x y -> These1 (f x) (g y)


instance Associative These1 where
    associative = isoF to_ from_
      where
        to_ = \case
          This1  x              -> This1  (This1  x  )
          That1    (This1  y  ) -> This1  (That1    y)
          That1    (That1    z) -> That1               z
          That1    (These1 y z) -> These1 (That1    y) z
          These1 x (This1  y  ) -> This1  (These1 x y)
          These1 x (That1    z) -> These1 (This1  x  ) z
          These1 x (These1 y z) -> These1 (These1 x y) z
        from_ = \case
          This1  (This1  x  )   -> This1  x
          This1  (That1    y)   -> That1    (This1  y  )
          This1  (These1 x y)   -> These1 x (This1  y  )
          That1               z -> That1    (That1    z)
          These1 (This1  x  ) z -> These1 x (That1    z)
          These1 (That1    y) z -> That1    (These1 y z)
          These1 (These1 x y) z -> These1 x (These1 y z)

instance Tensor These1 where
    type I These1 = Void1

    intro1 = This1
    intro2 = That1
    elim1  = \case
      This1  x   -> x
      That1    y -> absurd1 y
      These1 _ y -> absurd1 y
    elim2 = \case
      This1  x   -> absurd1 x
      That1    y -> y
      These1 x _ -> absurd1 x

instance Semigroupoidal These1 where
    type SF These1 = Steps

    appendSF = \case
      This1  (Steps xs)            -> Steps xs
      That1             (Steps ys) -> Steps (NEM.mapKeysMonotonic (+ 1) ys)
      These1 (Steps xs) (Steps ys) -> Steps $
        let (k, _) = NEM.findMax xs
        in  xs <> NEM.mapKeysMonotonic (+ (k + 1)) ys

    consSF = stepsUp
    toSF = \case
      This1  x   -> Steps $ NEM.singleton 0 x
      That1    y -> Steps $ NEM.singleton 1 y
      These1 x y -> Steps $ NEM.fromDistinctAscList ((0, x) :| [(1, y)])

    retractS = \case
      This1  x   -> x
      That1    y -> y
      These1 x y -> x <!> y
    interpretS f g = \case
      This1  x   -> f x
      That1    y -> g y
      These1 x y -> f x <!> g y

instance Monoidal These1 where
    type MF These1 = Steps

    splitSF = isoF stepsDown stepsUp
    splitMF = isoF R1 $ \case
      L1 v -> absurd1 v
      R1 x -> x
    appendMF = appendSF

    nilMF      = absurd1
    consMF     = consSF
    unconsMF   = R1 . stepsDown
    toMF       = toSF

    retractT   = retractS
    interpretT = interpretS
    pureT      = absurd1

decr :: Natural -> g a -> These1 (First :.: g) (NEMap Natural :.: g) a
decr i x = case minusNaturalMaybe i 1 of
      Nothing -> This1 . Comp1 $ First x
      Just i' -> That1 . Comp1 $ NEM.singleton i' x

stepsDown :: Steps f ~> These1 f (Steps f)
stepsDown = hbimap (getFirst . unComp1) (Steps . unComp1)
          . NEM.foldMapWithKey decr
          . getSteps

stepsUp :: These1 f (Steps f) ~> Steps f
stepsUp = \case
    This1  x    -> Steps $ NEM.singleton 0 x
    That1    xs -> Steps . NEM.mapKeysMonotonic (+ 1)
                         . getSteps
                         $ xs
    These1 x xs -> Steps . NEM.insertMapMin 0 x
                         . NEM.toMap
                         . NEM.mapKeysMonotonic (+ 1)
                         . getSteps
                         $ xs
