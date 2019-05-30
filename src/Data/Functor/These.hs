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
import           Data.Data
import           Data.Deriving
import           Data.Functor.HFunctor.Internal
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

instance Tensor These1 where
    type I These1 = Void1

    intro1 = This1
    intro2 = That1
    elim1  = \case
      This1  x   -> x
      That1    y -> absurd1 y
      These1 _ y -> absurd1 y
    elim2  = \case
      This1  x   -> absurd1 x
      That1    y -> y
      These1 x _ -> absurd1 x
    assoc = \case
      This1  x              -> This1  (This1  x  )
      That1    (This1  y  ) -> This1  (That1    y)
      That1    (That1    z) -> That1               z
      That1    (These1 y z) -> These1 (That1    y) z
      These1 x (This1  y  ) -> This1  (These1 x y)
      These1 x (That1    z) -> These1 (This1  x  ) z
      These1 x (These1 y z) -> These1 (These1 x y) z
    disassoc = \case
      This1  (This1  x  )   -> This1  x
      This1  (That1    y)   -> That1    (This1  y  )
      This1  (These1 x y)   -> These1 x (This1  y  )
      That1               z -> That1    (That1    z)
      These1 (This1  x  ) z -> These1 x (That1    z)
      These1 (That1    y) z -> That1    (These1 y z)
      These1 (These1 x y) z -> These1 x (These1 y z)

instance Monoidal These1 where
    type TM These1 = Steps

    nilTM  = absurd1
    consTM = \case
      This1  x            -> Steps $ NEM.singleton 0 x
      That1    (Steps xs) -> Steps $ NEM.mapKeysMonotonic (+ 1) xs
      These1 x (Steps xs) -> Steps . NEM.insertMapMin 0 x
                                   . NEM.toMap
                                   . NEM.mapKeysMonotonic (+ 1)
                                   $ xs
    unconsTM = R1
             . hbimap (getFirst . unComp1) (Steps . unComp1)
             . decrAll
             . getSteps
    appendTM = \case
      This1  (Steps xs)            -> Steps xs
      That1             (Steps ys) -> Steps ys
      These1 (Steps xs) (Steps ys) -> Steps $
        let (k, _) = NEM.findMax xs
        in  xs <> NEM.mapKeysMonotonic (+ (k + 1)) ys

    fromF = \case
      Done x            -> absurd1 x
      More (This1  x  ) -> Steps . NEM.singleton 0 $ x
      More (That1    y) ->
        let Steps ys = fromF y
        in  Steps $ NEM.mapKeysMonotonic (+ 1) ys
      More (These1 x y) ->
        let Steps ys = fromF y
        in  Steps
              . NEM.insertMapMin 0 x
              . NEM.toMap
              . NEM.mapKeysMonotonic (+ 1)
              $ ys
    toF = More
        . hbimap (getFirst . unComp1) (toF . Steps . unComp1)
        . decrAll
        . getSteps
    appendF = \case
      This1  xs    -> xs
      That1     ys -> ys
      These1 xs ys -> case xs of
        Done x              -> absurd1 x
        More (This1  x    ) -> More $ These1 x ys
        More (That1    xs') -> More $ That1    (appendF (These1 xs' ys))
        More (These1 x xs') -> More $ These1 x (appendF (These1 xs' ys))

    retractT = \case
      This1  x   -> x
      That1    y -> y
      These1 x y -> x <!> y
    interpretT f g = \case
      This1  x   -> f x
      That1    y -> g y
      These1 x y -> f x <!> g y
    toTM = \case
      This1  x   -> Steps $ NEM.singleton 0 x
      That1    y -> Steps $ NEM.singleton 1 y
      These1 x y -> Steps $ NEM.fromDistinctAscList ((0, x) :| [(1, y)])
    pureT = absurd1

decrAll :: NEMap Natural (f x) -> These1 (First :.: f) (NEMap Natural :.: f) x
decrAll = NEM.foldMapWithKey $ \i x ->
    case minusNaturalMaybe i 1 of
      Nothing -> This1 . Comp1 $ First x
      Just i' -> That1 . Comp1 $ NEM.singleton i' x
