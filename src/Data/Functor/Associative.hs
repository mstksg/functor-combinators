{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE EmptyDataDeriving          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}


module Data.Functor.Associative (
    Associative(..)
  , assoc
  , disassoc
  , Semigroupoidal(..)
  , F1(..)
  , unrolledSF
  , rerollSF
  , concatF1
  -- , toF1, fromF1, asF1
  ) where

import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Foldable
import           Data.Functor
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
import           Data.Functor.Day               (Day(..))
import           Data.Functor.HFunctor.Internal
import           Data.Functor.HFunctor.IsoF
import           Data.Functor.Identity
import           Data.Functor.Interpret
import           Data.Functor.Plus
import           Data.Kind
import           Data.List.NonEmpty             (NonEmpty(..))
import           Data.Profunctor
import           Data.Proxy
import           Data.Tagged
import           GHC.Generics hiding            (C)
import qualified Data.Functor.Day               as D

class HBifunctor t => Associative t where
    associative
        :: (Functor f, Functor g, Functor h)
        => t f (t g h) <~> t (t f g) h
    {-# MINIMAL associative #-}

assoc
    :: (Associative t, Functor f, Functor g, Functor h)
    => t f (t g h)
    ~> t (t f g) h
assoc = viewF associative

disassoc
    :: (Associative t, Functor f, Functor g, Functor h)
    => t (t f g) h
    ~> t f (t g h)
disassoc = reviewF associative

data F1 t f a = Done1 (f a)
              | More1 (t f (F1 t f) a)

deriving instance (Show (t f (F1 t f) a), Show (f a)) => Show (F1 t f a)


class (Associative t, Interpret (SF t)) => Semigroupoidal t where
    type SF t :: (Type -> Type) -> Type -> Type

    -- | If a @'SF' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'SF' t f@s applied to
    -- themselves into one giant @'SF' t f@ containing all of the @t f@s.
    appendSF :: t (SF t f) (SF t f) ~> SF t f
    unrollSF :: Functor f => SF t f ~> F1 t f

    -- | Prepend an application of @t f@ to the front of a @'SF' t f@.
    consSF :: t f (SF t f) ~> SF t f
    consSF = appendSF . hleft inject

    -- | Embed a direct application of @f@ to itself into a @'SF' t f@.
    toSF :: t f f ~> SF t f
    toSF = appendSF . hbimap inject inject

    -- | A version of 'retract' that works for a 'Tensor'.  It retracts
    -- /both/ @f@s into a single @f@.
    retractS :: C (SF t) f => t f f ~> f
    retractS = retract . toSF

    -- | A version of 'interpret' that works for a 'Tensor'.  It takes two
    -- interpreting functions, and interprets both joined functors one
    -- after the other into @h@.
    interpretS :: C (SF t) h => (f ~> h) -> (g ~> h) -> t f g ~> h
    interpretS f g = retract . toSF . hbimap f g

    {-# MINIMAL unrollSF, appendSF #-}

unrolledSF :: forall t f. (Semigroupoidal t, Functor f) => SF t f <~> F1 t f
unrolledSF = isoF unrollSF rerollSF

rerollSF :: Semigroupoidal t => F1 t f ~> SF t f
rerollSF = \case
    Done1 x  -> inject x
    More1 xs -> consSF . hright rerollSF $ xs

concatF1 :: (Semigroupoidal t, Functor f) => F1 t (SF t f) ~> F1 t f
concatF1 = \case
    Done1 x  -> unrollSF x
    More1 xs -> unrollSF . appendSF . hright (rerollSF . concatF1) $ xs

instance Associative (:*:) where
    associative = isoF to_ from_
      where
        to_   (x :*: (y :*: z)) = (x :*: y) :*: z
        from_ ((x :*: y) :*: z) = x :*: (y :*: z)

instance Semigroupoidal (:*:) where
    type SF (:*:) = NonEmptyF

    unrollSF = shuffle
             . hright (hright unrollSF . fromListF)
             . nonEmptyProd
      where
        shuffle (x :*: L1 ~Proxy) = Done1 x
        shuffle (x :*: R1 xs    ) = More1 (x :*: xs)
    appendSF (NonEmptyF xs :*: NonEmptyF ys) = NonEmptyF (xs <> ys)

    consSF (x :*: NonEmptyF xs) = NonEmptyF $ x :| toList xs
    toSF   (x :*: y           ) = NonEmptyF $ x :| [y]

    retractS (x :*: y) = x <!> y
    interpretS f g (x :*: y) = f x <!> g y

instance Associative Day where
    associative = isoF D.assoc D.disassoc

instance Semigroupoidal Day where
    type SF Day = Ap1

    unrollSF = shuffle
             . hright (hright unrollSF . fromAp)
             . ap1Day
      where
        shuffle (Day x (L1 (Identity y)) z) = Done1 ((`z` y) <$> x)
        shuffle (Day x (R1 xs         )  z) = More1 (Day x xs z)
    appendSF (Day x y z) = z <$> x <.> y

    consSF (Day x y z) = Ap1 x $ flip z <$> toAp y
    toSF   (Day x y z) = z <$> inject x <.> inject y

    retractS (Day x y z) = z <$> x <.> y
    interpretS f g (Day x y z) = z <$> f x <.> g y

instance Associative (:+:) where
    associative = isoF to_ from_
      where
        to_ = \case
          L1 x      -> L1 (L1 x)
          R1 (L1 y) -> L1 (R1 y)
          R1 (R1 z) -> R1 z
        from_ = \case
          L1 (L1 x) -> L1 x
          L1 (R1 y) -> R1 (L1 y)
          R1 z      -> R1 (R1 z)

instance Semigroupoidal (:+:) where
    type SF (:+:) = Step

    appendSF = \case
      L1 x          -> x
      R1 (Step n y) -> Step (n + 1) y
    unrollSF = More1                -- make sure this aligns with unrollMF
             . hright unrollSF
             . stepDown

    -- consSF = \case
    --   L1 x          -> Step 0       x
    --   R1 (Step n y) -> Step (n + 1) y
    -- toSF = \case
    --   L1 x -> Step 0 x
    --   R1 y -> Step 1 y

    retractS = \case
      L1 x -> x
      R1 y -> y
    interpretS f g = \case
      L1 x -> f x
      R1 y -> g y

instance Associative Comp where
    associative = isoF to_ from_
      where
        to_   (x :>>= y) = (x :>>= (unComp . y)) :>>= id
        from_ ((x :>>= y) :>>= z) = x :>>= ((:>>= z) . y)

instance Semigroupoidal Comp where
    type SF Comp = Free1

    unrollSF x = runFree1 x (\y n -> Done1 (y  <&> n))
                            (\y n -> More1 (y :>>= n))
    appendSF (x :>>= y) = x >>- y

    consSF (x :>>= y) = liftFree1 x >>- y
    toSF   (x :>>= g) = liftFree1 x >>- inject . g

    retractS       (x :>>= y) = x >>- y
    interpretS f g (x :>>= y) = f x >>- (g . y)
