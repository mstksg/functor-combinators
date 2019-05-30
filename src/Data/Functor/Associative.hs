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
  ) where

-- import           Control.Applicative.Lift
-- import           Data.Coerce
-- import           Data.Constraint.Trivial
import           Control.Applicative
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Copointed
import           Data.Foldable
import           Data.Function
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
import           Data.Functor.Day               (Day(..))
import           Data.Functor.HFunctor
import           Data.Functor.HFunctor.Internal
import           Data.Functor.Identity
import           Data.Functor.Interpret
import           Data.Functor.Plus
import           Data.Kind
import           Data.List.NonEmpty             (NonEmpty(..))
import           Data.Proxy
import           GHC.Generics hiding            (C)
import           GHC.Natural
import qualified Data.Functor.Day               as D


class HBifunctor t => Associative t where
    assoc    :: (Functor f, Functor g, Functor h) => t f (t g h) ~> t (t f g) h
    disassoc :: (Functor f, Functor g, Functor h) => t (t f g) h ~> t f (t g h)

class (Associative t, Interpret (SF t)) => Semigroupoidal t where
    type SF t :: (Type -> Type) -> Type -> Type

    -- | Prepend an application of @t f@ to the front of a @'SF' t f@.
    --
    -- Together with 'nilSF', forms an inverse with 'unconsSF'.
    consSF   :: t f (SF t f) ~> SF t f
    -- consSF     = fromF . More . hright toF

    -- unconsSF :: SF t f ~> t f (SF t f)

    -- | If a @'SF' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'SF' t f@s applied to
    -- themselves into one giant @'SF' t f@ containing all of the @t f@s.
    appendSF :: t (SF t f) (SF t f) ~> SF t f
    -- appendSF = fromF . appendF . hbimap toF toF

    -- | A version of 'retract' that works for a 'Tensor'.  It retracts
    -- /both/ @f@s into a single @f@.
    retractS :: C (SF t) f => t f f ~> f
    retractS = retract . toSF

    -- | A version of 'interpret' that works for a 'Tensor'.  It takes two
    -- interpreting functions, and interprets both joined functors one
    -- after the other into @h@.
    interpretS :: C (SF t) h => (f ~> h) -> (g ~> h) -> t f g ~> h
    interpretS f g = retractS . hbimap f g

    -- | Embed a direct application of @f@ to itself into a @'SF' t f@.
    toSF     :: t f f ~> SF t f
    -- toSF     = fromF . More . hright (More . hright Done . intro1)


instance Associative (:*:) where
   assoc (x :*: (y :*: z)) = (x :*: y) :*: z
   disassoc ((x :*: y) :*: z) = x :*: (y :*: z)

instance Semigroupoidal (:*:) where
    type SF (:*:) = NonEmptyF

    consSF (x :*: NonEmptyF xs)    = NonEmptyF $ x :| toList xs
    appendSF (NonEmptyF xs :*: NonEmptyF ys) = NonEmptyF (xs <> ys)

    retractS (x :*: y) = x <!> y
    interpretS f g (x :*: y) = f x <!> g y
    toSF (x :*: y) = NonEmptyF $ x :| [y]

instance Associative Day where
    assoc    = D.assoc
    disassoc = D.disassoc

instance Semigroupoidal Day where
    type SF Day = Ap1

    consSF (Day x y z)   = Ap1 x $ flip z <$> toAp y
    appendSF (Day x y z) = z <$> x <.> y

    retractS (Day x y z) = z <$> x <.> y
    interpretS f g (Day x y z) = z <$> f x <.> g y
    toSF (Day x y z) = z <$> inject x <.> inject y

instance Associative (:+:) where
    assoc = \case
      L1 x      -> L1 (L1 x)
      R1 (L1 y) -> L1 (R1 y)
      R1 (R1 z) -> R1 z
    disassoc = \case
      L1 (L1 x) -> L1 x
      L1 (R1 y) -> R1 (L1 y)
      R1 z      -> R1 (R1 z)

instance Semigroupoidal (:+:) where
    type SF (:+:) = Step

    consSF = \case
      L1 x          -> Step 0       x
      R1 (Step n y) -> Step (n + 1) y
    appendSF = \case
      L1 x -> x
      R1 y -> y

    retractS = \case
      L1 x -> x
      R1 y -> y
    interpretS f g = \case
      L1 x -> f x
      R1 y -> g y
    toSF = \case
      L1 x -> Step 0 x
      R1 y -> Step 1 y

instance Associative Comp where
    assoc (x :>>= y) = (x :>>= (unComp . y)) :>>= id
    disassoc ((x :>>= y) :>>= z) = x :>>= ((:>>= z) . y)

instance Semigroupoidal Comp where
    type SF Comp = Free1

    consSF (x :>>= y) = Free1 x (toFree . y)
    appendSF (Free1 x g :>>= h) = Free1 x (toFree . h <=< g)

    retractS (x :>>= y) = x >>- y
    interpretS f g (x :>>= y) = f x >>- (g . y)
    toSF (x :>>= g) = Free1 x (inject . g)


