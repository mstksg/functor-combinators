{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeApplications       #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}

module Data.Functor.Combinator (
    type (~>)
  , HFunctor(..)
  , Interpret(..)
  , HBifunctor(..)
  , HIso
  , Tensor(..)
  , Free(..)
  , Monoidal(..)
  , retractT, toFree
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Monad
import           Control.Monad.Codensity
import           Data.Functor.Coyoneda
import           Data.Functor.Identity
import           Data.Kind
import           Data.Profunctor
import           Data.Proxy
import           Data.Void
import           GHC.Generics hiding       (C)
import qualified Control.Monad.Free.Church as M
import qualified Data.Functor.Day          as D

type f ~> g = forall x. f x -> g x

infixr 0 ~>

class HFunctor t where
    map1 :: f ~> g -> t f ~> t g

class HFunctor t => Interpret t where
    type C t :: (Type -> Type) -> Constraint
    inject  :: f ~> t f
    retract :: C t f => t f ~> f

class HBifunctor t where
    type I t :: Type -> Type

    hleft  :: f ~> j -> t f g ~> t j g
    hright :: g ~> k -> t f g ~> t f k

    hbimap :: f ~> j -> g ~> k -> t f g ~> t j k

type HIso f g = forall p x. Profunctor p => p (f x) (f x) -> p (g x) (g x)

class (HBifunctor t, Functor (I t)) => Tensor t where
    intro1 :: f ~> t f (I t)
    intro2 :: g ~> t (I t) g

    elim1  :: t f (I t) ~> f
    elim2  :: t (I t) g ~> g

    assoc    :: t f (t g h) ~> t (t f g) h
    disassoc :: t (t f g) h ~> t f (t g h)

data Free t i f a = Done (i a)
                  | More (t f (Free t i f) a)

class Tensor t => Monoidal t where
    type FM t :: (Type -> Type) -> Type -> Type
    toFM     :: t f f ~> FM t f
    fromFree :: Free t (I t) f ~> FM t f

retractT
    :: ( Monoidal t
       , Interpret (FM t)
       , C (FM t) f
       )
    => t f f
    ~> f
retractT = retract . toFM

toFree
    :: ( Monoidal t
       , Interpret (FM t)
       , C (FM t) (Free t (I t) f)
       )
    => FM t f
    ~> Free t (I t) f
toFree = retract . map1 (More . hright Done . intro1)

instance HFunctor Coyoneda where
    map1 = hoistCoyoneda

instance Interpret Coyoneda where
    type C Coyoneda = Functor
    inject  = liftCoyoneda
    retract = lowerCoyoneda

instance HFunctor Ap where
    map1 = hoistAp

instance Interpret Ap where
    type C Ap = Applicative
    inject  = liftAp
    retract = runAp id

instance HFunctor M.F where
    map1 = M.hoistF

data Freer :: (Type -> Type) -> Type -> Type where
    Purer   :: a -> Freer f a
    Bindier :: f x -> (x -> Freer f a) -> Freer f a

instance Functor (Freer f) where
    fmap f = \case
      Purer x     -> Purer (f x)
      Bindier x y -> Bindier x (fmap f . y)

instance Applicative (Freer f) where
    pure  = Purer
    (<*>) = ap

instance Monad (Freer f) where
    return = pure
    (>>=) = \case
      Purer x     -> ($ x)
      Bindier x y -> \f -> Bindier x ((f =<<) . y)

instance M.MonadFree f (Freer f) where
    wrap = (`Bindier` id)

instance HFunctor Freer where
    map1 f = \case
      Purer x     -> Purer x
      Bindier x y -> Bindier (f x) (map1 f . y)

instance Interpret Freer where
    type C Freer = Monad
    inject x = Bindier x Purer
    retract  = \case
      Purer x     -> pure x
      Bindier x y -> retract . y =<< x
