{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE InstanceSigs         #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.HFoldable (
    HFoldable(..)
  , hfoldMap
  ) where

import           Control.Applicative
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Maybe
import           Control.Natural
import           Data.Coerce
import           Data.Functor.Apply.Free
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor
import           Data.HFunctor.Chain
import qualified Control.Applicative.Free     as FA

class HFoldable t where
    hfoldMap_ :: Monoid m => f ~> Const m -> t f ~> Const m

hfoldMap
    :: (HFoldable t, Monoid m)
    => (forall x. f x -> m)
    -> t f a
    -> m
hfoldMap f = getConst . hfoldMap_ (Const . f)

instance HFoldable IdentityT where
    hfoldMap_ f = f . runIdentityT

instance HFoldable FA.Ap where
    hfoldMap_ :: forall f m. Monoid m => f ~> Const m -> FA.Ap f ~> Const m
    hfoldMap_ f = go
      where
        go :: FA.Ap f ~> Const m
        go = \case
          FA.Pure _  -> Const mempty
          FA.Ap x xs -> f x <**> go xs

instance HFoldable Ap1 where
    hfoldMap_ f (Ap1 x xs) = f x <**> hfoldMap_ f xs

instance HFoldable ProxyF where
    hfoldMap_ _ _ = Const mempty

instance (Semigroupoidal t, HFoldable (SF t)) => HFoldable (Chain1 t) where
    hfoldMap_ f = hfoldMap_ f . rerollSF

instance (Monoidal t, HFoldable (MF t), i ~ I t) => HFoldable (Chain t i) where
    hfoldMap_ f = hfoldMap_ f . rerollMF

instance HFoldable MaybeT where
    hfoldMap_ f = coerce . f . runMaybeT
