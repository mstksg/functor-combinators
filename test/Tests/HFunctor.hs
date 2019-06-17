{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Tests.HFunctor (
    retractingProp
  , interpretProp, interpretProp_
  , hbindInjectProp, hbindInjectProp_
  , hbindhjoinProp, hbindhjoinProp_
  , hjoinAssocProp, hjoinAssocProp_
  ) where

import           Data.Functor.Combinator
import           Data.HFunctor
import           Hedgehog
import           Tests.Util
import qualified Hedgehog.Gen            as Gen
import qualified Hedgehog.Range          as Range

retractingProp
    :: forall t f m a.
     ( Interpret t
     , Monad m
     , C t f
     , Show (f a)
     , Show (t f a)
     , Eq (f a)
     )
    => Gen (f a)
    -> PropertyT m ()
retractingProp gx = do
    x <- forAll gx
    tripping x (inject @t) (Just . retract)

interpretProp
    :: forall t f m a.
     ( Interpret t
     , Monad m
     , C t f
     , Show (f a)
     , Show (t f a)
     , Eq (f a)
     )
    => Gen (t f a)
    -> PropertyT m ()
interpretProp gx = do
    x <- forAll gx
    retract x === interpret id x

hbindInjectProp
    :: forall t f m a.
     ( HBind t
     , Monad m
     , Show (t f a), Eq (t f a)
     )
    => Gen (t f a)
    -> PropertyT m ()
hbindInjectProp gx = do
    x <- forAll gx
    hbind inject x === x

hbindhjoinProp
    :: forall t f m a.
     ( HBind t
     , Monad m
     , Show (t (t f) a)
     , Show (t f a), Eq (t f a)
     )
    => Gen (t (t f) a)
    -> PropertyT m ()
hbindhjoinProp gx = do
    x <- forAll gx
    hbind id x === hjoin x

hjoinAssocProp
    :: forall t f m a.
     ( HBind t
     , Monad m
     , Show (t (t (t f)) a)
     , Show (t f a), Eq (t f a)
     )
    => Gen (t (t (t f)) a)
    -> PropertyT m ()
hjoinAssocProp gx = do
    x <- forAll gx
    hjoin (hjoin x) === hjoin (hmap hjoin x)

interpretProp_
    :: forall t f m a.
     ( Interpret t
     , TestHFunctor t
     , Monad m
     , C t f
     , Show (f a)
     , Show (t f a)
     , Eq (f a)
     )
    => Gen (f a)
    -> PropertyT m ()
interpretProp_ = interpretProp @t . genHF

hbindInjectProp_
    :: forall t f m a.
     ( HBind t
     , TestHFunctor t
     , Monad m
     , Show (t f a), Eq (t f a)
     )
    => Gen (f a)
    -> PropertyT m ()
hbindInjectProp_ = hbindInjectProp @t . genHF

hbindhjoinProp_
    :: forall t f m a.
     ( HBind t
     , TestHFunctor t
     , Monad m
     , Show (t f a), Eq (t f a)
     )
    => Gen (f a)
    -> PropertyT m ()
hbindhjoinProp_ = hbindInjectProp @t . genHF

hjoinAssocProp_
    :: forall t f m a.
     ( HBind t
     , TestHFunctor t
     , Monad m
     , Show (t (t (t f)) a)
     , Show (t f a), Eq (t f a)
     )
    => Gen (f a)
    -> PropertyT m ()
hjoinAssocProp_ = hjoinAssocProp @t . genHF . genHF . genHF
