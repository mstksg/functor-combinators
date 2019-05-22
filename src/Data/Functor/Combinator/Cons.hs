{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE TypeSynonymInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Data.Functor.Combinator.Cons (
    Cons(Comp, DayCons, ProdCons)
  -- * Instances
  -- ** Monadic
  , Comp, unComp, comp
  -- ** Applicative
  , DayCons, unDayCons
  -- ** Product
  , ProdK(..), ProdCons, unProdCons, prodCons
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Data.Coerce
import           Data.Function
import           Data.Functor.Combinator.Class
import           Data.Functor.Coyoneda
import           Data.Functor.Day              (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Kind
import           Data.Profunctor
import           Data.Proxy
import           Data.Semigroupoid.Static
import           GHC.Generics hiding           (C)
import qualified Data.Bifunctor.Product        as BP

-- | A lot of tensors can be factored out into a 'Cons' on some
-- parameterized profunctor.  For example, we have:
--
-- @
-- ':.:' = 'Cons' 'Star'
-- 'Day' = 'Cons' 'Static'
-- ':*:' = 'Cons' 'ProdK'
-- @
--
-- In the case of ':.:', this actually allows us to have 'HFunctor' and
-- 'Interpret' instances for functor composition, because the
-- representation of ':.:' normally does not allow this.  This gives us
-- a proper tensor to form 'Control.Monad.Free.Free', which makes the free
-- monad work nicely within our system.
--
-- In the normal case, you can just use 'Day' and ':*:' instead of
-- @'DayCons' = 'Cons' 'Static'@ and @'ProdCons' = 'Cons' 'ProdK'@.  The
-- only one that gives us extra power is @'Comp' = 'Cons' 'Star'@.
--
-- You can use 'DayCons' and 'ProdCons' as 'Day' and ':*:' using the
-- provided pattern synonyms.
data Cons
        :: ((Type -> Type) -> Type -> Type -> Type)
        -> (Type -> Type)
        -> (Type -> Type)
        -> Type
        -> Type where
    (:=>) :: f x -> p g x a -> Cons p f g a

instance (forall x. Functor (p g x)) => Functor (Cons p f g) where
    fmap f (x :=> y) = x :=> fmap f y

-- | A version of ':.:' that permits 'HBifunctor', 'Tensor', and 'Monoidal'
-- instances.
type Comp = Cons Star

instance HBifunctor Comp where
    hleft  f (x :=> y) = f x :=> y
    hright g (x :=> Star y) = x :=> Star (g . y)

    hbimap f g (x :=> Star y) = f x :=> Star (g . y)

deriving via (WrappedHBifunctor Comp f) instance HFunctor (Comp f)

comp :: f (g a) -> Comp f g a
comp = (:=> Star id)

pattern Comp :: Functor f => f (g a) -> Comp f g a
pattern Comp { unComp } <- ((\case x :=> Star f -> f <$> x)->unComp)
  where
    Comp x = comp x
{-# COMPLETE Comp #-}

instance Tensor Comp where
    type I Comp = Identity

    intro1 = (:=> Star Identity)
    intro2 = (Identity () :=>) . Star . const

    elim1 (x :=> Star y) = runIdentity . y <$> x
    elim2 (x :=> Star y) = y (runIdentity x)

    assoc (x :=> Star y) = (x :=> Star (unComp . y)) :=> Star id
    disassoc ((x :=> Star y) :=> z) = x :=> Star ((:=> z) . y)

instance Monoidal Comp where
    type TM Comp = Free

    nilTM  = pure . runIdentity
    consTM (x :=> Star y) = Free $ \p b -> b x $ \z -> runFree (y z) p b

    fromF = \case
      Done x -> pure . runIdentity $ x
      More (x :=> Star y) -> Free $ \p b -> b x $ \z -> runFree (fromF (y z)) p b
    toF x = runFree x (Done . Identity) $ \y z -> More (y :=> Star z)
    appendF (x :=> Star y) = case x of
      Done (Identity z)   -> y z
      More (z :=> Star q) -> More $ z :=> Star (appendF . comp . fmap y . q)

    retractT (x :=> Star y) = x >>= y
    injectT = pure . runIdentity
    toTM (x :=> Star y) = Free $ \p b -> b x (($ p) . b . y)

type DayCons = Cons Static

unDayCons :: DayCons b c ~> Day b c
unDayCons (x :=> Static y) = Day x y (&)

pattern DayCons :: Functor g => Day f g a -> DayCons f g a
pattern DayCons udc <- (unDayCons -> udc)
  where
    DayCons (Day x y f) = x :=> Static (flip f <$> y)
{-# COMPLETE DayCons #-}

instance HBifunctor DayCons where
    hleft  f (x :=> y) = f x :=> y
    hright g (x :=> Static y) = x :=> Static (g y)

    hbimap f g (x :=> Static y) = f x :=> Static (g y)

deriving via (WrappedHBifunctor DayCons f) instance HFunctor (DayCons f)

instance Tensor DayCons where
    type I DayCons = Identity

    intro1 = (:=> Static (Identity id))
    intro2 x = Identity () :=> Static (const <$> x)

    elim1 (x :=> Static (Identity y)) = y <$> x
    elim2 (Identity x :=> Static y) = ($ x) <$> y

    assoc (x :=> Static (y :=> Static z)) = (x :=> Static ((,) <$> y)) :=> Static (uncurry <$> z)
    disassoc ((x :=> Static y) :=> Static z) = x :=> Static ((($) <$> y) :=> Static ((.) <$> z))

instance Monoidal DayCons where
    type TM DayCons = Ap

    nilTM  = pure . runIdentity
    consTM (x :=> y) = (&) <$> liftAp x <*> runStatic y
    unconsTM = \case
      Pure x -> L1 $ Identity x
      Ap x y -> R1 $ x :=> Static y
    appendTM (x :=> Static y) = case x of
      Pure z -> ($ z) <$> y
      Ap z q -> (\a f g -> g (f a)) <$> liftAp z <*> q <*> y

    retractT (x :=> Static y) = x <**> y
    injectT = pure . runIdentity
    toTM (x :=> Static y) = Ap x (liftAp y)

data ProdK g a b = ProdK (a -> b) (g b)

type ProdCons = Cons ProdK

prodCons :: (f :*: g) ~> ProdCons f g
prodCons (x :*: y) = x :=> ProdK id y

pattern ProdCons :: Functor f => (f :*: g) a -> ProdCons f g a
pattern ProdCons { unProdCons } <- ((\case x :=> ProdK f y -> fmap f x :*: y) -> unProdCons)
  where
    ProdCons xy = prodCons xy
{-# COMPLETE ProdCons #-}

instance HBifunctor ProdCons where
    hleft  f (x :=> ProdK h y)   = f x :=> ProdK h y
    hright g (x :=> ProdK h y)   =   x :=> ProdK h (g y)
    hbimap f g (x :=> ProdK h y) = f x :=> ProdK h (g y)

deriving via (WrappedHBifunctor ProdCons f) instance HFunctor (ProdCons f)

instance Tensor ProdCons where
    type I ProdCons = Proxy

    intro1 = (:=> ProdK id Proxy)
    intro2 = (Proxy :=>) . ProdK id

    elim1 (x :=> ProdK f ~Proxy) = f <$> x
    elim2 (~Proxy :=> ProdK _ y) = y

    assoc (x :=> ProdK f (y :=> ProdK g z)) = (x :=> ProdK f (g <$> y)) :=> ProdK id z
    disassoc ((x :=> ProdK f y) :=> ProdK g z) = x :=> ProdK (g . f) (y :=> ProdK g z)

newtype ListFCo f a = ListFCo { unListFCo :: ListF (Coyoneda f) a }
    deriving (Functor, Applicative, Plus)

instance Alt (ListFCo f) where
    (<!>) :: forall a. ListFCo f a -> ListFCo f a -> ListFCo f a
    xs <!> ys = coerce (coerce xs <!> coerce ys :: ListF (Coyoneda f) a)

instance HFunctor ListFCo where
    hmap f = ListFCo . hmap (hoistCoyoneda f) . unListFCo

instance Interpret ListFCo where
    type C ListFCo = Plus

    inject  = ListFCo . inject . inject
    retract = retract . retract . unListFCo

instance Monoidal ProdCons where
    type TM ProdCons = ListFCo

    nilTM ~Proxy = zero
    consTM (x :=> ProdK f y) = ListFCo . ListF $
        Coyoneda f x : runListF (unListFCo y)
    unconsTM (ListFCo (ListF xs)) = case xs of
      []                -> L1 Proxy
      Coyoneda f y : ys -> R1 $ y :=> ProdK f (ListFCo (ListF ys))
    appendTM (ListFCo (ListF xs) :=> ProdK f (ListFCo (ListF ys))) =
      ListFCo . ListF $ (map . fmap) f xs ++ ys

    toTM (x :=> ProdK f y) = ListFCo . ListF $ [Coyoneda f x, inject y]
