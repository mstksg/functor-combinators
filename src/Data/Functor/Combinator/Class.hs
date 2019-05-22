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
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Data.Functor.Combinator.Class (
    type (~>)
  , HFunctor(..)
  , Interpret(..)
  , HBifunctor(..)
  , Tensor(..)
  , F(..)
  , Monoidal(..)
  , injectF, retractF, interpretF
  , WrappedHBifunctor(..)
  , Cons(..)
  -- * Instances
  , Comp, pattern Comp, unComp, comp
  , DayCons, pattern DayCons, unDayCons
  , Free(..)
  , Step(..)
  , VoidT
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Monad.Reader
import           Control.Monad.Writer      (MonadWriter(..))
import           Data.Function
import           Data.Functor.Coyoneda
import           Data.Functor.Day          (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Kind
import           Data.Profunctor
import           Data.Proxy
import           Data.Semigroup
import           Data.Semigroupoid.Static
import           GHC.Generics hiding       (C)
import           GHC.Natural
import qualified Control.Alternative.Free  as Alt
import qualified Control.Monad.Free        as M
import qualified Control.Monad.Free.Church as MC
import qualified Data.Functor.Day          as D

type f ~> g = forall x. f x -> g x

infixr 0 ~>

class HFunctor t where
    hmap :: f ~> g -> t f ~> t g

    {-# MINIMAL hmap #-}

-- | Laws:
--
-- @
-- retract . inject == id
-- @
class HFunctor t => Interpret t where
    type C t :: (Type -> Type) -> Constraint
    inject  :: f ~> t f

    retract :: C t f => t f ~> f
    retract = interpret id

    interpret :: C t g => (f ~> g) -> t f ~> g
    interpret f = retract . hmap f

    {-# MINIMAL inject, (retract | interpret) #-}

class HBifunctor t where
    hleft  :: f ~> j -> t f g ~> t j g
    hleft = (`hbimap` id)
    hright :: g ~> k -> t f g ~> t f k
    hright = hbimap id

    hbimap :: f ~> j -> g ~> k -> t f g ~> t j k
    hbimap f g = hleft f . hright g

    {-# MINIMAL hleft, hright | hbimap #-}

class HBifunctor t => Tensor t where
    type I t :: Type -> Type

    intro1 :: f ~> t f (I t)
    intro2 :: Functor g => g ~> t (I t) g

    elim1  :: Functor f => t f (I t) ~> f
    elim2  :: Functor g => t (I t) g ~> g

    assoc    :: (Functor f, Functor g, Functor h) => t f (t g h) ~> t (t f g) h
    disassoc :: (Functor f, Functor g, Functor h) => t (t f g) h ~> t f (t g h)

    {-# MINIMAL intro1, intro2, elim1, elim2, assoc, disassoc #-}

data F t i f a = Done (i a)
               | More (t f (F t i f) a)

instance (Functor i, forall g. Functor g => Functor (t f g)) => Functor (F t i f) where
    fmap f = \case
      Done x  -> Done (fmap f x)
      More xs -> More (fmap f xs)

class (Tensor t, Interpret (TM t)) => Monoidal t where
    type TM t :: (Type -> Type) -> Type -> Type

    nilTM    :: I t ~> TM t f
    nilTM    = fromF @t . Done
    consTM   :: t f (TM t f) ~> TM t f
    consTM     = fromF . More . hright toF
    unconsTM   :: TM t f ~> (I t :+: t f (TM t f))
    unconsTM m = case toF @t m of
      Done x  -> L1 x
      More xs -> R1 . hright fromF $ xs
    appendTM :: t (TM t f) (TM t f) ~> TM t f
    appendTM = fromF . appendF . hbimap toF toF

    fromF :: F t (I t) f ~> TM t f
    fromF = \case
      Done x  -> nilTM @t x
      More xs -> consTM . hright fromF $ xs
    toF   :: TM t f ~> F t (I t) f
    toF x = case unconsTM x of
      L1 y -> Done y
      R1 z -> More . hright toF $ z
    appendF  :: t (F t (I t) f) (F t (I t) f) ~> F t (I t) f
    appendF = toF . appendTM . hbimap fromF fromF

    retractT :: C (TM t) f => t f f ~> f
    retractT = retract . toTM
    injectT  :: C (TM t) f => I t ~> f
    injectT  = retract . fromF @t . Done

    toTM     :: t f f ~> TM t f
    toTM     = fromF . More . hright (More . hright Done . intro1)

    {-# MINIMAL nilTM, consTM, unconsTM, appendTM | fromF, toF, appendF #-}

instance HBifunctor t => HFunctor (F t i) where
    hmap f = \case
      Done x  -> Done x
      More xs -> More . hbimap f (hmap f) $ xs

injectF :: forall t f. Tensor t => f ~> F t (I t) f
injectF = More . hright Done . intro1

retractF
    :: forall t f. (Monoidal t, C (TM t) f)
    => F t (I t) f ~> f
retractF = \case
    Done x  -> injectT @t x
    More xs -> retractT . hright retractF $ xs

interpretF
    :: forall t f g. (Monoidal t, C (TM t) g)
    => (f ~> g)
    -> F t (I t) f ~> g
interpretF f = \case
    Done x  -> injectT @t x
    More xs -> retractT @t . hbimap f (interpretF f) $ xs

instance HFunctor Coyoneda where
    hmap = hoistCoyoneda

instance Interpret Coyoneda where
    type C Coyoneda = Functor
    inject  = liftCoyoneda
    retract = lowerCoyoneda
    interpret f (Coyoneda g x) = g <$> f x

instance HFunctor Ap where
    hmap = hoistAp

instance Interpret Ap where
    type C Ap = Applicative
    inject    = liftAp
    interpret = runAp

instance HBifunctor (:*:) where
    hleft  f (x :*: y) = f x :*:   y
    hright g (x :*: y) =   x :*: g y
    hbimap f g (x :*: y) = f x :*: g y

instance Tensor (:*:) where
    type I (:*:) = Proxy

    intro1 = (:*: Proxy)
    intro2 = (Proxy :*:)

    elim1 (x :*: _) = x
    elim2 (_ :*: y) = y

    assoc (x :*: (y :*: z)) = (x :*: y) :*: z
    disassoc ((x :*: y) :*: z) = x :*: (y :*: z)

-- | This is the Free 'Plus'.
newtype ListF f a = ListF { runListF :: [f a] }
  deriving (Show, Eq, Ord, Functor)

instance Applicative f => Applicative (ListF f) where
    pure  = ListF . (:[]) . pure
    ListF fs <*> ListF xs = ListF $ liftA2 (<*>) fs xs

instance Monoidal (:*:) where
    type TM (:*:) = ListF

    nilTM  = const (ListF [])
    consTM (x :*: y) = ListF $ x : runListF y
    unconsTM (ListF xs) = case xs of
      []   -> L1 Proxy
      y:ys -> R1 $ y :*: ListF ys
    appendTM (ListF xs :*: ListF ys) = ListF (xs ++ ys)

    fromF = \case
      Done ~Proxy -> ListF []
      More (x :*: y) -> ListF $ x : runListF (fromF y)
    toF (ListF xs) = case xs of
      []   -> Done Proxy
      y:ys -> More (y :*: toF (ListF ys))
    appendF (x :*: y) = case x of
      Done ~Proxy       -> y
      More (x' :*: x'') -> More (x' :*: appendF (x'' :*: y))

    retractT (x :*: y) = x <!> y
    toTM (x :*: y) = ListF [x, y]

instance HFunctor ListF where
    hmap f (ListF xs) = ListF (map f xs)

instance Interpret ListF where
    type C ListF = Plus
    inject = ListF . (:[])
    retract = foldr (<!>) zero . runListF

instance HFunctor Alt.Alt where
    hmap = Alt.hoistAlt

instance Interpret Alt.Alt where
    type C Alt.Alt = Alternative
    inject = Alt.liftAlt
    interpret = Alt.runAlt

instance HBifunctor Day where
    hleft  = D.trans1
    hright = D.trans2
    hbimap f g (Day x y z) = Day (f x) (g y) z

instance Tensor Day where
    type I Day = Identity

    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1
    assoc    = D.assoc
    disassoc = D.disassoc

instance Monoidal Day where
    type TM Day = Ap

    nilTM              = pure . runIdentity
    consTM (Day x y z) = z <$> liftAp x <*> y
    unconsTM = \case
      Pure x -> L1 $ Identity x
      Ap x y -> R1 $ Day x y (&)
    appendTM (Day x y z) = z <$> x <*> y

    fromF = \case
      Done (Identity x) -> pure x
      More (Day x y z)  -> z <$> liftAp x <*> fromF y
    toF = \case
      Pure x -> Done $ Identity x
      Ap x y -> More $ Day x (toF y) (&)
    appendF (Day x y f) = case x of
      Done (Identity x')  -> f x' <$> y
      More (Day x' y' f') -> More $ Day x' (appendF (Day y' y (,))) $
        \a (b, c) -> f (f' a b) c

    retractT (Day x y z) = z <$> x <*> y
    toTM (Day x y z) = z <$> liftAp x <*> liftAp y

data VoidT a
  deriving (Show, Eq, Ord, Functor)

absurdT :: VoidT ~> f
absurdT = \case {}

data Step f a = Step { stepPos :: Natural, stepVal :: f a }
  deriving (Show, Eq, Ord, Functor)

instance HFunctor Step where
    hmap f (Step n x) = Step n (f x)

instance Interpret Step where
    type C Step = MonadWriter (Sum Natural)
    inject = Step 0
    retract (Step n x)     = tell (Sum n) *> x
    interpret f (Step n x) = tell (Sum n) *> f x

instance HBifunctor (:+:) where
    hleft f = \case
      L1 x -> L1 (f x)
      R1 y -> R1 y

    hright g = \case
      L1 x -> L1 x
      R1 y -> R1 (g y)

    hbimap f g = \case
      L1 x -> L1 (f x)
      R1 y -> R1 (g y)

instance Tensor (:+:) where
    type I (:+:) = VoidT

    intro1 = L1
    intro2 = R1
    elim1  = \case
      L1 x -> x
      R1 y -> absurdT y
    elim2  = \case
      L1 x -> absurdT x
      R1 y -> y
    assoc = \case
      L1 x      -> L1 (L1 x)
      R1 (L1 y) -> L1 (R1 y)
      R1 (R1 z) -> R1 z
    disassoc = \case
      L1 (L1 x) -> L1 x
      L1 (R1 y) -> R1 (L1 y)
      R1 z      -> R1 (R1 z)

instance Monoidal (:+:) where
    type TM (:+:) = Step

    nilTM = absurdT
    consTM = \case
      L1 x          -> Step 0       x
      R1 (Step n y) -> Step (n + 1) y
    unconsTM (Step n x) = R1 $ case minusNaturalMaybe n 1 of
      Nothing -> L1 x
      Just m  -> R1 (Step m x)
    appendTM = \case
      L1 x -> x
      R1 y -> y

    fromF = \case
      Done x      -> absurdT x
      More (L1 x) -> Step 0 x
      More (R1 y) -> case fromF y of
        Step n z -> Step (n + 1) z
    toF (Step n x) = go n
      where
        go (flip minusNaturalMaybe 1 -> i) = case i of
          Nothing -> More (L1 x)
          Just j  -> More (R1 (go j))
    appendF = \case
      L1 x -> x
      R1 y -> y     -- hm, what is this?

    retractT = \case
      L1 x -> x
      R1 y -> y
    toTM = \case
      L1 x -> Step 0 x
      R1 y -> Step 1 y

newtype WrappedHBifunctor t (f :: Type -> Type) (g :: Type -> Type) a
    = WrappedHBifunctor { unwrapHBifunctor :: t f g a }
  deriving Functor

instance HBifunctor t => HFunctor (WrappedHBifunctor t f) where
    hmap f = WrappedHBifunctor . hright f . unwrapHBifunctor

deriving via (WrappedHBifunctor Day f)    instance HFunctor (Day f)
deriving via (WrappedHBifunctor (:*:) f)  instance HFunctor ((:*:) f)
deriving via (WrappedHBifunctor (:+:) f)  instance HFunctor ((:+:) f)

instance HFunctor MC.F where
    hmap = MC.hoistF

data Cons
        :: ((Type -> Type) -> Type -> Type -> Type)
        -> (Type -> Type)
        -> (Type -> Type)
        -> Type
        -> Type where
    (:=>) :: f x -> p g x a -> Cons p f g a

instance (forall x. Functor (p g x)) => Functor (Cons p f g) where
    fmap f (x :=> y) = x :=> fmap f y

-- | Church-encoded Freer monad
newtype Free f a = Free
    { runFree :: forall r. (a -> r) -> (forall s. f s -> (s -> r) -> r) -> r
    }

instance Functor (Free f) where
    fmap f x = Free $ \p b -> runFree x (p . f) b

instance Applicative (Free f) where
    pure  = return
    (<*>) = ap

instance Monad (Free f) where
    return x = Free $ \p _ -> p x
    x >>= f  = Free $ \p b -> runFree x (\y -> runFree (f y) p b) b

instance M.MonadFree f (Free f) where
    wrap x = Free $ \p b -> b x $ \y -> runFree y p b

instance HFunctor Free where
    hmap f x = Free $ \p b -> runFree x p $ \y z -> b (f y) z

instance Interpret Free where
    type C Free = Monad

    inject x = Free $ \p b -> b x p
    retract x = runFree x pure (>>=)
    interpret f x = runFree x pure ((>>=) . f)

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

unDayCons :: Cons Static b c d -> Day b c d
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

