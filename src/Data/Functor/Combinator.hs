{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DeriveFunctor          #-}
{-# LANGUAGE EmptyCase              #-}
{-# LANGUAGE EmptyDataDeriving      #-}
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
{-# LANGUAGE UndecidableInstances   #-}

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
  , listFAlt, altListF
  ) where

-- import           Control.Monad
-- import           Control.Monad.Codensity
import           Control.Alternative.Free   (Alt(..))
import           Control.Applicative
import           Control.Applicative.Free
import           Control.Monad.Reader
import           Data.Foldable
import           Data.Functor.Coyoneda
import           Data.Functor.Day           (Day(..))
import           Data.Functor.Identity
import           Data.Kind
import           Data.Profunctor
import           Data.Proxy
import           Data.Traversable
import           GHC.Generics hiding        (C)
import           Numeric.Natural
import qualified Control.Alternative.Free   as Alt
import qualified Control.Monad.Free.Church  as M
import qualified Data.Functor.Day           as D

type f ~> g = forall x. f x -> g x

infixr 0 ~>

class HFunctor t where
    map1 :: f ~> g -> t f ~> t g

class HFunctor t => Interpret t where
    type C t :: (Type -> Type) -> Constraint
    inject  :: f ~> t f

    retract :: C t f => t f ~> f
    retract = interpret id

    interpret :: C t g => (f ~> g) -> t f ~> g
    interpret f = retract . map1 f

class HBifunctor t where
    type I t :: Type -> Type

    hleft  :: f ~> j -> t f g ~> t j g
    hright :: g ~> k -> t f g ~> t f k

    hbimap :: f ~> j -> g ~> k -> t f g ~> t j k

type HIso f g = forall p x. Profunctor p => p (f x) (f x) -> p (g x) (g x)

class (HBifunctor t, Functor (I t)) => Tensor t where
    intro1 :: f ~> t f (I t)
    intro2 :: g ~> t (I t) g

    elim1  :: Functor f => t f (I t) ~> f
    elim2  :: Functor g => t (I t) g ~> g

    assoc    :: (Functor f, Functor g, Functor h) => t f (t g h) ~> t (t f g) h
    disassoc :: (Functor f, Functor g, Functor h) => t (t f g) h ~> t f (t g h)

data Free t i f a = Done (i a)
                  | More (t f (Free t i f) a)

class Tensor t => Monoidal t where
    type TM t :: (Type -> Type) -> Type -> Type
    toTM     :: t f f ~> TM t f
    fromFree :: Free t (I t) f ~> TM t f

retractT
    :: ( Monoidal t
       , Interpret (TM t)
       , C (TM t) f
       )
    => t f f
    ~> f
retractT = retract . toTM

toFree
    :: ( Monoidal t
       , Interpret (TM t)
       , C (TM t) (Free t (I t) f)
       )
    => TM t f
    ~> Free t (I t) f
toFree = retract . map1 (More . hright Done . intro1)

instance HFunctor Coyoneda where
    map1 = hoistCoyoneda

instance Interpret Coyoneda where
    type C Coyoneda = Functor
    inject  = liftCoyoneda
    retract = lowerCoyoneda
    interpret f (Coyoneda g x) = g <$> f x

instance HFunctor Ap where
    map1 = hoistAp

instance Interpret Ap where
    type C Ap = Applicative
    inject    = liftAp
    interpret = runAp

instance HBifunctor (:*:) where
    type I (:*:) = Proxy
    hleft  f (x :*: y) = f x :*:   y
    hright g (x :*: y) =   x :*: g y
    hbimap f g (x :*: y) = f x :*: g y

instance Tensor (:*:) where
    intro1 = (:*: Proxy)
    intro2 = (Proxy :*:)

    elim1 (x :*: _) = x
    elim2 (_ :*: y) = y

    assoc (x :*: (y :*: z)) = (x :*: y) :*: z
    disassoc ((x :*: y) :*: z) = x :*: (y :*: z)

newtype ListF f a = ListF { runListF :: [f a] }
  deriving (Show, Eq, Ord, Functor)

-- | We can embed 'ListF' in 'Alt'.  However, we can't go backwards,
-- because 'Alt' allows multiplication as well as addition.
listFAlt :: ListF f ~> Alt f
listFAlt = retract . map1 Alt.liftAlt

-- | Extract an 'Alt' back into a 'ListF', but fail if any '<*>' was used.
-- Should be a (partial) inverse with 'listFAlt'.
altListF :: forall f. Functor f => Alt f ~> Maybe :.: ListF f
altListF (Alt xs) = Comp1 . fmap (ListF . concat) . traverse go $ xs
  where
    go :: Alt.AltF f x -> Maybe [f x]
    go = \case
      Alt.Ap x (Alt fs) -> for fs $ \case
        Alt.Pure f -> Just (f <$> x)
        _          -> Nothing
      _                 -> Nothing

instance Applicative f => Applicative (ListF f) where
    pure  = ListF . (:[]) . pure
    ListF fs <*> ListF xs = ListF $ liftA2 (<*>) fs xs

instance Monoidal (:*:) where
    -- this could almost be Alt, but there is too much structure there
    type TM (:*:) = ListF

    toTM (x :*: y) = ListF [x, y]
    fromFree = \case
      Done _ -> ListF []
      More (x :*: y) -> ListF $ x : runListF (fromFree y)

instance HFunctor ListF where
    map1 f (ListF xs) = ListF (map f xs)

instance Interpret ListF where
    type C ListF = Alternative
    inject = ListF . (:[])
    retract = asum . runListF

instance HFunctor Alt where
    map1 = Alt.hoistAlt

instance Interpret Alt where
    type C Alt = Alternative
    inject = Alt.liftAlt
    interpret = Alt.runAlt

instance HBifunctor Day where
    type I Day = Identity

    hleft  = D.trans1
    hright = D.trans2
    hbimap f g (Day x y z) = Day (f x) (g y) z

instance Tensor Day where
    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1
    assoc    = D.assoc
    disassoc = D.disassoc

instance Monoidal Day where
    type TM Day = Ap
    toTM (Day x y z) = z <$> liftAp x <*> liftAp y
    fromFree = \case
      Done (Identity x) -> pure x
      More (Day x y z)  -> z <$> liftAp x <*> fromFree y

data VoidT a
  deriving (Show, Eq, Ord, Functor)

absurdT :: VoidT ~> f
absurdT = \case {}

data Step f a = Step { stepPos :: Natural, stepVal :: f a }
  deriving (Show, Eq, Ord, Functor)

instance HFunctor Step where
    map1 f (Step n x) = Step n (f x)

instance Interpret Step where
    type C Step = MonadReader Natural
    inject = Step 0
    retract (Step n x) = local (+ n) x
    interpret f (Step n x) = local (+ n) (f x)

instance HBifunctor (:+:) where
    type I (:+:) = VoidT

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
    toTM = \case
      L1 x -> Step 0 x
      R1 y -> Step 1 y
    fromFree = \case
      Done x      -> absurdT x
      More (L1 x) -> Step 0 x
      More (R1 y) -> case fromFree y of
        Step n z -> Step (n + 1) z


-- instance Functor f => Interpret ((:.:) f) where
--     type C ((:.:) f) = Monad f
--     inject x = Comp1 (pure x)
--     -- retract (Comp1 x) = join x

-- data Freer :: (Type -> Type) -> Type -> Type where
--     Purer   :: a -> Freer f a
--     Bindier :: f x -> (x -> Freer f a) -> Freer f a

-- instance Functor (Freer f) where
--     fmap f = \case
--       Purer x     -> Purer (f x)
--       Bindier x y -> Bindier x (fmap f . y)

-- instance Applicative (Freer f) where
--     pure  = Purer
--     (<*>) = ap

-- instance Monad (Freer f) where
--     return = pure
--     (>>=) = \case
--       Purer x     -> ($ x)
--       Bindier x y -> \f -> Bindier x ((f =<<) . y)

-- instance M.MonadFree f (Freer f) where
--     wrap = (`Bindier` id)

-- instance HFunctor Freer where
--     map1 f = \case
--       Purer x     -> Purer x
--       Bindier x y -> Bindier (f x) (map1 f . y)

-- instance Interpret Freer where
--     type C Freer = Monad
--     inject x = Bindier x Purer
--     retract  = \case
--       Purer x     -> pure x
--       Bindier x y -> retract . y =<< x

-- instance HBifunctor (:.:) where
--     type I (:.:) = Identity

--     hleft f  (Comp1 x) = Comp1 (f x)
    -- hright g (Comp1 x) = Comp1 (_ x)
    -- hbimap f g = _

instance Functor f => HFunctor ((:.:) f) where
    map1 f (Comp1 x) = Comp1 (fmap f x)

instance HFunctor M.F where
    map1 = M.hoistF

