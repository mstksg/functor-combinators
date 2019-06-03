{-# LANGUAGE DeriveFunctor        #-}
{-# LANGUAGE DerivingVia          #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE LambdaCase           #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeInType           #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ViewPatterns         #-}

module Data.Functor.HBifunctor (
    HBifunctor(..)
  , WrappedHBifunctor(..)
  , overHBifunctor
  -- * Combinators
  , JoinT(..)
  , TannenT(..)
  , BiffT(..)
  , ClownT(..)
  , JokerT(..)
  ) where

import           Data.Functor.HFunctor.Internal
import           Data.Functor.HFunctor.IsoF
import           Data.Kind

overHBifunctor
    :: HBifunctor t
    => AnIsoF' f f'
    -> AnIsoF' g g'
    -> t f g <~> t f' g'
overHBifunctor (cloneIsoF' -> f) (cloneIsoF' -> g) =
        isoF (hbimap (viewF   f) (viewF   g))
             (hbimap (reviewF f) (reviewF g))

-- | Form an 'HFunctor' by applying the same input twice to an
-- 'HBifunctor'.
newtype JoinT t f a = JoinT { runJoinT :: t f f a }

deriving instance Functor (t f f) => Functor (JoinT t f)

instance HBifunctor t => HFunctor (JoinT t) where
    hmap f (JoinT x) = JoinT $ hbimap f f x

-- | Form an 'HBifunctor' by wrapping another 'HBifunctor' in a 'HFunctor'.
newtype TannenT t p f g a = TannenT { runTannenT :: t (p f g) a }

deriving instance Functor (t (p f g)) => Functor (TannenT t p f g)

instance (HFunctor t, HBifunctor p) => HBifunctor (TannenT t p) where
    hbimap f g (TannenT x) = TannenT (hmap (hbimap f g) x)

deriving via (WrappedHBifunctor (TannenT (t :: (Type -> Type) -> Type -> Type) p) f)
    instance (HFunctor t, HBifunctor p) => HFunctor (TannenT t p f)

-- | Form an 'HBifunctor' over two 'HFunctor's.
newtype BiffT p s t f g a = BiffT { runBiffT :: p (s f) (t g) a }

deriving instance Functor (p (s f) (t g)) => Functor (BiffT p s t f g)

instance (HBifunctor p, HFunctor s, HFunctor t) => HBifunctor (BiffT p s t) where
    hbimap f g (BiffT x) = BiffT (hbimap (hmap f) (hmap g) x)

deriving via (WrappedHBifunctor (BiffT (p :: (Type -> Type) -> (Type -> Type) -> Type -> Type) s t) f)
    instance (HBifunctor p, HFunctor s, HFunctor t) => HFunctor (BiffT p s t f)

-- | Form an 'HBifunctor' over a 'HFunctor' by ignoring the second
-- argument.
newtype ClownT t f g a = ClownT { runClownT :: t f a }
    deriving (Eq, Ord, Show, Read)

deriving instance Functor (t f) => Functor (ClownT t f g)

instance HFunctor t => HBifunctor (ClownT t) where
    hbimap f _ (ClownT x) = ClownT (hmap f x)

deriving via (WrappedHBifunctor (ClownT t) f)
    instance HFunctor t => HFunctor (ClownT t f)

-- | Form an 'HBifunctor' over a 'HFunctor' by ignoring the first
-- argument.
newtype JokerT t f g a = JokerT { runJokerT :: t g a }
    deriving (Eq, Ord, Show, Read)

deriving instance Functor (t g) => Functor (JokerT t f g)

instance HFunctor t => HBifunctor (JokerT t) where
    hbimap _ g (JokerT x) = JokerT (hmap g x)

deriving via (WrappedHBifunctor (JokerT t) f)
    instance HFunctor t => HFunctor (JokerT t f)

