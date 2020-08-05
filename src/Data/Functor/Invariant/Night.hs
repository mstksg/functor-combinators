
module Data.Functor.Invariant.Night (
    Night(..)
  , Not(..)
  , night
  , runNightAlt
  , runNightDecide
  , toCoNight
  , toContraNight
  , assoc, unassoc
  , intro1, intro2
  , elim1, elim2
  , swap
  , runCoNightChain
  , runContraNightChain
  , runCoNightChain1
  , runContraNightChain1
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Functor.Alt
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Night   (Not(..))
import           Data.Functor.Invariant
import           Data.Functor.Plus
import           Data.HBifunctor
import           Data.HBifunctor.Associative hiding (assoc)
import           Data.HBifunctor.Tensor hiding      (elim1, elim2, intro1, intro2)
import           Data.HFunctor.Chain
import           Data.Kind
import           Data.Void
import           GHC.Generics
import qualified Data.Bifunctor.Assoc               as B
import qualified Data.Bifunctor.Swap                as B
import qualified Data.Functor.Contravariant.Night   as CN
import qualified Data.HBifunctor.Tensor             as T

data Night :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Night :: f b
          -> g c
          -> (a -> Either b c)
          -> (b -> a)
          -> (c -> a)
          -> Night f g a

night :: f a -> g b -> Night f g (Either a b)
night x y = Night x y id Left Right

runNightAlt
    :: forall f g h. Alt h
    => f ~> h
    -> g ~> h
    -> Night f g ~> h
runNightAlt f g (Night x y _ j k) = fmap j (f x) <!> fmap k (g y)

runNightDecide
    :: forall f g h. Decide h
    => f ~> h
    -> g ~> h
    -> Night f g ~> h
runNightDecide f g (Night x y h _ _) = decide h (f x) (g y)

-- | There is no covariant version of 'Night' defined in any common
-- library, so we use an equivalent type (if @f@ and @g@ are 'Functor's) @f
-- ':*:' g@.
toCoNight :: (Functor f, Functor g) => Night f g ~> f :*: g
toCoNight (Night x y _ f g) = fmap f x :*: fmap g y

toContraNight :: Night f g ~> CN.Night f g
toContraNight (Night x y f _ _) = CN.Night x y f

-- | 'Night' is associative.
assoc :: Night f (Night g h) ~> Night (Night f g) h
assoc (Night x (Night y z f g h) j k l) =
    Night (Night x y id Left Right) z
      (B.unassoc . second f . j)
      (either k (l . g))
      (l . h)

-- | 'Night' is associative.
unassoc :: Night (Night f g) h ~> Night f (Night g h)
unassoc (Night (Night x y f g h) z j k l) =
    Night x (Night y z id Left Right)
      (B.assoc . first f . j)
      (k . g)
      (either (k . h) l)

intro1 :: g ~> Night Not g
intro1 y = Night (Not id) y Right absurd id

intro2 :: f ~> Night f Not
intro2 x = Night x (Not id) Left id absurd

elim1 :: Invariant g => Night Not g ~> g
elim1 (Night x y f _ h) = invmap h (either (absurd . refute x) id . f) y

elim2 :: Invariant f => Night f Not ~> f
elim2 (Night x y f g _) = invmap g (either id (absurd . refute y) . f) x

swap :: Night f g ~> Night g f
swap (Night x y f g h) = Night y x (B.swap . f) h g

-- | In the covariant direction, we can interpret out of a 'Chain1' of 'Night'
-- into any 'Alt'.
runCoNightChain1
    :: forall f g. Alt g
    => f ~> g
    -> Chain1 Night f ~> g
runCoNightChain1 f = foldChain1 f (runNightAlt f id)

-- | In the contravariant direction, we can interpret out of a 'Chain1' of
-- 'Night' into any 'Decide'.
runContraNightChain1
    :: forall f g. Decide g
    => f ~> g
    -> Chain1 Night f ~> g
runContraNightChain1 f = foldChain1 f (runNightDecide f id)

-- | In the covariant direction, we can interpret out of a 'Chain' of 'Night'
-- into any 'Plus'.
runCoNightChain
    :: forall f g. Plus g
    => f ~> g
    -> Chain Night Not f ~> g
runCoNightChain f = foldChain (const zero) (runNightAlt f id)

-- | In the contravariant direction, we can interpret out of a 'Chain' of
-- 'Night' into any 'Conclude'.
runContraNightChain
    :: forall f g. Conclude g
    => f ~> g
    -> Chain Night Not f ~> g
runContraNightChain f = foldChain (conclude . refute) (runNightDecide f id)

instance HBifunctor Night where
    hbimap f g (Night x y h j k) = Night (f x) (g y) h j k

instance Associative Night where
    type NonEmptyBy Night = Chain1 Night
    type FunctorBy Night = Invariant
    associating = isoF assoc unassoc

    appendNE (Night xs ys f g h) = case xs of
      Done1 x                  -> More1 (Night x ys f g h)
      More1 (Night z zs j k l) -> More1 $
        Night z (appendNE (Night zs ys id Left Right))
          (B.assoc . first j . f)
          (g . k)
          (either (g . l) h)
    matchNE = matchChain1

    consNE = More1
    toNonEmptyBy = chain1Pair

instance Tensor Night Not where
    type ListBy Night = Chain Night Not

    intro1 = intro2
    intro2 = intro1
    elim1 = elim2
    elim2 = elim1

    appendLB = appendChain
    splitNE = splitChain1
    splittingLB = splittingChain

    toListBy = chainPair
