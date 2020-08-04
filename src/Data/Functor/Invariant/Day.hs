
module Data.Functor.Invariant.Day (
    Day(..)
  , day
  , runDayApply
  , runDayDivise
  , toCoDay
  , toContraDay
  , assoc, unassoc
  , intro1, intro2
  , elim1, elim2
  , swap
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Functor.Apply
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.HBifunctor
import           Data.HBifunctor.Associative hiding (assoc)
import           Data.HBifunctor.Tensor hiding      (elim1, elim2, intro1, intro2)
import           Data.HFunctor
import           Data.HFunctor.Chain
import           Data.Kind
import qualified Data.Bifunctor.Assoc               as B
import qualified Data.Bifunctor.Swap                as B
import qualified Data.Functor.Contravariant.Day     as CD
import qualified Data.Functor.Day                   as D
import qualified Data.HBifunctor.Tensor             as T

data Day :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Day :: f b
        -> g c
        -> (a -> (b, c))
        -> (b -> c -> a)
        -> Day f g a

day :: f a -> g b -> Day f g (a, b)
day x y = Day x y id (,)

runDayApply
    :: forall f g h. Apply h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayApply f g (Day x y _ j) = liftF2 j (f x) (g y)

runDayDivise
    :: forall f g h. Divise h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayDivise f g (Day x y h _) = divise h (f x) (g y)

toCoDay :: Day f g ~> D.Day f g
toCoDay (Day x y _ g) = D.Day x y g

toContraDay :: Day f g ~> CD.Day f g
toContraDay (Day x y f _) = CD.Day x y f

-- | 'Day' is associative.
assoc :: Day f (Day g h) ~> Day (Day f g) h
assoc (Day x (Day y z f g) h j) =
    Day (Day x y id (,)) z
      (B.unassoc . second f . h)
      (\(a,b) c -> j a (g b c))

-- | 'Day' is associative.
unassoc :: Day (Day f g) h ~> Day f (Day g h)
unassoc (Day (Day x y f g) z h j) =
    Day x (Day y z id (,))
      (B.assoc . first f . h)
      (\a (b, c) -> j (g a b) c)

intro1 :: g ~> Day Identity g
intro1 y = Day (Identity ()) y ((),) (const id)

intro2 :: f ~> Day f Identity
intro2 x = Day x (Identity ()) (,()) const

elim1 :: Invariant g => Day Identity g ~> g
elim1 (Day (Identity x) y f g) = invmap (g x) (snd . f) y

elim2 :: Invariant f => Day f Identity ~> f
elim2 (Day x (Identity y) f g) = invmap (`g` y) (fst . f) x

swap :: Day f g ~> Day g f
swap (Day x y f g) = Day y x (B.swap . f) (flip g)

instance HBifunctor Day where
    hbimap f g (Day x y h j) = Day (f x) (g y) h j

instance Associative Day where
    type NonEmptyBy Day = Chain1 Day
    type FunctorBy Day = Invariant
    associating = isoF assoc unassoc

    appendNE (Day xs ys f g) = case xs of
      Done1 x              -> More1 (Day x ys f g)
      More1 (Day z zs h j) -> More1 $
        Day z (appendNE (Day zs ys id (,)))
          (B.assoc . first h . f)
          (\a (b, c) -> g (j a b) c)
    matchNE = matchChain1

    consNE = More1
    toNonEmptyBy = More1 . hright Done1

instance Tensor Day Identity where
    type ListBy Day = Chain Day Identity

    intro1 = intro2
    intro2 = intro1
    elim1 = elim2
    elim2 = elim1

    appendLB = appendChain
    splitNE = splitChain1
    splittingLB = splittingChain

    toListBy = More . hright inject
