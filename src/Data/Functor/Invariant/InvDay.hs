
module Data.Functor.Invariant.InvDay (
    InvDay(..)
  , invDay
  , runInvDayAp
  , runInvDayDiv
  , toCoDay
  , toContraDay
  , intro1, intro2
  , elim1, elim2
  ) where

import           Control.Natural
import           Data.Functor.Apply
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Kind
import qualified Data.Functor.Contravariant.Day    as CD
import qualified Data.Functor.Day                  as D

data InvDay :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    InvDay :: f b
           -> g c
           -> (a -> (b, c))
           -> (b -> c -> a)
           -> InvDay f g a

invDay :: f a -> g b -> InvDay f g (a, b)
invDay x y = InvDay x y id (,)

runInvDayAp
    :: forall f g h. Apply h
    => f ~> h
    -> g ~> h
    -> InvDay f g ~> h
runInvDayAp f g (InvDay x y _ j) = liftF2 j (f x) (g y)

runInvDayDiv
    :: forall f g h. Divise h
    => f ~> h
    -> g ~> h
    -> InvDay f g ~> h
runInvDayDiv f g (InvDay x y h _) = divise h (f x) (g y)

toCoDay :: InvDay f g ~> D.Day f g
toCoDay (InvDay x y _ g) = D.Day x y g

toContraDay :: InvDay f g ~> CD.Day f g
toContraDay (InvDay x y f _) = CD.Day x y f

intro1 :: g ~> InvDay Identity g
intro1 y = InvDay (Identity ()) y ((),) (const id)

intro2 :: f ~> InvDay f Identity
intro2 x = InvDay x (Identity ()) (,()) const

elim1 :: Invariant g => InvDay Identity g ~> g
elim1 (InvDay (Identity x) y f g) = invmap (g x) (snd . f) y

elim2 :: Invariant f => InvDay f Identity ~> f
elim2 (InvDay x (Identity y) f g) = invmap (`g` y) (fst . f) x
