
module Data.Functor.Contravariant.Night (
    Night(..)
  , night
  , runNight
  , assoc, unassoc
  , swapped
  , trans1, trans2
  , intro1, intro2
  , elim1, elim2
  , Refuted(..)
  ) where

import           Control.Natural
import           Data.Bifunctor
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Divise
import           Data.Kind
import           Data.Void
import qualified Data.Bifunctor.Assoc              as B
import qualified Data.Bifunctor.Swap               as B

-- | A pairing of contravariant functors to create a new contravariant
-- functor that represents the "choice" between the two.
--
-- A @'Night' f g a@ is a contravariant "consumer" of @a@, and it does this
-- by either feeding the @a@ to @f@, or feeding the @a@ to @g@.  Which one
-- it gives it to happens at runtime depending /what/ @a@ is actually
-- given.
--
-- For example, if we have @x :: f a@ (a consumer of @a@s) and @y :: g b@
-- (a consumer of @b@s), then @'night' x y :: 'Night' f g ('Either' a b)@.
-- This is a consumer of @'Either' a b@s, and it consumes 'Left' branches
-- by feeding it to @x@, and 'Right' branches by feeding it to @y@.
--
-- The name 'Night' comes from a pun from the fact that this could be
-- considered the dual of the covariant 'Control.Functor.Day' -- the
-- "opposite" of Day.
data Night :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    Night :: f b
          -> g c
          -> (a -> Either b c)
          -> Night f g a

-- | Inject into a 'Night'.
--
-- @'night' x y@ is a consumer of @'Either' a b@; 'Left' will be passed
-- to @x@, and 'Right' will be passed to @y@.
night
    :: f a
    -> g b
    -> Night f g (Either a b)
night x y = Night x y id

-- | Interpret out of a 'Night' into any instance of 'Choice' by providing
-- two interpreting functions.
runNight
    :: Choice h
    => (f ~> h)
    -> (g ~> h)
    -> Night f g ~> h
runNight f g (Night x y z) = choice z (f x) (g y)

-- | 'Night' is associative.
assoc :: Night f (Night g h) ~> Night (Night f g) h
assoc (Night x (Night y z f) g) = Night (Night x y id) z (B.unassoc . second f . g)

-- | 'Night' is associative.
unassoc :: Night (Night f g) h ~> Night f (Night g h)
unassoc (Night (Night x y f) z g) = Night x (Night y z id) (B.assoc . first f . g)

-- | The two sides of a 'Night' can be swapped.
swapped :: Night f g ~> Night g f
swapped (Night x y f) = Night y x (B.swap . f)

-- | Hoist a function over the left side of a 'Night'.
trans1 :: f ~> h -> Night f g ~> Night h g
trans1 f (Night x y z) = Night (f x) y z

-- | Hoist a function over the right side of a 'Night'.
trans2 :: g ~> h -> Night f g ~> Night f h
trans2 f (Night x y z) = Night x (f y) z

-- | A value of type @'Refuted' a@ is "proof" that @a@ is uninhabited.
newtype Refuted a = Refuted { refute :: a -> Void }

instance Contravariant Refuted where
    contramap f (Refuted g) = Refuted (g . f)

instance Semigroup (Refuted a) where
    Refuted f <> Refuted g = Refuted (f <> g)

-- | The left identity of 'Night' is 'Refuted'; this is one side of that
-- isomorphism.
intro1 :: g ~> Night Refuted g
intro1 x = Night (Refuted id) x Right

-- | The right identity of 'Night' is 'Refuted'; this is one side of that
-- isomorphism.
intro2 :: f ~> Night f Refuted
intro2 x = Night x (Refuted id) Left

-- | The left identity of 'Night' is 'Refuted'; this is one side of that
-- isomorphism.
elim1 :: Contravariant g => Night Refuted g ~> g
elim1 (Night x y z) = contramap (either (absurd . refute x) id . z) y

-- | The right identity of 'Night' is 'Refuted'; this is one side of that
-- isomorphism.
elim2 :: Contravariant f => Night f Refuted ~> f
elim2 (Night x y z) = contramap (either id (absurd . refute y) . z) x

-- data InvDay :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
--     InvDay :: f b
--            -> g c
--            -> (a -> (b, c))
--            -> ((b, c) -> a)
--            -> InvDay f g a

-- invDay :: f a -> g b -> InvDay f g (a, b)
-- invDay x y = InvDay x y id id

-- introInv :: f ~> InvDay Identity f
-- introInv x = InvDay (Identity ()) x ((),) snd

-- elimInv :: Invariant f => InvDay Identity f ~> f
-- elimInv (InvDay (Identity x) y f g) = invmap (g . (x,)) (snd . f) y

-- data InvNight :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
--     InvNight
--         :: f b
--         -> g c
--         -> (Either b c -> a)
--         -> (a -> Either b c)
--         -> InvNight f g a

-- introInvDay :: f ~> InvNight Refuted f
-- introInvDay x = InvNight (Refuted id) x (either absurd id) Right

-- elimInvDay :: Invariant f => InvNight Refuted f ~> f
-- elimInvDay (InvNight x y f g) = invmap (f . Right) (either (absurd . refute x) id . g) y
