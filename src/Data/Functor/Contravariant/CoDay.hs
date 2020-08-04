
module Data.Functor.Contravariant.CoDay (
    CoDay(..)
  , coDay
  , runCoDay
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
-- A @'CoDay' f g a@ is a contravariant "consumer" of @a@, and it does this
-- by either feeding the @a@ to @f@, or feeding the @a@ to @g@.  Which one
-- it gives it to happens at runtime depending /what/ @a@ is actually
-- given.
--
-- For example, if we have @x :: f a@ (a consumer of @a@s) and @y :: g b@
-- (a consumer of @b@s), then @'coDay' x y :: 'CoDay' f g ('Either' a b)@.
-- This is a consumer of @'Either' a b@s, and it consumes 'Left' branches
-- by feeding it to @x@, and 'Right' branches by feeding it to @y@.
data CoDay :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
    CoDay :: f b
          -> g c
          -> (a -> Either b c)
          -> CoDay f g a

-- | Inject into a 'CoDay'.
--
-- @'coDay' x y@ is a consumer of @'Either' a b@; 'Left' will be passed
-- to @x@, and 'Right' will be passed to @y@.
coDay
    :: f a
    -> g b
    -> CoDay f g (Either a b)
coDay x y = CoDay x y id

-- | Interpret out of a 'CoDay' into any instance of 'Choice' by providing
-- two interpreting functions.
runCoDay
    :: Choice h
    => (f ~> h)
    -> (g ~> h)
    -> CoDay f g ~> h
runCoDay f g (CoDay x y z) = choice z (f x) (g y)

-- | 'CoDay' is associative.
assoc :: CoDay f (CoDay g h) ~> CoDay (CoDay f g) h
assoc (CoDay x (CoDay y z f) g) = CoDay (CoDay x y id) z (B.unassoc . second f . g)

-- | 'CoDay' is associative.
unassoc :: CoDay (CoDay f g) h ~> CoDay f (CoDay g h)
unassoc (CoDay (CoDay x y f) z g) = CoDay x (CoDay y z id) (B.assoc . first f . g)

-- | The two sides of a 'CoDay' can be swapped.
swapped :: CoDay f g ~> CoDay g f
swapped (CoDay x y f) = CoDay y x (B.swap . f)

-- | Hoist a function over the left side of a 'CoDay'.
trans1 :: f ~> h -> CoDay f g ~> CoDay h g
trans1 f (CoDay x y z) = CoDay (f x) y z

-- | Hoist a function over the right side of a 'CoDay'.
trans2 :: g ~> h -> CoDay f g ~> CoDay f h
trans2 f (CoDay x y z) = CoDay x (f y) z

-- | A value of type @'Refuted' a@ is "proof" that @a@ is uninhabited.
newtype Refuted a = Refuted { refute :: a -> Void }

instance Contravariant Refuted where
    contramap f (Refuted g) = Refuted (g . f)

instance Semigroup (Refuted a) where
    Refuted f <> Refuted g = Refuted (f <> g)

-- | The left identity of 'CoDay' is 'Refuted'; this is one side of that
-- isomorphism.
intro1 :: g ~> CoDay Refuted g
intro1 x = CoDay (Refuted id) x Right

-- | The right identity of 'CoDay' is 'Refuted'; this is one side of that
-- isomorphism.
intro2 :: f ~> CoDay f Refuted
intro2 x = CoDay x (Refuted id) Left

-- | The left identity of 'CoDay' is 'Refuted'; this is one side of that
-- isomorphism.
elim1 :: Contravariant g => CoDay Refuted g ~> g
elim1 (CoDay x y z) = contramap (either (absurd . refute x) id . z) y

-- | The right identity of 'CoDay' is 'Refuted'; this is one side of that
-- isomorphism.
elim2 :: Contravariant f => CoDay f Refuted ~> f
elim2 (CoDay x y z) = contramap (either id (absurd . refute y) . z) x

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

-- data InvCoDay :: (Type -> Type) -> (Type -> Type) -> (Type -> Type) where
--     InvCoDay
--         :: f b
--         -> g c
--         -> (Either b c -> a)
--         -> (a -> Either b c)
--         -> InvCoDay f g a

-- introInvDay :: f ~> InvCoDay Refuted f
-- introInvDay x = InvCoDay (Refuted id) x (either absurd id) Right

-- elimInvDay :: Invariant f => InvCoDay Refuted f ~> f
-- elimInvDay (InvCoDay x y f g) = invmap (f . Right) (either (absurd . refute x) id . g) y
