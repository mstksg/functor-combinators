-- |
-- Module      : Data.HFunctor.Final
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides 'Final', which can be considered the "free 'Interpret' over
-- a constraint": generate a handy 'Interpret' instance for any constraint
-- @c@.
module Data.HFunctor.Final (
    Final(..)
  , fromFinal, toFinal
  , FreeOf(..), finalizing
  , hoistFinalC
  , liftFinal0
  , liftFinal1
  , liftFinal2
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Monad
import           Control.Monad.Freer.Church hiding         (toFree)
import           Control.Monad.Reader
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Constraint.Trivial
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Contravariant.Divisible.Free
import           Data.Functor.Coyoneda
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Inplicative
import           Data.Functor.Invariant.Inplicative.Free
import           Data.Functor.Invariant.Internative
import           Data.Functor.Invariant.Internative.Free
import           Data.Functor.Plus
import           Data.HFunctor
import           Data.HFunctor.Interpret
import           Data.Kind
import           Data.Pointed
import qualified Control.Alternative.Free                  as Alt
import qualified Control.Applicative.Free.Fast             as FAF
import qualified Data.Functor.Contravariant.Coyoneda       as CCY

-- | A simple way to inject/reject into any eventual typeclass.
--
-- In a way, this is the "ultimate" multi-purpose 'Interpret' instance.
-- You can use this to inject an @f@ into a free structure of any
-- typeclass.  If you want @f@ to have a 'Monad' instance, for example,
-- just use
--
-- @
-- 'inject' :: f a -> 'Final' 'Monad' f a
-- @
--
-- When you want to eventually interpret out the data, use:
--
-- @
-- 'interpret' :: (f '~>' g) -> 'Final' c f a -> g a
-- @
--
-- Essentially, @'Final' c@ is the "free c".  @'Final' 'Monad'@ is the free
-- 'Monad', etc.
--
-- 'Final' can theoretically replace 'Ap', 'Ap1', 'ListF', 'NonEmptyF',
-- 'MaybeF', 'Free', 'Data.Functor.Identity.Identity', 'Coyoneda', and
-- other instances of 'FreeOf', if you don't care about being able to
-- pattern match on explicit structure.
--
-- However, it cannot replace 'Interpret' instances that are not free
-- structures, like 'Control.Applicative.Step.Step',
-- 'Control.Applicative.Step.Steps',
-- 'Control.Applicative.Backwards.Backwards', etc.
--
-- Note that this doesn't have instances for /all/ the typeclasses you
-- could lift things into; you probably have to define your own if you want
-- to use @'Final' c@ as an /instance/ of @c@ (using 'liftFinal0',
-- 'liftFinal1', 'liftFinal2' for help).
newtype Final c f a = Final
    { runFinal :: forall g. c g => (forall x. f x -> g x) -> g a }

-- | Lift an action into a 'Final'.
liftFinal0
    :: (forall g. c g => g a)
    -> Final c f a
liftFinal0 x = Final $ \_ -> x

-- | Map the action in a 'Final'.
liftFinal1
    :: (forall g. c g => g a -> g b)
    -> Final c f a
    -> Final c f b
liftFinal1 f x = Final $ \r -> f (runFinal x r)

-- | Merge two 'Final' actions.
liftFinal2
    :: (forall g. c g => g a -> g b -> g d)
    -> Final c f a
    -> Final c f b
    -> Final c f d
liftFinal2 f x y = Final $ \r -> f (runFinal x r) (runFinal y r)

instance Functor (Final Functor f) where
    fmap f = liftFinal1 (fmap f)

instance Functor (Final Apply f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Apply f) where
    (<.>) = liftFinal2 (<.>)
    liftF2 f = liftFinal2 (liftF2 f)

instance Functor (Final Bind f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Bind f) where
    (<.>) = liftFinal2 (<.>)
    liftF2 f = liftFinal2 (liftF2 f)
instance Bind (Final Bind f) where
    x >>- f = Final $ \r -> runFinal x r >>- \y -> runFinal (f y) r

instance Functor (Final Applicative f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Applicative f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
instance Applicative (Final Applicative f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)

instance Functor (Final Alternative f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Alternative f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
instance Applicative (Final Alternative f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)
-- | @since 0.3.0.0
instance Alt (Final Alternative f) where
    (<!>) = liftFinal2 (<|>)
-- | @since 0.3.0.0
instance Plus (Final Alternative f) where
    zero = liftFinal0 empty
instance Alternative (Final Alternative f) where
    empty = liftFinal0 empty
    (<|>) = liftFinal2 (<|>)

instance Functor (Final Monad f) where
    fmap f = liftFinal1 (fmap f)
instance Apply (Final Monad f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
instance Applicative (Final Monad f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)
instance Monad (Final Monad f) where
    x >>= f  = Final $ \r -> do
      y <- runFinal x r
      runFinal (f y) r

instance Functor (Final MonadPlus f) where
    fmap f = liftFinal1 (fmap f)
instance Applicative (Final MonadPlus f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)
instance Monad (Final MonadPlus f) where
    x >>= f  = Final $ \r -> do
      y <- runFinal x r
      runFinal (f y) r
-- | @since 0.3.0.0
instance Alt (Final MonadPlus f) where
    (<!>) = liftFinal2 (<|>)
-- | @since 0.3.0.0
instance Plus (Final MonadPlus f) where
    zero = liftFinal0 empty
instance Alternative (Final MonadPlus f) where
    empty = liftFinal0 empty
    (<|>) = liftFinal2 (<|>)
instance MonadPlus (Final MonadPlus f) where
    mzero = liftFinal0 mzero
    mplus = liftFinal2 mplus

instance Pointed (Final Pointed f) where
    point x = liftFinal0 (point x)

instance Functor (Final (MonadReader r) f) where
    fmap f = liftFinal1 (fmap f)
instance Applicative (Final (MonadReader r) f) where
    pure x = liftFinal0 (pure x)
    (<*>)  = liftFinal2 (<*>)
    liftA2 f = liftFinal2 (liftA2 f)
instance Apply (Final (MonadReader r) f) where
    (<.>) = liftFinal2 (<*>)
    liftF2 f = liftFinal2 (liftA2 f)
instance Monad (Final (MonadReader r) f) where
    x >>= f  = Final $ \r -> do
      y <- runFinal x r
      runFinal (f y) r
instance MonadReader r (Final (MonadReader r) f) where
    ask     = liftFinal0 ask
    local f = liftFinal1 (local f)

instance Functor (Final Alt f) where
    fmap f = liftFinal1 (fmap f)
instance Alt (Final Alt f) where
    (<!>) = liftFinal2 (<!>)

instance Functor (Final Plus f) where
    fmap f = liftFinal1 (fmap f)
instance Alt (Final Plus f) where
    (<!>) = liftFinal2 (<!>)
instance Plus (Final Plus f) where
    zero = liftFinal0 zero

-- | @since 0.3.0.0
instance Contravariant (Final Contravariant f) where
    contramap f = liftFinal1 (contramap f)

-- | @since 0.3.0.0
instance Contravariant (Final Divise f) where
    contramap f = liftFinal1 (contramap f)
-- | @since 0.3.0.0
instance Divise (Final Divise f) where
    divise f = liftFinal2 (divise f)

-- | @since 0.3.0.0
instance Contravariant (Final Divisible f) where
    contramap f = liftFinal1 (contramap f)
-- | @since 0.3.0.0
instance Divise (Final Divisible f) where
    divise f = liftFinal2 (divide f)
-- | @since 0.3.0.0
instance Divisible (Final Divisible f) where
    divide f = liftFinal2 (divide f)
    conquer = liftFinal0 conquer

-- | @since 0.3.0.0
instance Contravariant (Final Decide f) where
    contramap f = liftFinal1 (contramap f)
-- | @since 0.3.0.0
instance Decide (Final Decide f) where
    decide f = liftFinal2 (decide f)

-- | @since 0.3.0.0
instance Contravariant (Final Conclude f) where
    contramap f = liftFinal1 (contramap f)
-- | @since 0.3.0.0
instance Decide (Final Conclude f) where
    decide f = liftFinal2 (decide f)
-- | @since 0.3.0.0
instance Conclude (Final Conclude f) where
    conclude f = liftFinal0 (conclude f)

-- | @since 0.3.0.0
instance Contravariant (Final Decidable f) where
    contramap f = liftFinal1 (contramap f)
-- | @since 0.3.0.0
instance Divisible (Final Decidable f) where
    divide f = liftFinal2 (divide f)
    conquer = liftFinal0 conquer
-- | @since 0.3.0.0
instance Decide (Final Decidable f) where
    decide f = liftFinal2 (choose f)
-- | @since 0.3.0.0
instance Conclude (Final Decidable f) where
    conclude f = liftFinal0 (lose f)
-- | @since 0.3.0.0
instance Decidable (Final Decidable f) where
    choose f = liftFinal2 (choose f)
    lose f = liftFinal0 (lose f)

-- | @since 0.3.0.0
instance Invariant (Final Invariant f) where
    invmap f g = liftFinal1 (invmap f g)

-- | @since 0.4.0.0
instance Invariant (Final Inply f) where
    invmap f g = liftFinal1 (invmap f g)
-- | @since 0.4.0.0
instance Inply (Final Inply f) where
    gather f g = liftFinal2 (gather f g)
    gathered = liftFinal2 gathered

-- | @since 0.4.0.0
instance Invariant (Final Inplicative f) where
    invmap f g = liftFinal1 (invmap f g)
-- | @since 0.4.0.0
instance Inply (Final Inplicative f) where
    gather f g = liftFinal2 (gather f g)
    gathered = liftFinal2 gathered
-- | @since 0.4.0.0
instance Inplicative (Final Inplicative f) where
    knot x = liftFinal0 (knot x)

-- | @since 0.4.0.0
instance Invariant (Final Inalt f) where
    invmap f g = liftFinal1 (invmap f g)
-- | @since 0.4.0.0
instance Inalt (Final Inalt f) where
    swerve f g h = liftFinal2 (swerve f g h)
    swerved = liftFinal2 swerved

-- | @since 0.4.0.0
instance Invariant (Final Inplus f) where
    invmap f g = liftFinal1 (invmap f g)
-- | @since 0.4.0.0
instance Inalt (Final Inplus f) where
    swerve f g h = liftFinal2 (swerve f g h)
    swerved = liftFinal2 swerved
-- | @since 0.4.0.0
instance Inplus (Final Inplus f) where
    reject f = liftFinal0 (reject f)

-- | @since 0.4.0.0
instance Invariant (Final Internative f) where
    invmap f g = liftFinal1 (invmap f g)
-- | @since 0.4.0.0
instance Inply (Final Internative f) where
    gather f g = liftFinal2 (gather f g)
    gathered = liftFinal2 gathered
-- | @since 0.4.0.0
instance Inplicative (Final Internative f) where
    knot x = liftFinal0 (knot x)
-- | @since 0.4.0.0
instance Inalt (Final Internative f) where
    swerve f g h = liftFinal2 (swerve f g h)
    swerved = liftFinal2 swerved
-- | @since 0.4.0.0
instance Inplus (Final Internative f) where
    reject f = liftFinal0 (reject f)

-- | Re-interpret the context under a 'Final'.
hoistFinalC
    :: (forall g x. (c g => g x) -> (d g => g x))
    -> Final c f a
    -> Final d f a
hoistFinalC f (Final x) = Final $ \r -> f (x (\y -> f (r y)))

instance HFunctor (Final c) where
    hmap f x = Final $ \r -> runFinal x (r . f)

instance Inject (Final c) where
    inject x = Final $ \f -> f x

instance c f => Interpret (Final c) f where
    retract x = runFinal x id
    interpret f x = runFinal x f

-- | "Finalize" an 'Interpret' instance.
--
-- @
-- toFinal :: 'Coyoneda' f '~>' 'Final' 'Functor' f
-- toFinal :: 'Ap' f '~>' 'Final' 'Applicative' f
-- toFinal :: 'Alt' f '~>' 'Final' 'Alternative' f
-- toFinal :: 'Free' f '~>' 'Final' 'Monad' f
-- toFinal :: 'Lift' f '~>' 'Final' 'Pointed' f
-- toFinal :: 'ListF' f '~>' 'Final' 'Plus' f
-- @
--
-- Note that the instance of @c@ for @'Final' c@ must be defined.
--
-- This operation can potentially /forget/ structure in @t@.  For example,
-- we have:
--
-- @
-- 'toFinal' :: 'Control.Applicative.Step.Steps' f ~> 'Final' 'Alt' f
-- @
--
-- In this process, we lose the "positional" structure of
-- 'Control.Applicative.Step.Steps'.
--
-- In the case where 'toFinal' doesn't lose any information, this will form
-- an isomorphism with 'fromFinal', and @t@ is known as the "Free @c@".
-- For such a situation, @t@ will have a 'FreeOf' instance.
toFinal :: Interpret t (Final c f) => t f ~> Final c f
toFinal = interpret inject

-- | "Concretize" a 'Final'.
--
-- @
-- fromFinal :: 'Final' 'Functor' f '~>' 'Coyoneda' f
-- fromFinal :: 'Final' 'Applicative' f '~>' 'Ap' f
-- fromFinal :: 'Final' 'Alternative' f '~>' 'Alt' f
-- fromFinal :: 'Final' 'Monad' f '~>' 'Free' f
-- fromFinal :: 'Final' 'Pointed' f '~>' 'Lift' f
-- fromFinal :: 'Final' 'Plus' f '~>' 'ListF' f
-- @
--
-- This can be useful because 'Final' doesn't have a concrete structure
-- that you can pattern match on and inspect, but @t@ might.
--
-- In the case that this forms an isomorphism with 'toFinal', the @t@ will
-- have an instance of 'FreeOf'.
fromFinal :: (Inject t, c (t f)) => Final c f ~> t f
fromFinal = interpret inject

-- | A typeclass associating a free structure with the typeclass it is free
-- on.
--
-- This essentially lists instances of 'Interpret' where a "trip" through
-- 'Final' will leave it unchanged.
--
-- @
-- 'fromFree' . 'toFree' == id
-- 'toFree' . 'fromFree' == id
-- @
--
-- This can be useful because 'Final' doesn't have a concrete structure
-- that you can pattern match on and inspect, but @t@ might.  This lets you
-- work on a concrete structure if you desire.
class FreeOf c t | t -> c where
    -- | What "type" of functor is expected: should be either
    -- 'Unconstrained', 'Functor', 'Contravariant', or 'Invariant'.
    --
    -- @since 0.3.0.0
    type FreeFunctorBy t :: (Type -> Type) -> Constraint
    type FreeFunctorBy t = Unconstrained

    fromFree :: t f ~> Final c f
    toFree   :: FreeFunctorBy t f => Final c f ~> t f

    default fromFree :: Interpret t (Final c f) => t f ~> Final c f
    fromFree = toFinal
    default toFree :: (Inject t, c (t f)) => Final c f ~> t f
    toFree = fromFinal

-- | The isomorphism between a free structure and its encoding as 'Final'.
finalizing :: (FreeOf c t, FreeFunctorBy t f) => t f <~> Final c f
finalizing = isoF fromFree toFree

instance FreeOf Functor       Coyoneda
-- | @since 0.3.0.0
instance FreeOf Contravariant CCY.Coyoneda
instance FreeOf Applicative   Ap
instance FreeOf Apply         Ap1
instance FreeOf Applicative   FAF.Ap
instance FreeOf Alternative   Alt.Alt
instance FreeOf Monad         Free
instance FreeOf Bind          Free1
instance FreeOf Pointed       Lift
instance FreeOf Pointed       MaybeApply
-- | This could also be @'FreeOf' 'Divise'@ if @'FreeFunctorBy' 'NonEmptyF'
-- ~ 'Contravariant'@.  However, there isn't really a way to express this
-- at the moment.
instance FreeOf Alt           NonEmptyF  where type FreeFunctorBy NonEmptyF = Functor
-- | This could also be @'FreeOf' 'Divisible'@ if @'FreeFunctorBy' 'ListF'
-- ~ 'Contravariant'@.  However, there isn't really a way to express this
-- at the moment.
instance FreeOf Plus          ListF      where type FreeFunctorBy ListF = Functor
-- | @since 0.3.0.0
instance FreeOf Divise        Div1
-- | @since 0.3.0.0
instance FreeOf Divisible     Div
-- | @since 0.3.0.0
instance FreeOf Decide        Dec1
-- | @since 0.3.0.0
instance FreeOf Conclude      Dec
-- | @since 0.4.0.0
instance FreeOf Inply         DivAp1    where type FreeFunctorBy DivAp1 = Invariant
-- | @since 0.4.0.0
instance FreeOf Inplicative   DivAp
-- | @since 0.4.0.0
instance FreeOf Inalt         DecAlt1   where type FreeFunctorBy DecAlt1 = Invariant
-- | @since 0.4.0.0
instance FreeOf Inplus        DecAlt
instance FreeOf Unconstrained IdentityT
