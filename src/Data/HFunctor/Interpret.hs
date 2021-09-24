-- |
-- Module      : Data.HFunctor.Interpret
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides tools for working with unary functor combinators
-- that represent interpretable schemas.
--
-- These are types @t@ that take a functor @f@ and return a new functor @t
-- f@, enhancing @f@ with new structure and abilities.
--
-- For these, we have:
--
-- @
-- 'inject' :: f a -> t f a
-- @
--
-- which lets you "lift" an @f a@ into its transformed version, and also:
--
-- @
-- 'interpret'
--     :: C t g
--     => (forall x. f a -> g a)
--     -> t f a
--     -> g a
-- @
--
-- that lets you "interpret" a @t f a@ into a context @g a@, essentially
-- "running" the computaiton that it encodes.  The context is required to
-- have a typeclass constraints that reflects what is "required" to be able
-- to run a functor combinator.
--
-- Every single instance provides different tools.  Check out the instance
-- list for a nice list of useful combinators, or also the README for
-- a high-level rundown.
--
-- See "Data.Functor.Tensor" for binary functor combinators that mix
-- together two or more different functors.
module Data.HFunctor.Interpret (
    Interpret(..), forI
  -- * Utilities
  , iget
  , icollect
  , icollect1
  , itraverse
  , iapply
  , ifanout
  , ifanout1
  , getI, collectI
  , AltConst(..)
  , AndC
  , WrapHF(..)
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Comonad.Trans.Env            (EnvT(..))
import           Control.Monad.Freer.Church
import           Control.Monad.Reader
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Data.Coerce
import           Data.Data
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Coyoneda
import           Data.Functor.Invariant
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Reverse
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.HFunctor
import           Data.HFunctor.Internal
import           Data.List.NonEmpty                   (NonEmpty(..))
import           Data.Maybe
import           Data.Pointed
import           Data.Semigroup                       (Endo(..))
import           Data.Semigroup.Foldable
import           GHC.Generics
import qualified Control.Alternative.Free             as Alt
import qualified Control.Applicative.Free             as Ap
import qualified Control.Applicative.Free.Fast        as FAF
import qualified Control.Applicative.Free.Final       as FA
import qualified Data.Functor.Contravariant.Coyoneda  as CCY
import qualified Data.Map.NonEmpty                    as NEM

-- | An 'Interpret' lets us move in and out of the "enhanced" 'Functor' (@t
-- f@) and the functor it enhances (@f@).  An instance @'Interpret' t f@
-- means we have @t f a -> f a@.
--
-- For example, @'Free' f@ is @f@ enhanced with monadic structure.  We get:
--
-- @
-- 'inject'    :: f a -> 'Free' f a
-- 'interpret' :: 'Monad' m => (forall x. f x -> m x) -> 'Free' f a -> m a
-- @
--
-- 'inject' will let us use our @f@ inside the enhanced @'Free' f@.
-- 'interpret' will let us "extract" the @f@ from a @'Free' f@ if
-- we can give an /interpreting function/ that interprets @f@ into some
-- target 'Monad'.
--
-- We enforce that:
--
-- @
-- 'interpret' id . 'inject' == id
-- -- or
-- 'retract' . 'inject' == id
-- @
--
-- That is, if we lift a value into our structure, then immediately
-- interpret it out as itself, it should lave the value unchanged.
--
-- Note that instances of this class are /intended/ to be written with @t@
-- as a fixed type constructor, and @f@ to be allowed to vary freely:
--
-- @
-- instance Monad f => Interpret Free f
-- @
--
-- Any other sort of instance and it's easy to run into problems with type
-- inference.  If you want to write an instance that's "polymorphic" on
-- tensor choice, use the 'WrapHF' newtype wrapper over a type variable,
-- where the second argument also uses a type constructor:
--
-- @
-- instance Interpret (WrapHF t) (MyFunctor t)
-- @
--
-- This will prevent problems with overloaded instances.
class Inject t => Interpret t f where

    -- | Remove the @f@ out of the enhanced @t f@ structure, provided that
    -- @f@ satisfies the necessary constraints.  If it doesn't, it needs to
    -- be properly 'interpret'ed out.
    retract :: t f ~> f
    retract = interpret id

    -- | Given an "interpeting function" from @f@ to @g@, interpret the @f@
    -- out of the @t f@ into a final context @g@.
    interpret :: (g ~> f) -> t g ~> f
    interpret f = retract . hmap f

    {-# MINIMAL retract | interpret #-}

-- | A convenient flipped version of 'interpret'.
forI
    :: Interpret t f
    => t g a
    -> (g ~> f)
    -> f a
forI x f = interpret f x

-- | Useful wrapper over 'interpret' to allow you to directly extract
-- a value @b@ out of the @t f a@, if you can convert @f x@ into @b@.
--
-- Note that depending on the constraints on @f@ in @'Interpret' t f@, you
-- may have extra constraints on @b@.
--
-- *    If @f@ is unconstrained, there are no constraints on @b@
-- *    If @f@ must be 'Apply', 'Alt', 'Divise', or 'Decide', @b@ needs to be an instance of 'Semigroup'.
-- *    If @f@ is 'Applicative', 'Plus', 'Divisible', or 'Conclude', @b@ needs to be an instance of 'Monoid'
--
-- For some constraints (like 'Monad'), this will not be usable.
--
-- @
-- -- get the length of the @Map String@ in the 'Step'.
-- 'icollect' length
--      :: Step (Map String) Bool
--      -> Int
-- @
--
-- Note that in many cases, you can also use
-- 'Data.HFunctor.HTraversable.hfoldMap' and
-- 'Data.HFunctor.HTraversable.hfoldMap1'.
--
-- @since 0.3.1.0
iget
    :: Interpret t (AltConst b)
    => (forall x. f x -> b)
    -> t f a
    -> b
iget f = getAltConst . interpret (AltConst . f)

-- | (Deprecated) Old name for 'getI'; will be removed in a future
-- version.
getI :: Interpret t (AltConst b) => (forall x. f x -> b) -> t f a -> b
getI = iget
{-# DEPRECATED getI "Use iget instead" #-}

-- | Useful wrapper over 'iget' to allow you to collect a @b@ from all
-- instances of @f@ inside a @t f a@.
--
-- Will work if there is an instance of @'Interpret' t ('AltConst' m)@ if @'Monoid'
-- m@, which will be the case if the constraint on the target
-- functor is 'Functor', 'Apply', 'Applicative', 'Alt', 'Plus',
-- 'Data.Functor.Contravariant.Decide.Decide', 'Divisible', 'Decide',
-- 'Conclude', or unconstrained.
--
-- @
-- -- get the lengths of all @Map String@s in the 'Ap.Ap'.
-- 'icollect' length
--      :: Ap (Map String) Bool
--      -> [Int]
-- @
--
-- Note that in many cases, you can also use
-- 'Data.HFunctor.HTraversable.htoList'.
--
-- @since 0.3.1.0
icollect
    :: (forall m. Monoid m => Interpret t (AltConst m))
    => (forall x. f x -> b)
    -> t f a
    -> [b]
icollect f = flip appEndo [] . iget (Endo . (:) . f)

-- | (Deprecated) Old name for 'icollect'; will be removed in a future
-- version.
collectI :: (forall m. Monoid m => Interpret t (AltConst m)) => (forall x. f x -> b) -> t f a -> [b]
collectI = icollect
{-# DEPRECATED collectI "Use icollect instead" #-}

-- | Useful wrapper over 'iget' to allow you to collect a @b@ from all
-- instances of @f@ inside a @t f a@, into a non-empty collection of @b@s.
--
-- Will work if there is an instance of @'Interpret' t ('AltConst' m)@ if
-- @'Semigroup' m@, which will be the case if the constraint on the target
-- functor is 'Functor', 'Apply', 'Alt', 'Divise', 'Decide', or
-- unconstrained.
--
-- @
-- -- get the lengths of all @Map String@s in the 'Ap.Ap'.
-- 'icollect1' length
--      :: Ap1 (Map String) Bool
--      -> 'NonEmpty' Int
-- @
--
-- Note that in many cases, you can also use
-- 'Data.HFunctor.HTraversable.htoNonEmpty'.
--
-- @since 0.3.1.0
icollect1
    :: (forall m. Semigroup m => Interpret t (AltConst m))
    => (forall x. f x -> b)
    -> t f a
    -> NonEmpty b
icollect1 f = fromNDL . iget (ndlSingleton . f)

-- | Useful wrapper over 'interpret' to allow you to do an "effectful"
-- 'hmap'.
--
-- This can be useful in some situations, but if you want to do this, it's
-- probably better to just use 'Data.HFunctor.HTraversable.htraverse',
-- which is a more principled system for effectful hmapping.
--
-- @since 0.3.6.0
itraverse
    :: (Functor h, Interpret t (Comp h (t g)))
    => (forall x. f x -> h (g x))
    -> t f a
    -> h (t g a)
itraverse f = unComp . interpret (\x -> f x :>>= inject)

-- | Useful wrapper over 'interpret' to allow you to directly consume
-- a value of type @a@ with a @t f a@ to create a @b@.  Do this by
-- supplying the method by which each component @f x@ can consume an @x@.
-- This works for contravariant functor combinators, where @t f a@ can be
-- interpreted as a consumer of @a@s.
--
-- Note that depending on the constraints on @f@ in @'Interpret' t f@, you
-- may have extra constraints on @b@.
--
-- *    If @f@ is unconstrained, 'Decide', or 'Conclude', there are no
--      constraints on @b@.  This will be the case for combinators like
--      contravariant 'CCY.Coyoneda', 'Dec', 'Dec1'.
-- *    If @f@ must be 'Divise', @b@ needs to be an instance of
--      'Semigroup'.  This will be the case for combinators like 'Div1'.
-- *    If @f@ is 'Divisible', @b@ needs to be an instance of 'Monoid'.
--      This will be the case for combinators like 'Div'.
--
-- For any 'Functor' or 'Invariant' constraint, this is not usable.
--
-- @since 0.3.2.0
iapply
    :: Interpret t (Op b)
    => (forall x. f x -> x -> b)
    -> t f a
    -> a
    -> b
iapply f = getOp . interpret (Op . f)

-- | Useful wrapper over 'interpret' to allow you to directly consume
-- a value of type @a@ with a @t f a@ to create a @b@, and create a list of
-- all the @b@s created by all the @f@s.  Do this by supplying the method
-- by which each component @f x@ can consume an @x@. This works for
-- contravariant functor combinators, where @t f a@ can be interpreted as
-- a consumer of @a@s.
--
-- Will work if there is an instance of @'Interpret' t ('Op' m)@ if @'Monoid'
-- m@, which will be the case if the constraint on the target
-- functor is 'Contravariant', 'Decide', 'Conclude', 'Divise', 'Divisible',
-- or unconstrained.
--
-- Note that this is really only useful outside of 'iapply' for 'Div' and
-- 'Div1', where a @'Div' f@ which is a collection of many different @f@s
-- consuming types of different values.  You can use this with 'Dec' and
-- 'Dec1' and the contravarient 'CCY.Coyoneda' as well, but those would
-- always just give you a singleton list, so you might as well use
-- 'iapply'.  This is really only here for completion alongside 'icollect',
-- or if you define your own custom functor combinators.
ifanout
    :: (forall m. Monoid m => Interpret t (Op m))
    => (forall x. f x -> x -> b)
    -> t f a
    -> a
    -> [b]
ifanout f t = flip appEndo [] . iapply (\x y -> Endo (f x y :)) t

-- | Useful wrapper over 'interpret' to allow you to directly consume
-- a value of type @a@ with a @t f a@ to create a @b@, and create a list of
-- all the @b@s created by all the @f@s.  Do this by supplying the method
-- by which each component @f x@ can consume an @x@. This works for
-- contravariant functor combinators, where @t f a@ can be interpreted as
-- a consumer of @a@s.
--
-- Will work if there is an instance of @'Interpret' t ('Op' m)@ if @'Monoid'
-- m@, which will be the case if the constraint on the target
-- functor is 'Contravariant', 'Decide', 'Divise', or unconstrained.
--
-- Note that this is really only useful outside of 'iapply' and 'ifanout'
-- for 'Div1', where a @'Div1' f@ which is a collection of many different
-- @f@s consuming types of different values.  You can use this with 'Dec'
-- and 'Dec1' and the contravarient 'CCY.Coyoneda' as well, but those would
-- always just give you a singleton list, so you might as well use
-- 'iapply'.  This is really only here for completion alongside
-- 'icollect1', or if you define your own custom functor combinators.
ifanout1
    :: (forall m. Semigroup m => Interpret t (Op m))
    => (forall x. f x -> x -> b)
    -> t f a
    -> a
    -> NonEmpty b
ifanout1 f t = fromNDL . iapply (\x -> ndlSingleton . f x) t



-- | A version of 'Const' that supports 'Alt', 'Plus', 'Decide', and
-- 'Conclude' instances.  It does this
-- by avoiding having an 'Alternative' or 'Decidable' instance, which
-- causes all sorts of problems with the interactions between
-- 'Alternative'/'Applicative' and
-- 'Decidable'/'Data.Functor.Contravariant.Divisible.Divisible'.
--
-- @since 0.3.1.0
newtype AltConst w a = AltConst { getAltConst :: w }
  deriving (Show, Eq, Ord, Generic, Functor, Foldable, Traversable, Data)

instance Show w => Show1 (AltConst w) where
    liftShowsPrec _ _ d (AltConst x) = showsUnaryWith showsPrec "AltConst" d x
instance Eq w => Eq1 (AltConst w) where
    liftEq _ (AltConst x) (AltConst y) = x == y
instance Ord w => Ord1 (AltConst w) where
    liftCompare _ (AltConst x) (AltConst y) = compare x y

instance Contravariant (AltConst w) where
    contramap _ = coerce
instance Invariant (AltConst w) where
    invmap _ _ = coerce

instance Semigroup w => Apply (AltConst w) where
    AltConst x <.> AltConst y = AltConst (x <> y)
instance Monoid w => Applicative (AltConst w) where
    (<*>) = (<.>)
    pure _ = AltConst mempty
-- | Unlike for 'Const', this is possible because there is no 'Alternative'
-- instance to complicate things.
instance Semigroup w => Alt (AltConst w) where
    AltConst x <!> AltConst y = AltConst (x <> y)
-- | Unlike for 'Const', this is possible because there is no 'Alternative'
-- instance to complicate things.
instance Monoid w => Plus (AltConst w) where
    zero = AltConst mempty

instance Semigroup w => Divise (AltConst w) where
    divise _ (AltConst x) (AltConst y) = AltConst (x <> y)
instance Monoid w => Divisible (AltConst w) where
    divide  = divise
    conquer = AltConst mempty
-- | Unlike for 'Const', this is possible because there is no 'Decidable'
-- instance to complicate things.
instance Semigroup w => Decide (AltConst w) where
    decide _ (AltConst x) (AltConst y) = AltConst (x <> y)
-- | Unlike for 'Const', this is possible because there is no 'Decidable'
-- instance to complicate things.
instance Monoid w => Conclude (AltConst w) where
    conclude _ = AltConst mempty

-- | A free 'Functor'
instance Functor f => Interpret Coyoneda f where
    retract                    = lowerCoyoneda
    interpret f (Coyoneda g x) = g <$> f x

-- | A free 'Contravariant'
--
-- @since 0.3.0.0
instance Contravariant f => Interpret CCY.Coyoneda f where
    retract                        = CCY.lowerCoyoneda
    interpret f (CCY.Coyoneda g x) = contramap g (f x)

-- | A free 'Applicative'
instance Applicative f => Interpret Ap.Ap f where
    retract   = \case
      Ap.Pure x  -> pure x
      Ap.Ap x xs -> x <**> retract xs
    interpret f x = Ap.runAp f x

-- | A free 'Plus'
instance Plus f => Interpret ListF f where
    retract     = foldr (<!>) zero . runListF
    interpret f = foldr ((<!>) . f) zero . runListF

-- | A free 'Alt'
instance Alt f => Interpret NonEmptyF f where
    retract     = asum1 . runNonEmptyF
    interpret f = asum1 . fmap f . runNonEmptyF

-- | Technically, @f@ is over-constrained: we only need @'zero' :: f a@,
-- but we don't really have that typeclass in any standard hierarchies.  We
-- use 'Plus' here instead, but we never use '<!>'.  This would only go
-- wrong in situations where your type supports 'zero' but not '<!>', like
-- instances of 'Control.Monad.Fail.MonadFail' without
-- 'Control.Monad.MonadPlus'.
instance Plus f => Interpret MaybeF f where
    retract     = fromMaybe zero . runMaybeF
    interpret f = maybe zero f . runMaybeF

instance (Monoid k, Plus f) => Interpret (MapF k) f where
    retract = foldr (<!>) zero . runMapF
    interpret f = foldr ((<!>) . f) zero . runMapF

instance (Monoid k, Alt f) => Interpret (NEMapF k) f where
    retract = asum1 . runNEMapF
    interpret f = asum1 . fmap f . runNEMapF

-- | Equivalent to instance for @'EnvT' ('Data.Semigroup.Sum'
-- 'Numeric.Natural.Natural')@.
instance Interpret Step f where
    retract = stepVal
    interpret f = f . stepVal

instance Alt f => Interpret Steps f where
    retract     = asum1 . getSteps
    interpret f = asum1 . NEM.map f . getSteps

-- | Equivalent to instance for @'EnvT' 'Data.Semigroup.Any'@ and @'HLift'
-- 'IdentityT'@.
instance Interpret Flagged f where
    retract = flaggedVal
    interpret f = f . flaggedVal

-- | Technically, @f@ is over-constrained: we only need @'zero' :: f a@,
-- but we don't really have that typeclass in any standard hierarchies.  We
-- use 'Plus' here instead, but we never use '<!>'.  This would only go
-- wrong in situations where your type supports 'zero' but not '<!>', like
-- instances of 'Control.Monad.Fail.MonadFail' without
-- 'Control.Monad.MonadPlus'.
instance Plus f => Interpret (These1 g) f where
    retract = \case
      This1  _   -> zero
      That1    y -> y
      These1 _ y -> y
    interpret f = \case
      This1  _   -> zero
      That1    y -> f y
      These1 _ y -> f y

-- | A free 'Alternative'
instance Alternative f => Interpret Alt.Alt f where
    interpret f x = Alt.runAlt f x

instance Plus g => Interpret ((:*:) g) f where
    retract (_ :*: y) = y

instance Plus g => Interpret (Product g) f where
    retract (Pair _ y) = y

-- | Technically, @f@ is over-constrained: we only need @'zero' :: f a@,
-- but we don't really have that typeclass in any standard hierarchies.  We
-- use 'Plus' here instead, but we never use '<!>'.  This would only go
-- wrong in situations where your type supports 'zero' but not '<!>', like
-- instances of 'Control.Monad.Fail.MonadFail' without
-- 'Control.Monad.MonadPlus'.
instance Plus f => Interpret ((:+:) g) f where
    retract = \case
      L1 _ -> zero
      R1 y -> y

-- | Technically, @f@ is over-constrained: we only need @'zero' :: f a@,
-- but we don't really have that typeclass in any standard hierarchies.  We
-- use 'Plus' here instead, but we never use '<!>'.  This would only go
-- wrong in situations where your type supports 'zero' but not '<!>', like
-- instances of 'Control.Monad.Fail.MonadFail' without
-- 'Control.Monad.MonadPlus'.
instance Plus f => Interpret (Sum g) f where
    retract = \case
      InL _ -> zero
      InR y -> y

instance Interpret (M1 i c) f where
    retract (M1 x) = x
    interpret f (M1 x) = f x

-- | A free 'Monad'
instance Monad f => Interpret Free f where
    retract   = retractFree
    interpret f x = interpretFree f x

-- | A free 'Bind'
instance Bind f => Interpret Free1 f where
    retract   = retractFree1
    interpret f x = interpretFree1 f x

-- | A free 'Applicative'
instance Applicative f => Interpret FA.Ap f where
    retract   = FA.retractAp
    interpret f x = FA.runAp f x

-- | A free 'Applicative'
instance Applicative f => Interpret FAF.Ap f where
    retract   = FAF.retractAp
    interpret f x = FAF.runAp f x

instance Interpret IdentityT f where
    retract = coerce
    interpret f = f . runIdentityT

-- | A free 'Pointed'
instance Pointed f => Interpret Lift f where
    retract   = elimLift point id
    interpret f x = elimLift point f x

-- | A free 'Pointed'
instance Pointed f => Interpret MaybeApply f where
    retract     = either id point . runMaybeApply
    interpret f = either f point . runMaybeApply

instance Interpret Backwards f where
    retract     = forwards
    interpret f = f . forwards

instance Interpret WrappedApplicative f where
    retract     = unwrapApplicative
    interpret f = f . unwrapApplicative

-- | A free 'MonadReader', but only when applied to a 'Monad'.
instance MonadReader r f => Interpret (ReaderT r) f where
    retract     x = runReaderT x =<< ask
    interpret f x = f . runReaderT x =<< ask

-- | This ignores the environment, so @'interpret' /= 'hbind'@
instance Monoid e => Interpret (EnvT e) f where
    retract     (EnvT _ x) = x
    interpret f (EnvT _ x) = f x

instance Interpret Reverse f where
    retract     = getReverse
    interpret f = f . getReverse

-- -- | The only way for this to obey @'retract' . 'inject' == 'id'@ is to
-- -- have it impossible to retract out of.
-- instance Impossible f => Interpret ProxyF f where
--     retract = nope . reProxy

-- reProxy :: p f a -> Proxy f
-- reProxy _ = Proxy

-- -- | The only way for this to obey @'retract' . 'inject' == 'id'@ is to
-- -- have it impossible to retract out of.
-- instance (Monoid e, Impossible f) => Interpret (ConstF e) f where
--     retract = nope . reProxy

-- | A constraint on @a@ for both @c a@ and @d a@.  Requiring @'AndC'
-- 'Show' 'Eq' a@ is the same as requiring @('Show' a, 'Eq' a)@.
class (c a, d a) => AndC c d a
instance (c a, d a) => AndC c d a

instance (Interpret s f, Interpret t f) => Interpret (ComposeT s t) f where
    retract     = interpret retract . getComposeT
    interpret f = interpret (interpret f) . getComposeT

-- | Never uses 'inject'
instance Interpret t f => Interpret (HLift t) f where
    retract = \case
      HPure  x -> x
      HOther x -> retract x
    interpret f = \case
      HPure  x -> f x
      HOther x -> interpret f x

-- | Never uses 'inject'
instance Interpret t f => Interpret (HFree t) f where
    retract = \case
      HReturn x -> x
      HJoin   x -> interpret retract x

-- | A newtype wrapper meant to be used to define polymorphic 'Interpret'
-- instances.  See documentation for 'Interpret' for more information.
--
-- Please do not ever define an instance of 'Interpret' "naked" on the
-- second parameter:
--
-- @
-- instance Interpret (WrapHF t) f
-- @
--
-- As that would globally ruin everything using 'WrapHF'.
newtype WrapHF t f a = WrapHF { unwrapHF :: t f a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

instance Show1 (t f) => Show1 (WrapHF t f) where
    liftShowsPrec sp sl d (WrapHF x) = showsUnaryWith (liftShowsPrec sp sl) "WrapHF" d x

instance Eq1 (t f) => Eq1 (WrapHF t f) where
    liftEq eq (WrapHF x) (WrapHF y) = liftEq eq x y

instance Ord1 (t f) => Ord1 (WrapHF t f) where
    liftCompare c (WrapHF x) (WrapHF y) = liftCompare c x y

instance HFunctor t => HFunctor (WrapHF t) where
    hmap f (WrapHF x) = WrapHF (hmap f x)

instance Inject t => Inject (WrapHF t) where
    inject = WrapHF . inject

instance HBind t => HBind (WrapHF t) where
    hbind f (WrapHF x) = WrapHF (hbind (unwrapHF . f) x)
    hjoin (WrapHF x) = WrapHF (hbind unwrapHF x)

