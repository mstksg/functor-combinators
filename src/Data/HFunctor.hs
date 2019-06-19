{-# LANGUAGE ConstraintKinds         #-}
{-# LANGUAGE DeriveDataTypeable      #-}
{-# LANGUAGE DeriveFoldable          #-}
{-# LANGUAGE DeriveFunctor           #-}
{-# LANGUAGE DeriveGeneric           #-}
{-# LANGUAGE DeriveTraversable       #-}
{-# LANGUAGE FlexibleInstances       #-}
{-# LANGUAGE InstanceSigs            #-}
{-# LANGUAGE LambdaCase              #-}
{-# LANGUAGE MultiParamTypeClasses   #-}
{-# LANGUAGE PolyKinds               #-}
{-# LANGUAGE RankNTypes              #-}
{-# LANGUAGE ScopedTypeVariables     #-}
{-# LANGUAGE StandaloneDeriving      #-}
{-# LANGUAGE TemplateHaskell         #-}
{-# LANGUAGE TypeFamilies            #-}
{-# LANGUAGE TypeInType              #-}
{-# LANGUAGE TypeOperators           #-}
{-# LANGUAGE UndecidableInstances    #-}
{-# LANGUAGE UndecidableSuperClasses #-}
{-# LANGUAGE ViewPatterns            #-}

-- |
-- Module      : Data.HFunctor
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides abstractions for working with unary functor combinators.
--
-- Principally, it defines the 'HFunctor' itself, as well as some classes
-- that expose extra functionality that some 'HFunctor's have ('Inject' and
-- 'HBind').
--
-- See "Data.HFunctor.Interpret" for tools to use 'HFunctor's as functor
-- combinators that can represent interpretable schemas, and
-- "Data.HBifunctor" for an abstraction over /binary/ functor combinators.
module Data.HFunctor (
    HFunctor(..)
  , overHFunctor
  , Inject(..)
  , HBind(..)
  -- * Simple instances
  , ProxyF(..)
  , ConstF(..)
  -- * 'HFunctor' Combinators
  , HLift(..), retractHLift
  , HFree(..), foldHFree, retractHFree
  ) where

import           Control.Applicative.Backwards
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Comonad.Trans.Env
import           Control.Monad.Freer.Church
import           Control.Monad.Reader
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Coerce
import           Data.Data
import           Data.Deriving
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Coyoneda
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Reverse
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.HFunctor.Internal
import           Data.List.NonEmpty             (NonEmpty(..))
import           Data.Pointed
import           Data.Semigroup.Foldable
import           GHC.Generics
import qualified Control.Alternative.Free       as Alt
import qualified Control.Applicative.Free.Fast  as FAF
import qualified Control.Applicative.Free.Final as FA
import qualified Data.Map                       as M
import qualified Data.Map.NonEmpty              as NEM

-- | Lift an isomorphism over an 'HFunctor'.
--
-- Essentailly, if @f@ and @g@ are isomorphic, then so are @t f@ and @t g@.
overHFunctor
    :: HFunctor t
    => f <~> g
    -> t f <~> t g
overHFunctor f = isoF (hmap (viewF f)) (hmap (reviewF f))

-- | The functor combinator that forgets all structure in the input.
-- Ignores the input structure and stores no information.
--
-- Acts like the "zero" with respect to functor combinator composition.
--
-- @
-- 'Control.Monad.Trans.Compose.ComposeT' ProxyF f      ~ ProxyF
-- 'Control.Monad.Trans.Compose.ComposeT' f      ProxyF ~ ProxyF
-- @
--
-- It can be 'inject'ed into (losing all information), but it is impossible
-- to ever 'Data.HFunctor.Interpret.retract' or
-- 'Data.HFunctor.Interpret.interpret' it.
--
-- This is essentially @'ConstF' ()@.
data ProxyF f a = ProxyF
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''ProxyF
deriveRead1 ''ProxyF
deriveEq1 ''ProxyF
deriveOrd1 ''ProxyF

instance HFunctor ProxyF where
    hmap _ = coerce

-- | Functor combinator that forgets all structure on the input, and
-- instead stores a value of type @e@.
--
-- Like 'ProxyF', acts like a "zero" with functor combinator composition.
--
-- It can be 'inject'ed into (losing all information), but it is impossible
-- to ever 'Data.HFunctor.Interpret.retract' or
-- 'Data.HFunctor.Interpret.interpret' it.
data ConstF e f a = ConstF { getConstF :: e }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''ConstF
deriveRead1 ''ConstF
deriveEq1 ''ConstF
deriveOrd1 ''ConstF

instance HFunctor (ConstF e) where
    hmap _ = coerce

-- | An "'HFunctor' combinator" that enhances an 'HFunctor' with the
-- ability to hold a single @f a@.  This is the higher-order analogue of
-- 'Control.Applicative.Lift.Lift'.
--
-- You can think of it as a free 'Inject' for any @f@.
--
-- Note that @'HLift' 'IdentityT'@ is equivalent to @'EnvT'
-- 'Data.Semigroup.Any'@.
data HLift t f a = HPure  (f a)
                 | HOther (t f a)
  deriving Functor

instance (Show1 (t f), Show1 f) => Show1 (HLift t f) where
    liftShowsPrec sp sl d = \case
      HPure x -> showsUnaryWith (liftShowsPrec sp sl) "HPure" d x
      HOther x -> showsUnaryWith (liftShowsPrec sp sl) "HOther" d x

deriving instance (Show (f a), Show (t f a)) => Show (HLift t f a)
deriving instance (Read (f a), Read (t f a)) => Read (HLift t f a)
deriving instance (Eq (f a), Eq (t f a)) => Eq (HLift t f a)
deriving instance (Ord (f a), Ord (t f a)) => Ord (HLift t f a)

instance (Eq1 (t f), Eq1 f) => Eq1 (HLift t f) where
    liftEq eq = \case
      HPure  x -> \case
        HPure  y -> liftEq eq x y
        HOther _ -> False
      HOther x -> \case
        HPure  _ -> False
        HOther y -> liftEq eq x y

instance (Ord1 (t f), Ord1 f) => Ord1 (HLift t f) where
    liftCompare c = \case
      HPure  x -> \case
        HPure  y -> liftCompare c x y
        HOther _ -> LT
      HOther x -> \case
        HPure  _ -> GT
        HOther y -> liftCompare c x y

instance HFunctor t => HFunctor (HLift t) where
    hmap f = \case
      HPure  x -> HPure  (f x)
      HOther x -> HOther (hmap f x)

-- | A higher-level 'Data.HFunctor.Interpret.retract' to get a @t f a@ back
-- out of an @'HLift' t f a@, provided @t@ is an instance of 'Inject'.
--
-- This witnesses the fact that 'HLift' is the "Free 'Inject'".
retractHLift
    :: Inject t
    => HLift t f a
    -> t f a
retractHLift = \case
    HPure  x -> inject x
    HOther x -> x

-- | An "'HFunctor' combinator" that turns an 'HFunctor' into potentially
-- infinite nestings of that 'HFunctor'.
--
-- An @'HFree' t f a@ is either @f a@, @t f a@, @t (t f) a@, @t (t (t f))
-- a@, etc.
--
-- This effectively turns @t@ into a tree with @t@ branches.
--
-- One particularly useful usage is with 'MapF'.  For example if you had
-- a data type representing a command line command parser:
--
-- @
-- data Command a
-- @
--
-- You could represent "many possible named commands" using
--
-- @
-- type Commands = 'MapF' 'String' Command
-- @
--
-- And you can represent multiple /nested/ named commands using:
--
-- @
-- type NestedCommands = 'HFree' ('MapF' 'String')
-- @
--
-- This has an 'Data.HFunctor.Interpret.Interpret' instance, but it can be
-- more useful to use via direct pattern matching, or through
--
-- @
-- 'foldHFree'
--     :: 'HBifunctor' t
--     => f '~>' g
--     -> t g ~> g
--     -> HFree t f ~> g
-- @
--
-- which requires no extra constriant on @g@, and lets you consider each
-- branch separately.
--
-- This can be considered the higher-oder analogue of
-- 'Control.Monad.Free.Free'; it is the free 'HBind' for any @'HFunctor'
-- t@.
--
-- Note that @'HFree' 'IdentityT'@ is equivalent to 'Step'.
data HFree t f a = HReturn (f a)
                 | HJoin   (t (HFree t f) a)

deriving instance (Functor f, Functor (t (HFree t f))) => Functor (HFree t f)

-- | Recursively fold down an 'HFree' into a single @g@ result, by handling
-- each branch.  Can be more useful than
-- 'Data.HFunctor.Interpret.interpret' because it allows you to treat each
-- branch separately, and also does not require any constraint on @g@.
--
-- This is the catamorphism on 'HFree'.
foldHFree
    :: forall t f g. HFunctor t
    => (f ~> g)
    -> (t g ~> g)
    -> (HFree t f ~> g)
foldHFree f g = go
  where
    go :: HFree t f ~> g
    go (HReturn x) = f x
    go (HJoin   x) = g (hmap go x)

-- | A higher-level 'Data.HFunctor.Interpret.retract' to get a @t f a@ back
-- out of an @'HFree' t f a@, provided @t@ is an instance of 'Bind'.
--
-- This witnesses the fact that 'HFree' is the "Free 'Bind'".
retractHFree
    :: HBind t
    => HFree t f a
    -> t f a
retractHFree = \case
    HReturn x -> inject x
    HJoin   x -> hbind retractHFree x

instance (Show1 (t (HFree t f)), Show1 f) => Show1 (HFree t f) where
    liftShowsPrec sp sl d = \case
      HReturn x -> showsUnaryWith (liftShowsPrec sp sl) "HReturn" d x
      HJoin   x -> showsUnaryWith (liftShowsPrec sp sl) "HJoin"   d x

instance (Show1 (t (HFree t f)), Show1 f, Show a) => Show (HFree t f a) where
    showsPrec = liftShowsPrec showsPrec showList

instance HFunctor t => HFunctor (HFree t) where
    hmap :: forall f g. (f ~> g) -> HFree t f ~> HFree t g
    hmap f = go
      where
        go :: HFree t f ~> HFree t g
        go = \case
          HReturn x -> HReturn (f x)
          HJoin   x -> HJoin (hmap go x)

-- | A typeclass for 'HFunctor's where you can "inject" an @f a@ into a @t
-- f a@:
--
-- @
-- 'inject' :: f a -> t f a
-- @
--
-- If you think of @t f a@ as an "enhanced @f@", then 'inject' allows you
-- to use an @f@ as its enhanced form.
--
-- With the exception of directly pattern matching on the result, 'inject'
-- itself is not too useful in the general case without
-- 'Data.HFunctor.Interpret.Interpret' to allow us to interpret or retrieve
-- back the @f@.
class HFunctor t => Inject t where
    -- | Lift from @f@ into the enhanced @t f@ structure.  Analogous to
    -- 'lift' from 'MonadTrans'.
    --
    -- Note that this lets us "lift" a @f a@; if you want to lift an @a@
    -- with @a -> t f a@, check if @t f@ is an instance of 'Applicative' or
    -- 'Pointed'.
    inject :: f ~> t f

    {-# MINIMAL inject #-}

-- | 'HBind' is effectively a "higher-order 'Monad'", in the sense that
-- 'HFunctor' is a "higher-order 'Functor'".
--
-- It can be considered a typeclass for 'HFunctor's that you can bind
-- continuations to, nautral/universal over all @f@/functors. They work
-- "for all functors" you lift, without requiring any constraints.
--
-- It is very similar to 'Data.HFunctor.Interpret.Interpret', except
-- 'Data.HFunctor.Interpret.Interpret' has the ability to constrain the
-- contexts to some typeclass.
--
-- The main law is that binding 'inject' should leave things unchanged:
--
-- @
-- 'hbind' 'inject' == 'id'
-- @
--
-- But 'hbind' should also be associatiatve, in a way that makes
--
-- @
-- 'hjoin' . hjoin
--    = hjoin . 'hmap' hjoin
-- @
--
-- That is, squishing a @t (t (t f)) a@ into a @t f a@ can be done "inside"
-- first, then "outside", or "outside" first, then "inside".
--
-- Note that these laws are different from the
-- 'Data.HFunctor.Interpret.Interpret' laws, so we often have instances
-- where 'hbind' and 'Data.HFunctor.Interpret.interpret' (though they both
-- may typecheck) produce different behavior.
--
-- This class is similar to 'Control.Monad.Morph.MMonad' from
-- "Control.Monad.Morph", but instances must work without a 'Monad' constraint.
class Inject t => HBind t where
    -- | Bind a continuation to a @t f@ into some context @g@.
    hbind :: (f ~> t g) -> t f ~> t g
    hbind f = hjoin . hmap f

    -- | Collapse a nested @t (t f)@ into a single @t f@.
    hjoin :: t (t f) ~> t f
    hjoin = hbind id
    {-# MINIMAL hbind | hjoin #-}

instance Inject Coyoneda where
    inject = liftCoyoneda

instance Inject Ap where
    inject = liftAp

instance Inject ListF where
    inject = ListF . (:[])

instance Inject NonEmptyF where
    inject = NonEmptyF . (:| [])

instance Inject MaybeF where
    inject = MaybeF . Just

-- | Injects into a singleton map at 'mempty'.
instance Monoid k => Inject (NEMapF k) where
    inject = NEMapF . NEM.singleton mempty

-- | Injects into a singleton map at 'mempty'.
instance Monoid k => Inject (MapF k) where
    inject = MapF . M.singleton mempty

-- | Injects with 0.
--
-- Equivalent to instance for @'EnvT' ('Data.Semigroup.Sum'
-- 'Numeric.Natural.Natural')@.
instance Inject Step where
    inject = Step 0

-- | Injects into a singleton map at 0; same behavior as @'NEMapF'
-- ('Data.Semigroup.Sum' 'Numeric.Natural.Natural')@.
instance Inject Steps where
    inject = Steps . NEM.singleton 0

-- | Injects with 'False'.
--
-- Equivalent to instance for @'EnvT' 'Data.Semigroup.Any'@ and @'HLift'
-- 'IdentityT'@.
instance Inject Flagged where
    inject = Flagged False

instance Inject (These1 f) where
    inject = That1

instance Applicative f => Inject (Comp f) where
    inject x = pure () :>>= const x

instance Applicative f => Inject ((:.:) f) where
    inject x = Comp1 $ pure x

-- | Only uses 'zero'
instance Plus f => Inject ((:*:) f) where
    inject = (zero :*:)

-- | Only uses 'zero'
instance Plus f => Inject (Product f) where
    inject = Pair zero

instance Inject ((:+:) f) where
    inject = R1

instance Inject (Sum f) where
    inject = InR

instance Inject (M1 i c) where
    inject = M1

instance Inject Alt.Alt where
    inject = Alt.liftAlt

instance Inject Free where
    inject = liftFree

instance Inject Free1 where
    inject = liftFree1

instance Inject FA.Ap where
    inject = FA.liftAp

instance Inject FAF.Ap where
    inject = FAF.liftAp

instance Inject IdentityT where
    inject = coerce

instance Inject Lift where
    inject = Other

instance Inject MaybeApply where
    inject = MaybeApply . Left

instance Inject Backwards where
    inject = Backwards

instance Inject WrappedApplicative where
    inject = WrapApplicative

instance Inject (ReaderT r) where
    inject = ReaderT . const

instance Monoid e => Inject (EnvT e) where
    inject = EnvT mempty

instance Inject Reverse where
    inject = Reverse

instance Inject ProxyF where
    inject _ = ProxyF

instance Monoid e => Inject (ConstF e) where
    inject _ = ConstF mempty

instance (Inject s, Inject t) => Inject (ComposeT s t) where
    inject = ComposeT . inject . inject

instance HFunctor t => Inject (HLift t) where
    inject = HPure

-- | 'HFree' is the "free 'HBind' and 'Inject'" for any 'HFunctor'
instance HFunctor t => Inject (HFree t) where
    inject = HReturn

instance HBind Coyoneda where
    hbind f (Coyoneda g x) = g <$> f x

instance HBind Ap where
    hbind = runAp

instance HBind ListF where
    hbind f = foldMap f . runListF

instance HBind NonEmptyF where
    hbind f = foldMap1 f . runNonEmptyF

instance HBind MaybeF where
    hbind f = foldMap f . runMaybeF

-- | Equivalent to instance for @'EnvT' ('Data.Semigroup.Sum'
-- 'Numeric.Natural.Natural')@.
instance HBind Step where
    hbind f (Step n x) = Step (n + m) y
      where
        Step m y = f x

-- | Equivalent to instance for @'EnvT' 'Data.Semigroup.Any'@ and @'HLift'
-- 'IdentityT'@.
instance HBind Flagged where
    hbind f (Flagged p x) = Flagged (p || q) y
      where
        Flagged q y = f x

instance Alt f => HBind (These1 f) where
    hbind f = \case
      This1  x   -> This1 x
      That1    y -> f y
      These1 x y -> case f y of
        This1  x'    -> This1 (x <!> x')
        That1     y' -> That1 y'
        These1 x' y' -> These1 (x <!> x') y'

instance Plus f => HBind ((:*:) f) where
    hbind f (x :*: y) = (x <!> x') :*: y'
      where
        x' :*: y' = f y

instance Plus f => HBind (Product f) where
    hbind f (Pair x y) = Pair (x <!> x') y'
      where
        Pair x' y' = f y

instance HBind ((:+:) f) where
    hbind f = \case
      L1 x -> L1 x
      R1 y -> f y

instance HBind (Sum f) where
    hbind f = \case
      InL x -> InL x
      InR y -> f y

instance HBind (M1 i c) where
    hbind f (M1 x) = f x

instance HBind Alt.Alt where
    hbind = Alt.runAlt

instance HBind Free where
    hbind = interpretFree

instance HBind Free1 where
    hbind = interpretFree1

instance HBind FA.Ap where
    hbind = FA.runAp

instance HBind FAF.Ap where
    hbind = FAF.runAp

instance HBind IdentityT where
    hbind f = f . runIdentityT

instance HBind Lift where
    hbind = elimLift point

instance HBind MaybeApply where
    hbind f = either f point . runMaybeApply

instance HBind Backwards where
    hbind f = f . forwards

instance HBind WrappedApplicative where
    hbind f = f . unwrapApplicative

instance HBind Reverse where
    hbind f = f . getReverse

instance HBind ProxyF where
    hbind _ = coerce

-- | Combines the accumulators, Writer-style
instance Monoid e => HBind (EnvT e) where
    hbind f (EnvT e x) = EnvT (e <> e') y
      where
        EnvT e' y = f x

instance (HBind t, Inject t) => HBind (HLift t) where
    hbind f = \case
      HPure   x -> f x
      HOther x -> HOther $ (`hbind` x) $ \y -> case f y of
        HPure  z -> inject z
        HOther z -> z

-- | 'HFree' is the "free 'HBind'" for any 'HFunctor'
instance HFunctor t => HBind (HFree t) where
    hbind f = \case
      HReturn x -> f x
      HJoin   x -> HJoin $ hmap (hbind f) x
