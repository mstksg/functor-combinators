{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE DerivingStrategies         #-}
{-# LANGUAGE DerivingVia                #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE EmptyDataDeriving          #-}
{-# LANGUAGE FlexibleContexts           #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE FunctionalDependencies     #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE InstanceSigs               #-}
{-# LANGUAGE KindSignatures             #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE MultiParamTypeClasses      #-}
{-# LANGUAGE PatternSynonyms            #-}
{-# LANGUAGE QuantifiedConstraints      #-}
{-# LANGUAGE RankNTypes                 #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE StandaloneDeriving         #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

-- |
-- Module      : Data.HBifunctor.Tensor
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides tools for working with binary functor combinators.
--
-- "Data.Functor.HFunctor" deals with /single/ functor combinators
-- (transforming a single functor).  This module provides tools for working
-- with combinators that combine and mix two functors "together".
--
-- The binary analog of 'HFunctor' is 'HBifunctor': we can map
-- a structure-transforming function over both of the transformed functors.
--
-- The binary analog of 'Interpret' is 'Monoidal' (and 'Tensor').  If your
-- combinator is an instance of 'Monoidal', it means that you can "squish"
-- both arguments together into an 'Interpret'.  For example:
--
-- @
-- 'toMF' :: (f ':*:' f) a -> 'ListF' f a
-- 'toMF' :: 'Comp' f f a -> 'Free' f a
-- 'toMF' :: 'Day' f f a -> 'Ap' f a
-- @
module Data.HBifunctor.Tensor (
  -- * 'Tensor'
    Tensor(..)
  , rightIdentity
  , leftIdentity
  , voidLeftIdentity
  , voidRightIdentity
  -- * 'Monoidal'
  , Monoidal(..)
  , nilMF
  , consMF
  , unconsMF
  -- ** Utility
  , inL
  , inR
  -- * 'Matchable'
  , Matchable(..)
  , splittingSF
  , matchingMF
  -- * 'Chain'
  , Chain(..)
  , foldChain
  , unfoldChain
  , unrollMF
  , rerollMF
  , unrollingMF
  , fromChain1
  -- ** Matchable
  , splittingChain1
  , splitChain1
  , matchingChain
  , unmatchChain
  ) where

import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Function
import           Data.Functor.Apply.Free
import           Data.Functor.Classes
import           Data.Functor.Day            (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Sum
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HFunctor
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
import           Data.HFunctor.IsoF
import           Data.Kind
import           Data.Proxy
import           GHC.Generics hiding         (C)
import qualified Data.Functor.Day            as D

-- | An 'Associative' 'HBifunctor' can be a 'Tensor' if there is some
-- identity @i@ where @t i f@ is equivalent to just @f@.
--
-- That is, "enhancing" @f@ with @t i@ does nothing.
--
-- The methods in this class provide us useful ways of navigating
-- a @'Tensor' t@ with respect to this property.
--
-- The 'Tensor' is essentially the 'HBifunctor' equivalent of 'Inject',
-- with 'intro1' and 'intro2' taking the place of 'inject'.
class Associative t => Tensor t where
    -- | The identity of @'Tensor' t@.  If you "combine" @f@ with the
    -- identity, it leaves @f@ unchanged.
    --
    -- For example, the identity of ':*:' is 'Proxy'.  This is because
    --
    -- @
    -- ('Proxy' :*: f) a
    -- @
    --
    -- is equivalent to just
    --
    -- @
    -- f a
    -- @
    --
    -- ':*:'-ing @f@ with 'Proxy' gives you no additional structure.
    --
    -- Another example:
    --
    -- @
    -- ('Void1' ':+:' f) a
    -- @
    --
    -- is equivalent to just
    --
    -- @
    -- f a
    -- @
    --
    -- because the 'L1' case is unconstructable.
    type I t :: Type -> Type

    -- | Because @t f (I t)@ is equivalent to @f@, we can always "insert"
    -- @f@ into @t f (I t)@.
    --
    -- This is analogous to 'inject' from 'Inject', but for 'HBifunctor's.
    intro1 :: f ~> t f (I t)

    -- | Because @t (I t) g@ is equivalent to @f@, we can always "insert"
    -- @g@ into @t (I t) g@.
    --
    -- This is analogous to 'inject' from 'Inject', but for 'HBifunctor's.
    intro2 :: g ~> t (I t) g

    -- | Witnesses the property that @'I' t@ is the identity of @t@: @t
    -- f (I t)@ always leaves @f@ unchanged, so we can always just drop the
    -- @'I' t@.
    elim1 :: Functor f => t f (I t) ~> f

    -- | Witnesses the property that @'I' t@ is the identity of @t@: @t
    -- (I t) g@ always leaves @g@ unchanged, so we can always just drop the
    -- @'I' t@.
    elim2 :: Functor g => t (I t) g ~> g

    {-# MINIMAL intro1, intro2, elim1, elim2 #-}

-- | @f@ is isomorphic to @t f ('I' t)@: that is, @'I' t@ is the identity
-- of @t@, and leaves @f@ unchanged.
rightIdentity :: (Tensor t, Functor f) => f <~> t f    (I t)
rightIdentity = isoF intro1 elim1

-- | @g@ is isomorphic to @t ('I' t) g@: that is, @'I' t@ is the identity
-- of @t@, and leaves @g@ unchanged.
leftIdentity  :: (Tensor t, Functor g) => g <~> t (I t) g
leftIdentity = isoF intro2 elim2

-- | 'leftIdentity' ('intro1' and 'elim1') for ':+:' actually does not
-- require 'Functor'.  This is the more general version.
voidLeftIdentity :: f <~> Void1 :+: f
voidLeftIdentity = isoF R1 (absurd1 !*! id)

-- | 'rightIdentity' ('intro2' and 'elim2') for ':+:' actually does not
-- require 'Functor'.  This is the more general version.
voidRightIdentity :: f <~> Void1 :+: f
voidRightIdentity = isoF R1 (absurd1 !*! id)

-- | A useful construction that works like a "linked list" of @t f@ applied
-- to itself multiple times.  That is, it contains @t f f@, @t f (t f f)@,
-- @t f (t f (t f f))@, etc, with @f@ occuring zero or more times.
--
-- If @t@ is 'Monoidal', then it means we can "collapse" this linked list
-- into some final type @'MF' t@ ('rerollMF'), and also extract it back
-- into a linked list ('unrollMF').
data Chain t i f a = Done (i a)
                   | More (t f (Chain t i f) a)

deriving instance (Eq (i a), Eq (t f (Chain t i f) a)) => Eq (Chain t i f a)
deriving instance (Ord (i a), Ord (t f (Chain t i f) a)) => Ord (Chain t i f a)
deriving instance (Show (i a), Show (t f (Chain t i f) a)) => Show (Chain t i f a)
deriving instance (Read (i a), Read (t f (Chain t i f) a)) => Read (Chain t i f a)
deriving instance (Functor i, Functor (t f (Chain t i f))) => Functor (Chain t i f)
deriving instance (Foldable i, Foldable (t f (Chain t i f))) => Foldable (Chain t i f)
deriving instance (Traversable i, Traversable (t f (Chain t i f))) => Traversable (Chain t i f)

instance (Eq1 i, Eq1 (t f (Chain t i f))) => Eq1 (Chain t i f) where
    liftEq eq = \case
      Done x -> \case
        Done y -> liftEq eq x y
        More _ -> False
      More x -> \case
        Done _ -> False
        More y -> liftEq eq x y

instance (Ord1 i, Ord1 (t f (Chain t i f))) => Ord1 (Chain t i f) where
    liftCompare c = \case
      Done x -> \case
        Done y -> liftCompare c x y
        More _ -> LT
      More x -> \case
        Done _ -> GT
        More y -> liftCompare c x y

instance (Show1 (t f (Chain t i f)), Show1 i) => Show1 (Chain t i f) where
    liftShowsPrec sp sl d = \case
        Done x  -> showsUnaryWith (liftShowsPrec sp sl) "Done" d x
        More xs -> showsUnaryWith (liftShowsPrec sp sl) "More" d xs

instance (Functor i, Read1 (t f (Chain t i f)), Read1 i) => Read1 (Chain t i f) where
    liftReadsPrec rp rl = readsData $
            readsUnaryWith (liftReadsPrec rp rl) "Done" Done
         <> readsUnaryWith (liftReadsPrec rp rl) "More" More

-- | Recursively fold down a 'Chain'.  Provide a function on how to handle
-- the "single @f@ case" ('nilMF'), and how to handle the "combined @t f g@
-- case", and this will fold the entire @'Chain' t i) f@ into a single @g@.
--
-- This is a catamorphism.
foldChain
    :: forall t i f g. HBifunctor t
    => (i ~> g)             -- ^ Handle 'Done'
    -> (t f g ~> g)         -- ^ Handle 'More'
    -> Chain t i f ~> g
foldChain f g = go
  where
    go :: Chain t i f ~> g
    go = \case
      Done x  -> f x
      More xs -> g (hright go xs)

-- | Recursively build up a 'Chain'.  Provide a function that takes some
-- starting seed @g@ and returns either "done" (@i@) or "continue further"
-- (@t f g@), and it will create a @'Chain' t i f@ from a @g@.
--
-- This is an anamorphism.
unfoldChain
    :: forall t f g i. HBifunctor t
    => (g ~> i :+: t f g)
    -> g ~> Chain t i f
unfoldChain f = go
  where
    go :: g ~> Chain t i f
    go = (Done !*! More . hright go) . f

instance HBifunctor t => HFunctor (Chain t i) where
    hmap f = foldChain Done (More . hleft f)

instance (Tensor t, i ~ I t) => Inject (Chain t i) where
    inject = More . hright Done . intro1

-- | We can collapse and interpret an @'Chain' t i@ if we have @'Tensor' t@.
instance (Monoidal t, i ~ I t) => Interpret (Chain t i) where
    type C (Chain t i) = AndC (C (SF t)) (C (MF t))
    retract = \case
      Done x  -> pureT @t x
      More xs -> binterpret id retract xs
    interpret
        :: forall f g. (C (SF t) g, C (MF t) g)
        => f ~> g
        -> Chain t i f ~> g
    interpret f = go
      where
        go :: Chain t i f ~> g
        go = \case
          Done x  -> pureT @t x
          More xs -> binterpret f go xs

-- | A 'Chain1' is "one or more linked @f@s", and a 'Chain' is "zero or
-- more linked @f@s".  So, we can convert from a 'Chain1' to a 'Chain' that
-- always has at least one @f@.
--
-- The result of this function always is made with 'More' at the top level.
fromChain1 :: Tensor t => Chain1 t f ~> Chain t (I t) f
fromChain1 = foldChain1 (More . hright Done . intro1) More

-- | A @'Monoidal' t@ is a 'Semigroupoidal', in that it provides some type
-- @'MF' t f@ that is equivalent to one of:
--
-- *  @I a@                             -- 0 times
-- *  @f a@                             -- 1 time
-- *  @t f f a@                         -- 2 times
-- *  @t f (t f f) a@                   -- 3 times
-- *  @t f (t f (t f f)) a@             -- 4 times
-- *  @t f (t f (t f (t f f))) a@       -- 5 times
-- *  .. etc
--
-- The difference is that unlike @'SF' t@, @'MF' t@ has the "zero times"
-- value.
--
-- This typeclass lets you use a type like 'ListF' in terms of repeated
-- applications of ':*:', or 'Ap' in terms of repeated applications of
-- 'Day', or 'Free' in terms of repeated applications of 'Comp', etc.
--
-- For example, @f ':*:' f@ can be interpreted as "a free selection of two
-- @f@s", allowing you to specify "I have to @f@s that I can use".  If you
-- want to specify "I want 0, 1, or many different @f@s that I can use",
-- you can use @'ListF' f@.
--
-- At the high level, the thing that 'Monoidal' adds to 'Semigroupoidal'
-- is 'inL', 'inR', and 'nilMF':
--
-- @
-- 'inL'    :: f a -> t f g a
-- 'inR'    :: g a -> t f g a
-- 'nilMF'  :: I a -> MF t f a
-- @
--
-- which are like the 'HBifunctor' versions of 'inject': it lets you inject
-- an @f@ into @t f g@, so you can start doing useful mixing operations
-- with it.  'nilMF' lets you construct an "empty" @'MF' t@.
--
-- Also useful is:
--
-- @
-- 'toMF' :: t f f a -> MF t f a
-- @
--
-- Which converts a @t@ into its aggregate type 'MF'
class (Tensor t, Semigroupoidal t, Interpret (MF t)) => Monoidal t where
    -- | The "monoidal functor combinator" generated by @t@.
    --
    -- A value of type @MF t f a@ is either:
    --
    -- *  @I a@                         -- zero fs
    -- *  @f a@                         -- one f
    -- *  @t f f a@                     -- two fs
    -- *  @t f (t f f) a@               -- three fs
    -- *  @t f (t f (t f f)) a@
    -- *  @t f (t f (t f (t f f))) a@
    -- *  .. etc
    --
    -- For example, for ':*:', we have 'ListF'.  This is because:
    --
    -- @
    -- Proxy         ~ ListF []
    -- x             ~ ListF [x]
    -- x :*: y       ~ ListF [x,y]
    -- x :*: y :*: z ~ ListF [x,y,z]
    -- -- etc.
    -- @
    --
    -- You can create an "empty" one with 'nilMF', a "singleton" one with
    -- 'inject', or else one from a single @t f f@ with 'toMF'.
    type MF t :: (Type -> Type) -> Type -> Type


    -- | If a @'MF' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'MF' t f@s applied to
    -- themselves into one giant @'MF' t f@ containing all of the @t f@s.
    appendMF    :: t (MF t f) (MF t f) ~> MF t f

    -- | Lets you convert an @'SF' t f@ into a single application of @f@ to
    -- @'MF' t f@.
    --
    -- Analogous to a function @'Data.List.NonEmpty.NonEmpty' a -> (a,
    -- [a])@
    --
    -- Note that this is not reversible in general unless we have
    -- @'Matchable' t@.
    splitSF     :: SF t f ~> t f (MF t f)

    -- | An @'MF' t f@ is either empty, or a single application of @t@ to @f@
    -- and @MF t f@ (the "head" and "tail").  This witnesses that
    -- isomorphism.
    --
    -- To /use/ this property, see 'nilMF', 'consMF', and 'unconsMF'.
    splittingMF :: MF t f <~> I t :+: t f (MF t f)

    -- | Embed a direct application of @f@ to itself into a @'MF' t f@.
    toMF   :: t f f ~> MF t f
    toMF   = reviewF (splittingMF @t)
           . R1
           . hright (inject @(MF t))

    -- | @'SF' t f@ is "one or more @f@s", and @'MF t f@ is "zero or more
    -- @f@s".  This function lets us convert from one to the other.
    --
    -- This is analogous to a function @'Data.List.NonEmpty.NonEmpty' a ->
    -- [a]@.
    fromSF :: SF t f ~> MF t f
    fromSF = reviewF (splittingMF @t) . R1 . splitSF @t

    -- | If we have an @'I' t@, we can generate an @f@ based on how it
    -- interacts with @t@.
    --
    -- Specialized (and simplified), this type is:
    --
    -- @
    -- 'pureT' \@'Day'   :: 'Applicative' f => a -> f a  -- 'pure'
    -- 'pureT' \@'Comp'  :: 'Monad' f => a -> f a    -- 'return'
    -- 'pureT' \@(':*:') :: 'Plus' f => f a          -- 'zero'
    -- @
    --
    -- Note that because @t@ appears nowhere in the input or output types,
    -- you must always use this with explicit type application syntax (like
    -- @pureT \@Day@)
    pureT  :: C (MF t) f => I t ~> f
    pureT  = retract . reviewF (splittingMF @t) . L1

    {-# MINIMAL appendMF, splitSF, splittingMF #-}

-- | Create the "empty 'MF'@.
--
-- If @'MF' t f@ represents multiple applications of @t f@ with
-- itself, then @nilMF@ gives us "zero applications of @f@".
--
-- Note that @t@ cannot be inferred from the input or output type of
-- 'nilMF', so this function must always be called with -XTypeApplications:
--
-- @
-- 'nilMF' \@'Day' :: 'Identity' '~>' 'Ap' f
-- 'nilMF' \@'Comp' :: 'Identity' '~>' 'Free' f
-- 'nilMF' \@(':*:') :: 'Proxy' '~>' 'ListF' f
-- @
nilMF    :: forall t f. Monoidal t => I t ~> MF t f
nilMF    = reviewF (splittingMF @t) . L1

-- | Lets us "cons" an application of @f@ to the front of an @'MF' t f@.
consMF   :: forall t f. Monoidal t => t f (MF t f) ~> MF t f
consMF   = reviewF (splittingMF @t) . R1

-- | "Pattern match" on an @'MF' t@
--
-- An @'MF' t f@ is either empty, or a single application of @t@ to @f@
-- and @MF t f@ (the "head" and "tail")
--
-- This is analogous to the function @'Data.List.uncons' :: [a] -> Maybe
-- (a, [a])@.
unconsMF :: forall t f. Monoidal t => MF t f ~> I t :+: t f (MF t f)
unconsMF = viewF splittingMF

-- | A type @'MF' t@ is supposed to represent the successive application of
-- @t@s to itself.  The type @'Chain' t ('I' t) f@ is an actual concrete
-- ADT that contains successive applications of @t@ to itself, and you can
-- pattern match on each layer.
--
-- 'unrollingMF' states that the two types are isormorphic.  Use 'unrollMF'
-- and 'rerollMF' to convert between the two.
unrollingMF :: forall t f. Monoidal t => MF t f <~> Chain t (I t) f
unrollingMF = isoF unrollMF rerollMF

-- | A type @'MF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unrollMF' makes that successive application explicit,
-- buy converting it to a literal 'Chain' of applications of @t@ to
-- itself.
unrollMF :: forall t f. Monoidal t => MF t f ~> Chain t (I t) f
unrollMF = unfoldChain (unconsMF @t)

-- | A type @'MF' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollSF' takes an explicit 'Chain' of applications of
-- @t@ to itself and rolls it back up into an @'MF' t@.
rerollMF :: forall t f. Monoidal t => Chain t (I t) f ~> MF t f
rerollMF = foldChain (nilMF @t) consMF

-- | Convenient wrapper over 'intro1' that lets us introduce an arbitrary
-- functor @g@ to the right of an @f@.
--
-- You can think of this as an 'HBifunctor' analogue of 'inject'.
inL
    :: forall t f g a. (Monoidal t, C (MF t) g)
    => f a
    -> t f g a
inL = hright (pureT @t) . intro1 @t

-- | Convenient wrapper over 'intro2' that lets us introduce an arbitrary
-- functor @f@ to the right of a @g@.
--
-- You can think of this as an 'HBifunctor' analogue of 'inject'.
inR
    :: forall t f g a. (Monoidal t, C (MF t) f)
    => g a
    -> t f g a
inR = hleft (pureT @t) . intro2 @t

-- | For some @t@, we have the ability to "statically analyze" the @'MF' t@
-- and pattern match and manipulate the structure without ever
-- interpreting or retracting.  These are 'Matchable'.
class Monoidal t => Matchable t where
    -- | The inverse of 'splitSF'.  A consing of @f@ to @'MF' t f@ is
    -- non-empty, so it can be represented as an @'SF' t f@.
    --
    -- This is analogous to a function @'uncurry' ('Data.List.NonEmpty.:|')
    -- :: (a, [a]) -> 'Data.List.NonEmpty.NonEmpty' a@.
    unsplitSF :: t f (MF t f) ~> SF t f

    -- | "Pattern match" on an @'MF' t f@: it is either empty, or it is
    -- non-empty (and so can be an @'SF' t f@).
    --
    -- This is analgous to a function @'Data.List.NonEmpty.nonEmpty' :: [a]
    -- -> Maybe ('Data.List.NonEmpty.NonEmpty' a)@.
    matchMF   :: MF t f ~> I t :+: SF t f

-- | An @'SF' t f@ is isomorphic to an @f@ consed with an @'MF' t f@, like
-- how a @'Data.List.NonEmpty.NonEmpty' a@ is isomorphic to @(a, [a])@.
splittingSF :: Matchable t => SF t f <~> t f (MF t f)
splittingSF = isoF splitSF unsplitSF

-- | An @'MF' t f@ is isomorphic to either the empty case (@'I' t@) or the
-- non-empty case (@'SF' t f@), like how @[a]@ is isomorphic to @'Maybe'
-- ('Data.List.NonEmpty.NonEmpty' a)@.
matchingMF :: forall t f. Matchable t => MF t f <~> I t :+: SF t f
matchingMF = isoF (matchMF @t) (unmatchMF @t)

unmatchMF :: forall t f. Monoidal t => I t :+: SF t f ~> MF t f
unmatchMF = nilMF @t !*! fromSF @t

-- | A @'Chain1' t f@ is like a non-empty linked list of @f@s, and
-- a @'Chain' t ('I' t) f@ is a possibly-empty linked list of @f@s.  This
-- witnesses the fact that the former is isomorphic to @f@ consed to the
-- latter.
splittingChain1
    :: forall t f. (Matchable t, Functor f)
    => Chain1 t f <~> t f (Chain t (I t) f)
splittingChain1 = fromF unrollingSF
                . splittingSF @t
                . overHBifunctor id unrollingMF

-- | The "forward" function representing 'splittingChain1'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
splitChain1
    :: forall t f. Matchable t
    => Chain1 t f ~> t f (Chain t (I t) f)
splitChain1 = hright (unrollMF @t) . splitSF @t . rerollSF

-- | A @'Chain' t ('I' t) f@ is a linked list of @f@s, and a @'Chain1' t f@ is
-- a non-empty linked list of @f@s.  This witnesses the fact that
-- a @'Chain' t (I t) f@ is either empty (@'I' t@) or non-empty (@'Chain1'
-- t f@).
matchingChain
    :: forall t f. (Matchable t, Functor f)
    => Chain t (I t) f <~> I t :+: Chain1 t f
matchingChain = fromF unrollingMF
              . matchingMF @t
              . overHBifunctor id unrollingSF

-- | The "reverse" function representing 'matchingChain'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
unmatchChain
    :: forall t f. Matchable t
    => I t :+: Chain1 t f ~> Chain t (I t) f
unmatchChain = unrollMF @t . unmatchMF @t . hright (rerollSF @t)

instance Tensor (:*:) where
    type I (:*:) = Proxy

    intro1 = (:*: Proxy)
    intro2 = (Proxy :*:)

    elim1 (x      :*: ~Proxy) = x
    elim2 (~Proxy :*: y     ) = y

instance Tensor Product where
    type I Product = Proxy

    intro1 = (`Pair` Proxy)
    intro2 = (Proxy `Pair`)

    elim1 (Pair x ~Proxy) = x
    elim2 (Pair ~Proxy y) = y

instance Tensor Day where
    type I Day = Identity

    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1

instance Tensor (:+:) where
    type I (:+:) = Void1

    intro1 = L1
    intro2 = R1

    elim1 = \case
      L1 x -> x
      R1 y -> absurd1 y
    elim2 = \case
      L1 x -> absurd1 x
      R1 y -> y

instance Tensor Sum where
    type I Sum = Void1

    intro1 = InL
    intro2 = InR

    elim1 = \case
      InL x -> x
      InR y -> absurd1 y
    elim2 = \case
      InL x -> absurd1 x
      InR y -> y

instance Tensor Comp where
    type I Comp = Identity

    intro1 = (:>>= Identity)
    intro2 = (Identity () :>>=) . const

    elim1 (x :>>= y) = runIdentity . y <$> x
    elim2 (x :>>= y) = y (runIdentity x)

instance Monoidal Comp where
    type MF Comp = Free

    appendMF (x :>>= y) = x >>= y
    splitSF             = free1Comp
    splittingMF = isoF to_ from_
      where
        to_ :: Free f ~> Identity :+: Comp f (Free f)
        to_ = foldFree' (L1 . Identity) $ \y n -> R1 $
            y :>>= (from_ . n)
        from_ :: Identity :+: Comp f (Free f) ~> Free f
        from_ = pure . runIdentity
            !*! (\case x :>>= f -> liftFree x >>= f)

    toMF (x :>>= y) = liftFree x >>= (inject . y)
    pureT           = pure . runIdentity

instance Monoidal (:*:) where
    type MF (:*:) = ListF

    appendMF (ListF xs :*: ListF ys) = ListF (xs ++ ys)
    splitSF     = nonEmptyProd
    splittingMF = isoF to_ from_
      where
        to_ = \case
          ListF []     -> L1 Proxy
          ListF (x:xs) -> R1 (x :*: ListF xs)
        from_ = \case
          L1 ~Proxy           -> ListF []
          R1 (x :*: ListF xs) -> ListF (x:xs)

    toMF (x :*: y) = ListF [x, y]
    pureT _        = zero

instance Monoidal Product where
    type MF Product = ListF

    appendMF (ListF xs `Pair` ListF ys) = ListF (xs ++ ys)
    splitSF     = viewF prodProd . nonEmptyProd
    splittingMF = isoF to_ from_
      where
        to_ = \case
          ListF []     -> L1 Proxy
          ListF (x:xs) -> R1 (x `Pair` ListF xs)
        from_ = \case
          L1 ~Proxy              -> ListF []
          R1 (x `Pair` ListF xs) -> ListF (x:xs)

    toMF (Pair x y) = ListF [x, y]
    pureT _         = zero

instance Monoidal Day where
    type MF Day = Ap

    appendMF (Day x y z) = z <$> x <*> y
    splitSF     = ap1Day
    splittingMF = isoF to_ from_
      where
        to_ = \case
          Pure x  -> L1 (Identity x)
          Ap x xs -> R1 (Day x xs (&))
        from_ = \case
          L1 (Identity x) -> Pure x
          R1 (Day x xs f) -> Ap x (flip f <$> xs)

    toMF (Day x y z) = z <$> liftAp x <*> liftAp y
    pureT            = pure . runIdentity

instance Monoidal (:+:) where
    type MF (:+:) = Step

    appendMF    = appendSF
    splitSF     = stepDown
    splittingMF = stepping . voidLeftIdentity

    toMF  = toSF
    pureT = absurd1

instance Monoidal Sum where
    type MF Sum = Step

    appendMF    = appendSF
    splitSF     = viewF sumSum . stepDown
    splittingMF = stepping . voidLeftIdentity . overHBifunctor id sumSum

    toMF  = toSF
    pureT = absurd1

instance Matchable (:*:) where
    unsplitSF = ProdNonEmpty
    matchMF   = fromListF

instance Matchable Product where
    unsplitSF = ProdNonEmpty . reviewF prodProd
    matchMF   = fromListF

instance Matchable Day where
    unsplitSF = DayAp1
    matchMF   = fromAp

instance Matchable (:+:) where
    unsplitSF   = stepUp
    matchMF     = R1

instance Matchable Sum where
    unsplitSF   = stepUp . reviewF sumSum
    matchMF     = R1
