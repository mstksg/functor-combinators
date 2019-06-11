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
  , sumLeftIdentity
  , sumRightIdentity
  , prodLeftIdentity
  , prodRightIdentity
  -- * 'Monoidal'
  , Monoidal(..)
  , CM
  , nilMF
  , consMF
  , unconsMF
  -- ** Utility
  , inL
  , inR
  , outL
  , outR
  , biretractT
  , binterpretT
  , prodOutL
  , prodOutR
  -- ** Unsafe
  , unsafePlus
  , unsafeApply
  , unsafeBind
  -- * 'Matchable'
  , Matchable(..)
  , splittingSF
  , matchingMF
  ) where

import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Function
import           Data.Functor.Apply.Free
import           Data.Functor.Day            (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HFunctor
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
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
    -- ('V1' ':+:' f) a
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
sumLeftIdentity :: f <~> V1 :+: f
sumLeftIdentity = isoF R1 (absurd1 !*! id)

-- | 'rightIdentity' ('intro2' and 'elim2') for ':+:' actually does not
-- require 'Functor'.  This is the more general version.
sumRightIdentity :: f <~> f :+: V1
sumRightIdentity = isoF L1 (id !*! absurd1)

-- | 'leftIdentity' ('intro1' and 'elim1') for ':*:' actually does not
-- require 'Functor'.  This is the more general version.
prodLeftIdentity :: f <~> Proxy :*: f
prodLeftIdentity = isoF (Proxy :*:) (\case _ :*: y -> y)

-- | 'rightIdentity' ('intro2' and 'elim2') for ':*:' actually does not
-- require 'Functor'.  This is the more general version.
prodRightIdentity :: g <~> g :*: Proxy
prodRightIdentity = isoF (:*: Proxy) (\case x :*: _ -> x)

-- | 'outL' for ':*:' actually does not require 'Functor'.  This is the
-- more general version.
prodOutL :: f :*: g ~> f
prodOutL (x :*: _) = x

-- | 'outR' for ':*:' actually does not require 'Functor'.  This is the
-- more general version.
prodOutR :: f :*: g ~> g
prodOutR (_ :*: y) = y

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
    -- | The "monoidal functor combinator" induced by @t@.
    --
    -- A value of type @MF t f a@ is /equivalent/ to one of:
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
    -- 'Proxy'         ~ 'ListF' []         ~ 'nilMF' \@(':*:')
    -- x             ~ ListF [x]        ~ 'inject' x
    -- x :*: y       ~ ListF [x,y]      ~ 'toMF' (x :*: y)
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
    --
    -- Note that because @t@ is not inferrable from the input or output
    -- type, you should call this using /-XTypeApplications/:
    --
    -- @
    -- 'fromSF' \@(':*:') :: 'NonEmptyF' f a -> 'ListF' f a
    -- fromSF \@'Comp'  :: 'Free1' f a -> 'Free' f a
    -- @
    fromSF :: SF t f ~> MF t f
    fromSF = reviewF (splittingMF @t) . R1 . splitSF @t

    -- | If we have an @'I' t@, we can generate an @f@ based on how it
    -- interacts with @t@.
    --
    -- Specialized (and simplified), this type is:
    --
    -- @
    -- 'pureT' \@'Day'   :: 'Applicative' f => 'Identity' a -> f a  -- 'pure'
    -- pureT \@'Comp'  :: 'Monad' f => Identity a -> f a        -- 'return'
    -- pureT \@(':*:') :: 'Plus' f => 'Proxy' a -> f a            -- 'zero'
    -- @
    --
    -- Note that because @t@ appears nowhere in the input or output types,
    -- you must always use this with explicit type application syntax (like
    -- @pureT \@Day@)
    pureT  :: CM t f => I t ~> f
    pureT  = retract . reviewF (splittingMF @t) . L1

    -- | If we have a constraint on the 'Monoidal' satisfied, it should
    -- also imply the constraint on the 'Semigroupoidal'.
    --
    -- This is basically saying that @'C' ('SF' t)@ should be a superclass
    -- of @'C' ('MF' t)@.
    --
    -- For example, for ':*:', this type signature says that 'Alt' is
    -- a superclass of 'Plus', so whenever you have 'Plus', you should
    -- always also have 'Alt'.
    --
    -- For 'Day', this type signature says that 'Apply' is a superclass of
    -- 'Applicative', so whenever you have 'Applicative', you should always
    -- also have 'Apply'.
    --
    -- This is necessary because in the current class hierarchy, 'Apply'
    -- isn't a true superclass of 'Applicative'.  'upgradeC' basically
    -- "imbues" @f@ with an 'Apply' instance based on its 'Applicative'
    -- instance, so things can be easier to use.
    --
    -- For example, let's say I have a type @Parser@ that is an
    -- 'Applicative' instance, but the source library does not define an
    -- 'Apply' instance.  I cannot use 'biretract' or 'binterpret' with it,
    -- even though I should be able to, because they require 'Apply'.
    --
    -- That is:
    --
    -- @
    -- 'biretract' :: 'Day' Parser Parser a -> Parser a
    -- @
    --
    -- is a type error, because it requires @'Apply' Parser@.
    --
    -- But, if we know that @Parser@ has an 'Applicative' instance, we can
    -- use:
    --
    -- @
    -- 'upgradeC' @'Day' ('Proxy' \@Parser) 'biretract'
    --   :: Day Parser Parser a -> a
    -- @
    --
    -- and this will now typecheck properly.
    --
    -- Ideally, @Parser@ would also have an 'Apply' instance.  But we
    -- cannot control this if an external library defines @Parser@.
    --
    -- (Alternatively you can just use 'biretractT'.)
    --
    -- Note that you should only use this if @f@ doesn't already have the
    -- 'SF' constraint.  If it does, this could lead to conflicting
    -- instances.  Only use this with /specific/, concrete @f@s.  Otherwise
    -- this is unsafe and can possibly break coherence guarantees.
    --
    -- The @proxy@ argument can be provided using something like @'Proxy'
    -- \@f@, to specify which @f@ you want to upgrade.
    upgradeC :: CM t f => proxy f -> (CS t f => r) -> r

    {-# MINIMAL appendMF, splitSF, splittingMF, upgradeC #-}

-- | Convenient alias for the constraint required for 'inL', 'inR',
-- 'pureT', etc.
--
-- It's usually a constraint on the target/result context of interpretation
-- that allows you to "exit" or "run" a @'Monoidal' t@.
type CM t = C (MF t)

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
-- nilMF \@'Comp' :: Identity ~> 'Free' f
-- nilMF \@(':*:') :: 'Proxy' ~> 'ListF' f
-- @
nilMF    :: forall t f. Monoidal t => I t ~> MF t f
nilMF    = reviewF (splittingMF @t) . L1

-- | Lets us "cons" an application of @f@ to the front of an @'MF' t f@.
consMF   :: Monoidal t => t f (MF t f) ~> MF t f
consMF   = reviewF splittingMF . R1

-- | "Pattern match" on an @'MF' t@
--
-- An @'MF' t f@ is either empty, or a single application of @t@ to @f@
-- and @MF t f@ (the "head" and "tail")
--
-- This is analogous to the function @'Data.List.uncons' :: [a] -> Maybe
-- (a, [a])@.
unconsMF :: Monoidal t => MF t f ~> I t :+: t f (MF t f)
unconsMF = viewF splittingMF

-- | Convenient wrapper over 'intro1' that lets us introduce an arbitrary
-- functor @g@ to the right of an @f@.
--
-- You can think of this as an 'HBifunctor' analogue of 'inject'.
inL
    :: forall t f g. (Monoidal t, CM t g)
    => f ~> t f g
inL = hright (pureT @t) . intro1

-- | Convenient wrapper over 'intro2' that lets us introduce an arbitrary
-- functor @f@ to the right of a @g@.
--
-- You can think of this as an 'HBifunctor' analogue of 'inject'.
inR
    :: forall t f g. (Monoidal t, CM t f)
    => g ~> t f g
inR = hleft (pureT @t) . intro2

-- | Convenient wrapper over 'elim1' that lets us drop one of the arguments
-- of a 'Tensor' for free, without requiring any extra constraints (like
-- for 'binterpret').
--
-- See 'prodOutL' for a version that does not require @'Functor' f@,
-- specifically for ':*:'.
outL
    :: (Tensor t, I t ~ Proxy, Functor f)
    => t f g ~> f
outL = elim1 . hright absorb

-- | Convenient wrapper over 'elim2' that lets us drop one of the arguments
-- of a 'Tensor' for free, without requiring any constraints (like for
-- 'binterpret').
--
-- See 'prodOutR' for a version that does not require @'Functor' g@,
-- specifically for ':*:'.
outR
    :: (Tensor t, I t ~ Proxy, Functor g)
    => t f g ~> g
outR = elim2 . hleft absorb

-- | This is 'biretract', but taking a @'C' ('MF' t)@ constraint instead of
-- a @'C' ('SF' t)@ constraint.  For example, for 'Day', it takes an
-- 'Applicative' constraint instead of an 'Apply' constraint.
--
-- In an ideal world, this would be not necessary, and we can use
-- 'biretract'.  However, sometimes @'C' ('MF' t)@ is not an actual
-- subclass of @'C' ('SF' t)@ (like 'Apply' and 'Applicative'), even though
-- it should technically always be so.
--
-- Note that you should only use this if @f@ doesn't already have the 'SF'
-- constraint (for example, for 'Day', if @f@ already has an 'Apply'
-- instance).  If it does, this could lead to conflicting instances.  If
-- @f@ already has the 'SF' instance, just use 'biretract' directly.  Only
-- use this with /specific/, concrete @f@s.
biretractT :: forall t f. (Monoidal t, CM t f) => t f f ~> f
biretractT = upgradeC @t (Proxy @f)
               biretract

-- | This is 'binterpret', but taking a @'C' ('MF' t)@ constraint instead of
-- a @'C' ('SF' t)@ constraint.  For example, for 'Day', it takes an
-- 'Applicative' constraint instead of an 'Apply' constraint.
--
-- In an ideal world, this would be not necessary, and we can use
-- 'biretract'.  However, sometimes @'C' ('MF' t)@ is not an actual
-- subclass of @'C' ('SF' t)@ (like 'Apply' and 'Applicative'), even though
-- it should technically always be so.
--
-- Note that you should only use this if @f@ doesn't already have the 'SF'
-- constraint (for example, for 'Day', if @f@ already has an 'Apply'
-- instance).  If it does, this could lead to conflicting instances.  If
-- @f@ already has the 'SF' instance, just use 'biretract' directly.  Only
-- use this with /specific/, concrete @f@s.
binterpretT
    :: forall t f g h. (Monoidal t, CM t h)
    => f ~> h
    -> g ~> h
    -> t f g ~> h
binterpretT f g = upgradeC @t (Proxy @h) $
                    binterpret f g

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
    --
    -- Note that because @t@ cannot be inferred from the input or output
    -- type, you should use this with /-XTypeApplications/:
    --
    -- @
    -- 'matchMF' \@'Day' :: 'Ap' f a -> ('Identity' :+: 'Ap1' f) a
    -- @
    matchMF   :: MF t f ~> I t :+: SF t f

-- | An @'SF' t f@ is isomorphic to an @f@ consed with an @'MF' t f@, like
-- how a @'Data.List.NonEmpty.NonEmpty' a@ is isomorphic to @(a, [a])@.
splittingSF :: Matchable t => SF t f <~> t f (MF t f)
splittingSF = isoF splitSF unsplitSF

-- | An @'MF' t f@ is isomorphic to either the empty case (@'I' t@) or the
-- non-empty case (@'SF' t f@), like how @[a]@ is isomorphic to @'Maybe'
-- ('Data.List.NonEmpty.NonEmpty' a)@.
matchingMF :: forall t f. Matchable t => MF t f <~> I t :+: SF t f
matchingMF = isoF (matchMF @t) (nilMF @t !*! fromSF @t)

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
    type I (:+:) = V1

    intro1 = L1
    intro2 = R1

    elim1 = \case
      L1 x -> x
      R1 y -> absurd1 y
    elim2 = \case
      L1 x -> absurd1 x
      R1 y -> y

instance Tensor Sum where
    type I Sum = V1

    intro1 = InL
    intro2 = InR

    elim1 = \case
      InL x -> x
      InR y -> absurd1 y
    elim2 = \case
      InL x -> absurd1 x
      InR y -> y

instance Tensor These1 where
    type I These1 = V1

    intro1 = This1
    intro2 = That1
    elim1  = \case
      This1  x   -> x
      That1    y -> absurd1 y
      These1 _ y -> absurd1 y
    elim2 = \case
      This1  x   -> absurd1 x
      That1    y -> y
      These1 x _ -> absurd1 x

instance Tensor Comp where
    type I Comp = Identity

    intro1 = (:>>= Identity)
    intro2 = (Identity () :>>=) . const

    elim1 (x :>>= y) = runIdentity . y <$> x
    elim2 (x :>>= y) = y (runIdentity x)

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

    upgradeC _ x = x

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

    upgradeC _ x = x

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
    pureT            = generalize

    upgradeC = unsafeApply

instance Monoidal (:+:) where
    type MF (:+:) = Step

    appendMF    = appendSF
    splitSF     = stepDown
    splittingMF = stepping . sumLeftIdentity

    toMF  = toSF
    pureT = absurd1

    upgradeC _ x = x

instance Monoidal Sum where
    type MF Sum = Step

    appendMF    = appendSF
    splitSF     = viewF sumSum . stepDown
    splittingMF = stepping . sumLeftIdentity . overHBifunctor id sumSum

    toMF  = toSF
    pureT = absurd1

    upgradeC _ x = x

instance Monoidal These1 where
    type MF These1 = Steps

    appendMF    = appendSF
    splitSF     = stepsDown
    splittingMF = steppings . sumLeftIdentity

    toMF  = toSF
    pureT = absurd1

    upgradeC _ x = x

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
        from_ = generalize
            !*! (\case x :>>= f -> liftFree x >>= f)

    toMF (x :>>= y) = liftFree x >>= (inject . y)
    pureT           = generalize

    upgradeC = unsafeBind

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

instance Matchable These1 where
    unsplitSF = stepsUp
    matchMF   = R1
