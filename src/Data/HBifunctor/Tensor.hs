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
-- 'toLB' :: (f ':*:' f) a -> 'ListF' f a
-- 'toLB' :: 'Comp' f f a -> 'Free' f a
-- 'toLB' :: 'Day' f f a -> 'Ap' f a
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
  , MonoidIn(..)
  , nilLB
  , consLB
  , unconsLB
  -- ** Utility
  , inL
  , inR
  , outL
  , outR
  -- , biretractT
  -- , binterpretT
  , prodOutL
  , prodOutR
  -- * 'Matchable'
  , Matchable(..)
  , splittingNEB
  , matchingLB
  ) where

import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Function
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
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
import           Data.List.NonEmpty          (NonEmpty(..))
import           Data.Proxy
import           GHC.Generics hiding         (C)
import qualified Data.Functor.Day            as D
import qualified Data.Map.NonEmpty           as NEM

-- | An 'Associative' 'HBifunctor' can be a 'Tensor' if there is some
-- identity @i@ where @t i f@ and @t f i@ are equivalent to just @f@.
--
-- That is, "enhancing" @f@ with @t i@ does nothing.
--
-- The methods in this class provide us useful ways of navigating
-- a @'Tensor' t@ with respect to this property.
--
-- The 'Tensor' is essentially the 'HBifunctor' equivalent of 'Inject',
-- with 'intro1' and 'intro2' taking the place of 'inject'.
class (Associative t, Inject (ListBy t)) => Tensor t i | t -> i where
    -- | The "monoidal functor combinator" induced by @t@.
    --
    -- A value of type @ListBy t f a@ is /equivalent/ to one of:
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
    -- 'Proxy'         ~ 'ListF' []         ~ 'nilLB' \@(':*:')
    -- x             ~ ListF [x]        ~ 'inject' x
    -- x :*: y       ~ ListF [x,y]      ~ 'toLB' (x :*: y)
    -- x :*: y :*: z ~ ListF [x,y,z]
    -- -- etc.
    -- @
    --
    -- You can create an "empty" one with 'nilLB', a "singleton" one with
    -- 'inject', or else one from a single @t f f@ with 'toLB'.
    type ListBy t :: (Type -> Type) -> Type -> Type

    -- | Because @t f (I t)@ is equivalent to @f@, we can always "insert"
    -- @f@ into @t f (I t)@.
    --
    -- This is analogous to 'inject' from 'Inject', but for 'HBifunctor's.
    intro1 :: f ~> t f i

    -- | Because @t (I t) g@ is equivalent to @f@, we can always "insert"
    -- @g@ into @t (I t) g@.
    --
    -- This is analogous to 'inject' from 'Inject', but for 'HBifunctor's.
    intro2 :: g ~> t i g

    -- | Witnesses the property that @'I' t@ is the identity of @t@: @t
    -- f (I t)@ always leaves @f@ unchanged, so we can always just drop the
    -- @'I' t@.
    elim1 :: Functor f => t f i ~> f

    -- | Witnesses the property that @'I' t@ is the identity of @t@: @t
    -- (I t) g@ always leaves @g@ unchanged, so we can always just drop the
    -- @'I' t@.
    elim2 :: Functor g => t i g ~> g

    -- | If a @'ListBy' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'ListBy' t f@s applied to
    -- themselves into one giant @'ListBy' t f@ containing all of the @t f@s.
    appendLB    :: t (ListBy t f) (ListBy t f) ~> ListBy t f

    -- | Lets you convert an @'NonEmptyBy' t f@ into a single application of @f@ to
    -- @'ListBy' t f@.
    --
    -- Analogous to a function @'Data.List.NonEmpty.NonEmpty' a -> (a,
    -- [a])@
    --
    -- Note that this is not reversible in general unless we have
    -- @'Matchable' t@.
    splitNEB     :: NonEmptyBy t f ~> t f (ListBy t f)

    -- | An @'ListBy' t f@ is either empty, or a single application of @t@ to @f@
    -- and @ListBy t f@ (the "head" and "tail").  This witnesses that
    -- isomorphism.
    --
    -- To /use/ this property, see 'nilLB', 'consLB', and 'unconsLB'.
    splittingLB :: ListBy t f <~> i :+: t f (ListBy t f)

    -- | Embed a direct application of @f@ to itself into a @'ListBy' t f@.
    toLB   :: t f f ~> ListBy t f
    toLB   = reviewF (splittingLB @t)
           . R1
           . hright (inject @(ListBy t))

    -- | @'NonEmptyBy' t f@ is "one or more @f@s", and @'ListBy t f@ is "zero or more
    -- @f@s".  This function lets us convert from one to the other.
    --
    -- This is analogous to a function @'Data.List.NonEmpty.NonEmpty' a ->
    -- [a]@.
    --
    -- Note that because @t@ is not inferrable from the input or output
    -- type, you should call this using /-XTypeApplications/:
    --
    -- @
    -- 'fromNEB' \@(':*:') :: 'NonEmptyF' f a -> 'ListF' f a
    -- fromNEB \@'Comp'  :: 'Free1' f a -> 'Free' f a
    -- @
    fromNEB :: NonEmptyBy t f ~> ListBy t f
    fromNEB = reviewF (splittingLB @t) . R1 . splitNEB @t


--    -- | If we have a constraint on the 'Monoidal' satisfied, it should
--    -- also imply the constraint on the 'Semigroupoidal'.
--    --
--    -- This is basically saying that @'C' ('NonEmptyBy' t)@ should be a superclass
--    -- of @'C' ('ListBy' t)@.
--    --
--    -- For example, for ':*:', this type signature says that 'Alt' is
--    -- a superclass of 'Plus', so whenever you have 'Plus', you should
--    -- always also have 'Alt'.
--    --
--    -- For 'Day', this type signature says that 'Apply' is a superclass of
--    -- 'Applicative', so whenever you have 'Applicative', you should always
--    -- also have 'Apply'.
--    --
--    -- This is necessary because in the current class hierarchy, 'Apply'
--    -- isn't a true superclass of 'Applicative'.  'upgradeC' basically
--    -- "imbues" @f@ with an 'Apply' instance based on its 'Applicative'
--    -- instance, so things can be easier to use.
--    --
--    -- For example, let's say I have a type @Parser@ that is an
--    -- 'Applicative' instance, but the source library does not define an
--    -- 'Apply' instance.  I cannot use 'biretract' or 'binterpret' with it,
--    -- even though I should be able to, because they require 'Apply'.
--    --
--    -- That is:
--    --
--    -- @
--    -- 'biretract' :: 'Day' Parser Parser a -> Parser a
--    -- @
--    --
--    -- is a type error, because it requires @'Apply' Parser@.
--    --
--    -- But, if we know that @Parser@ has an 'Applicative' instance, we can
--    -- use:
--    --
--    -- @
--    -- 'upgradeC' @'Day' ('Proxy' \@Parser) 'biretract'
--    --   :: Day Parser Parser a -> a
--    -- @
--    --
--    -- and this will now typecheck properly.
--    --
--    -- Ideally, @Parser@ would also have an 'Apply' instance.  But we
--    -- cannot control this if an external library defines @Parser@.
--    --
--    -- (Alternatively you can just use 'biretractT'.)
--    --
--    -- Note that you should only use this if @f@ doesn't already have the
--    -- 'SF' constraint.  If it does, this could lead to conflicting
--    -- instances.  Only use this with /specific/, concrete @f@s.  Otherwise
--    -- this is unsafe and can possibly break coherence guarantees.
--    --
--    -- The @proxy@ argument can be provided using something like @'Proxy'
--    -- \@f@, to specify which @f@ you want to upgrade.
--    upgradeC :: CM t f => proxy f -> (CS t f => r) -> r

    -- upgradeC :: CM t f => proxy f -> (CS t f => r) -> r
    -- {-# MINIMAL intro1, intro2, elim1, elim2, appendLB, splitNEB, splittingLB, upgradeC #-}

    {-# MINIMAL intro1, intro2, elim1, elim2, appendLB, splitNEB, splittingLB #-}

-- | @f@ is isomorphic to @t f i@: that is, @i@ is the identity of @t@, and
-- leaves @f@ unchanged.
rightIdentity :: (Tensor t i, Functor f) => f <~> t f i
rightIdentity = isoF intro1 elim1

-- | @g@ is isomorphic to @t i g@: that is, @i@ is the identity of @t@, and
-- leaves @g@ unchanged.
leftIdentity  :: (Tensor t i, Functor g) => g <~> t i g
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

class (Tensor t i, SemigroupIn t f, Interpret (ListBy t) f) => MonoidIn t i f where

    -- | If we have an @i@, we can generate an @f@ based on how it
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
    --
    -- Along with 'biretract', this function makes @f@ a monoid in the
    -- category of endofunctors with respect to tensor @t@.
    pureT  :: i ~> f
    pureT  = retract . reviewF (splittingLB @t) . L1

---- | A @'Monoidal' t@ is a 'Semigroupoidal', in that it provides some type
---- @'ListBy' t f@ that is equivalent to one of:
----
---- *  @I a@                             -- 0 times
---- *  @f a@                             -- 1 time
---- *  @t f f a@                         -- 2 times
---- *  @t f (t f f) a@                   -- 3 times
---- *  @t f (t f (t f f)) a@             -- 4 times
---- *  @t f (t f (t f (t f f))) a@       -- 5 times
---- *  .. etc
----
---- The difference is that unlike @'NonEmptyBy' t@, @'ListBy' t@ has the "zero times"
---- value.
----
---- This typeclass lets you use a type like 'ListF' in terms of repeated
---- applications of ':*:', or 'Ap' in terms of repeated applications of
---- 'Day', or 'Free' in terms of repeated applications of 'Comp', etc.
----
---- For example, @f ':*:' f@ can be interpreted as "a free selection of two
---- @f@s", allowing you to specify "I have to @f@s that I can use".  If you
---- want to specify "I want 0, 1, or many different @f@s that I can use",
---- you can use @'ListF' f@.
----
---- At the high level, the thing that 'Monoidal' adds to 'Semigroupoidal'
---- is 'inL', 'inR', and 'nilLB':
----
---- @
---- 'inL'    :: f a -> t f g a
---- 'inR'    :: g a -> t f g a
---- 'nilLB'  :: I a -> ListBy t f a
---- @
----
---- which are like the 'HBifunctor' versions of 'inject': it lets you inject
---- an @f@ into @t f g@, so you can start doing useful mixing operations
---- with it.  'nilLB' lets you construct an "empty" @'ListBy' t@.
----
---- Also useful is:
----
---- @
---- 'toLB' :: t f f a -> ListBy t f a
---- @
----
---- Which converts a @t@ into its aggregate type 'ListBy'
--class (Tensor t, Semigroupoidal t, Interpret (ListBy t)) => Monoidal t where

-- | Create the "empty 'ListBy'".
--
-- If @'ListBy' t f@ represents multiple applications of @t f@ with
-- itself, then @nilLB@ gives us "zero applications of @f@".
--
-- Note that @t@ cannot be inferred from the input or output type of
-- 'nilLB', so this function must always be called with -XTypeApplications:
--
-- @
-- 'nilLB' \@'Day' :: 'Identity' '~>' 'Ap' f
-- nilLB \@'Comp' :: Identity ~> 'Free' f
-- nilLB \@(':*:') :: 'Proxy' ~> 'ListF' f
-- @
nilLB    :: forall t i f. MonoidIn t i f => i ~> ListBy t f
nilLB    = reviewF (splittingLB @t) . L1

-- | Lets us "cons" an application of @f@ to the front of an @'ListBy' t f@.
consLB   :: MonoidIn t i f => t f (ListBy t f) ~> ListBy t f
consLB   = reviewF splittingLB . R1

-- | "Pattern match" on an @'ListBy' t@
--
-- An @'ListBy' t f@ is either empty, or a single application of @t@ to @f@
-- and @ListBy t f@ (the "head" and "tail")
--
-- This is analogous to the function @'Data.List.uncons' :: [a] -> Maybe
-- (a, [a])@.
unconsLB :: Tensor t i => ListBy t f ~> i :+: t f (ListBy t f)
unconsLB = viewF splittingLB

-- | Convenient wrapper over 'intro1' that lets us introduce an arbitrary
-- functor @g@ to the right of an @f@.
--
-- You can think of this as an 'HBifunctor' analogue of 'inject'.
inL
    :: forall t i f g. MonoidIn t i g
    => f ~> t f g
inL = hright (pureT @t) . intro1

-- | Convenient wrapper over 'intro2' that lets us introduce an arbitrary
-- functor @f@ to the right of a @g@.
--
-- You can think of this as an 'HBifunctor' analogue of 'inject'.
inR
    :: forall t i f g. MonoidIn t i f
    => g ~> t f g
inR = hleft (pureT @t) . intro2

-- | Convenient wrapper over 'elim1' that lets us drop one of the arguments
-- of a 'Tensor' for free, without requiring any extra constraints (like
-- for 'binterpret').
--
-- See 'prodOutL' for a version that does not require @'Functor' f@,
-- specifically for ':*:'.
outL
    :: (Tensor t Proxy, Functor f)
    => t f g ~> f
outL = elim1 . hright absorb

-- | Convenient wrapper over 'elim2' that lets us drop one of the arguments
-- of a 'Tensor' for free, without requiring any constraints (like for
-- 'binterpret').
--
-- See 'prodOutR' for a version that does not require @'Functor' g@,
-- specifically for ':*:'.
outR
    :: (Tensor t Proxy, Functor g)
    => t f g ~> g
outR = elim2 . hleft absorb

---- | This is 'biretract', but taking a @'C' ('ListBy' t)@ constraint instead of
---- a @'C' ('NonEmptyBy' t)@ constraint.  For example, for 'Day', it takes an
---- 'Applicative' constraint instead of an 'Apply' constraint.
----
---- In an ideal world, this would be not necessary, and we can use
---- 'biretract'.  However, sometimes @'C' ('ListBy' t)@ is not an actual
---- subclass of @'C' ('NonEmptyBy' t)@ (like 'Apply' and 'Applicative'), even though
---- it should technically always be so.
----
---- Note that you should only use this if @f@ doesn't already have the 'NonEmptyBy'
---- constraint (for example, for 'Day', if @f@ already has an 'Apply'
---- instance).  If it does, this could lead to conflicting instances.  If
---- @f@ already has the 'NonEmptyBy' instance, just use 'biretract' directly.  Only
---- use this with /specific/, concrete @f@s.
--biretractT :: forall t f. Monoidal t i f => t f f ~> f
--biretractT = upgradeC @t (Proxy @f)
--               biretract

---- | This is 'binterpret', but taking a @'C' ('ListBy' t)@ constraint instead of
---- a @'C' ('NonEmptyBy' t)@ constraint.  For example, for 'Day', it takes an
---- 'Applicative' constraint instead of an 'Apply' constraint.
----
---- In an ideal world, this would be not necessary, and we can use
---- 'biretract'.  However, sometimes @'C' ('ListBy' t)@ is not an actual
---- subclass of @'C' ('NonEmptyBy' t)@ (like 'Apply' and 'Applicative'), even though
---- it should technically always be so.
----
---- Note that you should only use this if @f@ doesn't already have the 'NonEmptyBy'
---- constraint (for example, for 'Day', if @f@ already has an 'Apply'
---- instance).  If it does, this could lead to conflicting instances.  If
---- @f@ already has the 'NonEmptyBy' instance, just use 'biretract' directly.  Only
---- use this with /specific/, concrete @f@s.
--binterpretT
--    :: forall t f g h. (Monoidal t, CM t h)
--    => f ~> h
--    -> g ~> h
--    -> t f g ~> h
--binterpretT f g = upgradeC @t (Proxy @h) $
--                    binterpret f g

-- | For some @t@, we have the ability to "statically analyze" the @'ListBy' t@
-- and pattern match and manipulate the structure without ever
-- interpreting or retracting.  These are 'Matchable'.
class Tensor t i => Matchable t i where
    -- | The inverse of 'splitNEB'.  A consing of @f@ to @'ListBy' t f@ is
    -- non-empty, so it can be represented as an @'NonEmptyBy' t f@.
    --
    -- This is analogous to a function @'uncurry' ('Data.List.NonEmpty.:|')
    -- :: (a, [a]) -> 'Data.List.NonEmpty.NonEmpty' a@.
    unsplitNEB :: t f (ListBy t f) ~> NonEmptyBy t f

    -- | "Pattern match" on an @'ListBy' t f@: it is either empty, or it is
    -- non-empty (and so can be an @'NonEmptyBy' t f@).
    --
    -- This is analgous to a function @'Data.List.NonEmpty.nonEmpty' :: [a]
    -- -> Maybe ('Data.List.NonEmpty.NonEmpty' a)@.
    --
    -- Note that because @t@ cannot be inferred from the input or output
    -- type, you should use this with /-XTypeApplications/:
    --
    -- @
    -- 'matchLB' \@'Day' :: 'Ap' f a -> ('Identity' :+: 'Ap1' f) a
    -- @
    matchLB   :: ListBy t f ~> i :+: NonEmptyBy t f

-- | An @'NonEmptyBy' t f@ is isomorphic to an @f@ consed with an @'ListBy' t f@, like
-- how a @'Data.List.NonEmpty.NonEmpty' a@ is isomorphic to @(a, [a])@.
splittingNEB
    :: Matchable t i
    => NonEmptyBy t f <~> t f (ListBy t f)
splittingNEB = isoF splitNEB unsplitNEB

-- | An @'ListBy' t f@ is isomorphic to either the empty case (@'I' t@) or the
-- non-empty case (@'NonEmptyBy' t f@), like how @[a]@ is isomorphic to @'Maybe'
-- ('Data.List.NonEmpty.NonEmpty' a)@.
matchingLB
    :: forall t i f. (Matchable t i, MonoidIn t i f)
    => ListBy t f <~> i :+: NonEmptyBy t f
matchingLB = isoF (matchLB @t) (nilLB @t !*! fromNEB @t)

instance Tensor (:*:) Proxy where
    type ListBy (:*:) = ListF
    intro1 = (:*: Proxy)
    intro2 = (Proxy :*:)
    elim1 (x      :*: ~Proxy) = x
    elim2 (~Proxy :*: y     ) = y

    appendLB (ListF xs :*: ListF ys) = ListF (xs ++ ys)
    splitNEB     = nonEmptyProd
    splittingLB = isoF to_ from_
      where
        to_ = \case
          ListF []     -> L1 Proxy
          ListF (x:xs) -> R1 (x :*: ListF xs)
        from_ = \case
          L1 ~Proxy           -> ListF []
          R1 (x :*: ListF xs) -> ListF (x:xs)

    toLB (x :*: y) = ListF [x, y]
    -- upgradeC _ x = x

instance Plus f => MonoidIn (:*:) Proxy f where
    pureT _        = zero

instance Tensor Product Proxy where
    type ListBy Product = ListF
    intro1 = (`Pair` Proxy)
    intro2 = (Proxy `Pair`)
    elim1 (Pair x ~Proxy) = x
    elim2 (Pair ~Proxy y) = y

    appendLB (ListF xs `Pair` ListF ys) = ListF (xs ++ ys)
    splitNEB     = viewF prodProd . nonEmptyProd
    splittingLB = isoF to_ from_
      where
        to_ = \case
          ListF []     -> L1 Proxy
          ListF (x:xs) -> R1 (x `Pair` ListF xs)
        from_ = \case
          L1 ~Proxy              -> ListF []
          R1 (x `Pair` ListF xs) -> ListF (x:xs)

    toLB (Pair x y) = ListF [x, y]
    -- upgradeC _ x = x

instance Plus f => MonoidIn Product Proxy f where
    pureT _         = zero

instance Tensor Day Identity where
    type ListBy Day = Ap
    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1

    appendLB (Day x y z) = z <$> x <*> y
    splitNEB     = ap1Day
    splittingLB = isoF to_ from_
      where
        to_ = \case
          Pure x  -> L1 (Identity x)
          Ap x xs -> R1 (Day x xs (&))
        from_ = \case
          L1 (Identity x) -> Pure x
          R1 (Day x xs f) -> Ap x (flip f <$> xs)

    toLB (Day x y z) = z <$> liftAp x <*> liftAp y
    -- upgradeC = unsafeApply

instance (Apply f, Applicative f) => MonoidIn Day Identity f where
    pureT            = generalize

instance Tensor (:+:) V1 where
    type ListBy (:+:) = Step
    intro1 = L1
    intro2 = R1

    elim1 = \case
      L1 x -> x
      R1 y -> absurd1 y
    elim2 = \case
      L1 x -> absurd1 x
      R1 y -> y

    appendLB    = id !*! stepUp . R1
    splitNEB     = stepDown
    splittingLB = stepping . sumLeftIdentity

    toLB  = \case
      L1 x -> Step 0 x
      R1 x -> Step 1 x
--    upgradeC _ x = x

instance MonoidIn (:+:) V1 f where
    pureT = absurd1

instance Tensor Sum V1 where
    type ListBy Sum = Step
    intro1 = InL
    intro2 = InR

    elim1 = \case
      InL x -> x
      InR y -> absurd1 y
    elim2 = \case
      InL x -> absurd1 x
      InR y -> y

    appendLB    = id !*! stepUp . R1
    splitNEB     = viewF sumSum . stepDown
    splittingLB = stepping
                . sumLeftIdentity
                . overHBifunctor id sumSum

    toLB  = \case
      InL x -> Step 0 x
      InR x -> Step 1 x
--    upgradeC _ x = x

instance MonoidIn Sum V1 f where
    pureT = absurd1


instance Tensor These1 V1 where
    type ListBy These1 = Steps
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

    appendLB    = \case
      This1  x   -> x
      That1    y -> stepsUp . That1 $ y
      These1 x y -> x <> y
    splitNEB     = stepsDown . flaggedVal . getComposeT
    splittingLB = steppings . sumLeftIdentity

    toLB  = \case
      This1  x   -> Steps $ NEM.singleton 0 x
      That1    y -> Steps $ NEM.singleton 1 y
      These1 x y -> Steps $ NEM.fromDistinctAscList ((0, x) :| [(1, y)])
    -- upgradeC _ x = x

instance Alt f => MonoidIn These1 V1 f where
    pureT = absurd1

instance Tensor Comp Identity where
    type ListBy Comp = Free

    intro1 = (:>>= Identity)
    intro2 = (Identity () :>>=) . const

    elim1 (x :>>= y) = runIdentity . y <$> x
    elim2 (x :>>= y) = y (runIdentity x)

    appendLB (x :>>= y) = x >>= y
    splitNEB             = free1Comp
    splittingLB = isoF to_ from_
      where
        to_ :: Free f ~> Identity :+: Comp f (Free f)
        to_ = foldFree' (L1 . Identity) $ \y n -> R1 $
            y :>>= (from_ . n)
        from_ :: Identity :+: Comp f (Free f) ~> Free f
        from_ = generalize
            !*! (\case x :>>= f -> liftFree x >>= f)

    toLB (x :>>= y) = liftFree x >>= (inject . y)
    -- upgradeC = unsafeBind

instance (Bind f, Monad f) => MonoidIn Comp Identity f where
    pureT           = generalize

instance Matchable (:*:) Proxy where
    unsplitNEB = ProdNonEmpty
    matchLB   = fromListF

instance Matchable Product Proxy where
    unsplitNEB = ProdNonEmpty . reviewF prodProd
    matchLB   = fromListF

instance Matchable Day Identity where
    unsplitNEB = DayAp1
    matchLB   = fromAp

instance Matchable (:+:) V1 where
    unsplitNEB   = stepUp
    matchLB     = R1

instance Matchable Sum V1 where
    unsplitNEB   = stepUp . reviewF sumSum
    matchLB     = R1

-- We can't write this until we get an isomorphism between MF These1 and SF These1
-- instance Matchable These1 where
--     unsplitNEB = stepsUp
--     matchLB   = R1
