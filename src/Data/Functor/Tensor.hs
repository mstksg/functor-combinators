{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveFunctor              #-}
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
-- Module      : Data.Functor.Tensor
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
module Data.Functor.Tensor (
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
  , matchMF
  , unmatchMF
  -- ** Utility
  , inL
  , inR
  , fromSF
  -- * 'Chain'
  , Chain(..)
  , foldChain
  , unfoldChain
  , matchChain
  , splitChain1
  , injectChain
  , unrollMF
  , rerollMF
  , unrollingMF
  -- * Combinators
  , ClownT(..)

  -- , JoinT(..)
  -- , TannenT(..)
  -- , BiffT(..)
  -- , ClownT(..)
  -- , JokerT(..)
  ) where

import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Function
import           Data.Functor.Apply.Free
import           Data.Functor.Associative
import           Data.Functor.Day           (Day(..))
import           Data.Functor.HBifunctor
import           Data.Functor.HFunctor
import           Data.Functor.HFunctor.IsoF
import           Data.Functor.Identity
import           Data.Functor.Interpret
import           Data.Functor.Plus
import           Data.Kind
import           Data.Proxy
import           GHC.Generics hiding        (C)
import qualified Data.Functor.Day           as D

-- | A 'HBifunctor' can be a 'Tensor' if:
--
-- 1.   There is some identity @i@ where @t i f@ is equivalent to just @f@.
--      That is, "enhancing" @f@ with @t i@ does nothing.
--
-- 2.   @t@ is associative: @f `t` (g `t` h)@ is equivalent to @(f `t` g)
--      `t` h)@.
--
-- The methods in this class provide us useful ways of navigating
-- a @'Tensor' t@ with respect to this property.
--
-- Realistically, there won't be any 'Tensor' instances that are not also
-- 'Monoidal' instances.  The two classes are separated only to help
-- organize functionality into cleaner sub-divisions.
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
    type I t :: Type -> Type

    intro1 :: f ~> t f (I t)
    intro2 :: g ~> t (I t) g

    elim1 :: Functor f => t f (I t) ~> f
    elim2 :: Functor g => t (I t) g ~> g

    {-# MINIMAL intro1, intro2, elim1, elim2 #-}

rightIdentity :: (Tensor t, Functor f) => f <~> t f    (I t)
rightIdentity = isoF intro1 elim1

leftIdentity  :: (Tensor t, Functor g) => g <~> t (I t) g
leftIdentity = isoF intro2 elim2


-- | A useful construction that works like a "linked list" of @t f@ applied
-- to itself multiple times.  That is, it contains @t f f@, @t f (t f f)@,
-- @t f (t f (t f f))@, etc.
--
-- If @t@ is 'Monoidal', then it means we can "collapse" this linked list
-- into some final type @'MF' t@ ('fromF'), and also extract it back into a linked
-- list ('toF').
data Chain t i f a = Done (i a)
               | More (t f (Chain t i f) a)

instance (Functor i, Functor (t f (Chain t i f))) => Functor (Chain t i f) where
    fmap f = \case
      Done x  -> Done (fmap f x)
      More xs -> More (fmap f xs)

deriving instance (Show (i a), Show (t f (Chain t i f) a)) => Show (Chain t i f a)
deriving instance (Read (i a), Read (t f (Chain t i f) a)) => Read (Chain t i f a)

foldChain
    :: forall t i f g. HBifunctor t
    => (i ~> g)
    -> (t f g ~> g)
    -> Chain t i f ~> g
foldChain f g = go
  where
    go :: Chain t i f ~> g
    go = \case
      Done x  -> f x
      More xs -> g (hright go xs)

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

-- | We can collapse and interpret an @'Chain' t i@ if we have @'Tensor' t@.
--
-- Note that 'inject' only requires @'Tensor' t@.  This is given as
-- 'injectChain'.
instance (Monoidal t, i ~ I t) => Interpret (Chain t i) where
    type C (Chain t i) = AndC (C (SF t)) (C (MF t))
    inject  = injectChain
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

-- | If we have @'Tensor' t@, we can make a singleton 'Chain'.
--
-- We can also 'retract' and 'interpret' an 'Chain' using its 'Interpret'
-- instance.
injectChain :: forall t f. Tensor t => f ~> Chain t (I t) f
injectChain = More . hright Done . intro1


-- | For some tensors @t@, you can represt the act of repeatedly combining
-- the same functor an arbitrary amount of times:
--
-- @
-- t f f                    -- 2 times
-- t f (t f f)              -- 3 times
-- t f (t f (t f f))        -- 4 times
-- t f (t f (t f (t f f)))  -- 5 times
-- @
--
-- Sometimes, we have a type that can /describe/ this repeated combination.
-- For example, @'ListF' f@ is the type that contains @f@ ':*:'d with
-- itself many number of times, and @'Ap'@ is the type that contains @f@
-- 'Day'd with itself many number of times.
--
-- @
-- 'ListF' [x, y]       == x ':*:' y
-- 'ListF' [x, y, z]    == x ':*:' y ':*:' z
-- 'ListF' [x, y, z, q] == x ':*:' y ':*:' z ':*:' q
-- @
--
-- This is convenient because it allows you to represent repeated
-- applications of @t@ as a single data type.
--
-- For example, @'Day' f f@ can be interpreted as "two sequenced @f@s",
-- allowing you to specify "I want exactly two sequenced @f@s".  If you
-- want to specify "I want 0, 1, or many @f@s sequenced after each other",
-- then you can use @'Ap' f@.
--
-- And, @f ':*:' f@ can be interpreted as "a free selection of two @f@s",
-- allowing you to specify "I have to @f@s that I can use".  If you want to
-- specify "I want 0, 1, or many different @f@s that I can use", you can
-- use @'ListF' f@.
--
-- The 'Monoidal' class unifies different such patterns.  The associated
-- type 'MF' is the "repeated aplications of @t@" type.
--
-- See documentation of "Data.Functor.Tensor" for information on how to
-- define instances of this typeclass.
class (Tensor t, Semigroupoidal t, Interpret (MF t)) => Monoidal t where
    type MF t :: (Type -> Type) -> Type -> Type

    splittingSF :: SF t f <~> t f (MF t f)
    appendMF    :: t (MF t f) (MF t f) ~> MF t f

    matchingMF  :: MF t f <~> I t :+: SF t f
    matchingMF  = splittingMF @t . overHBifunctor id (fromF (splittingSF @t))

    splittingMF :: MF t f <~> I t :+: t f (MF t f)
    splittingMF = matchingMF @t . overHBifunctor id (splittingSF @t)

    toMF     :: t f f ~> MF t f
    toMF     = reviewF (matchingMF @t)
             . R1
             . reviewF (splittingSF @t)
             . hright (inject @(MF t))

    pureT  :: C (MF t) f => I t ~> f
    pureT  = retract . reviewF (matchingMF @t) . L1

    {-# MINIMAL splittingSF, appendMF, (matchingMF | splittingMF) #-}

fromSF   :: forall t f. Monoidal t => SF t f ~> MF t f
fromSF   = reviewF (matchingMF @t) . R1
nilMF    :: forall t f. Monoidal t => I t ~> MF t f
nilMF    = reviewF (matchingMF @t) . L1
consMF   :: forall t f. Monoidal t => t f (MF t f) ~> MF t f
consMF   = reviewF (splittingMF @t) . R1
unconsMF :: forall t f. Monoidal t => MF t f ~> I t :+: t f (MF t f)
unconsMF = viewF splittingMF

    ---- | If @'MF' t f@ represents multiple applications of @t f@ with
    ---- itself, then @nilMF@ gives us "zero applications of @f@".
    ----
    ---- Note that @t@ cannot be inferred from the type of 'nilMF', so this
    ---- function must always be called with -XTypeApplications:
    ----
    ---- @
    ---- 'nilMF' \@'Day' :: 'Identity' '~>' 'Ap' f
    ---- 'nilMF' \@'Comp' :: 'Identity' '~>' 'Free' f
    ---- 'nilMF' \@(':*:') :: 'Proxy' '~>' 'ListF' f
    ---- @
    ----
    ---- Together with 'consMF', forms an inverse with 'unconsMF'.
    --nilMF    :: I t ~> MF t f
    --consMF   :: t f (MF t f) ~> MF t f

    ---- | If a @'MF' t f@ represents multiple applications of @t f@ to itself,
    ---- 'unconsMF' lets us break it up into two possibilities:
    ----
    ---- 1.   The @'MF' t f@ had no applications of @f@
    ---- 2.   The @'MF' t f@ had at least one application of @f@; we return
    ----      the "first" @f@ applied to the rest of the @f@s.
    ----
    ---- Should form an inverse with 'reconsMF':
    ----
    ---- @
    ---- 'reconsMF' . 'unconsMF' == id
    ---- 'unconsMF' . 'reconsMF' == id
    ---- @
    ----
    ---- where 'reconsMF' is 'nilMF' on the left side of the ':+:', and
    ---- 'consMF' on the right side of the ':+:'.
    --unconsMF   :: MF t f ~> I t :+: t f (MF t f)
    ---- unconsMF m = case toF @t m of
    ----   Done x  -> L1 x
    ----   More xs -> R1 . hright fromF $ xs

    --appendMF :: t (MF t f) (MF t f) ~> MF t f

    --fromSF   :: SF t f ~> t f (MF t f)
    --unconsSF :: MF t f ~> I t :+: SF t f

    ---- | Embed a direct application of @f@ to itself into a @'MF' t f@.
    --toMF     :: t f f ~> MF t f
    --toMF     = consMF . fromSF @t . toSF

    ---- | If we have an instance of @t@, we can generate an @f@ based on how
    ---- it interacts with @t@.
    ----
    ---- Specialized (and simplified), this type is:
    ----
    ---- @
    ---- 'pureT' \@'Day'   :: 'Applicative' f => a -> f a  -- 'pure'
    ---- 'pureT' \@'Comp'  :: 'Monad' f => a -> f a    -- 'return'
    ---- 'pureT' \@(':*:') :: 'Plus' f => f a          -- 'zero'
    ---- @
    --pureT  :: C (MF t) f => I t ~> f
    --pureT  = retract . nilMF @t


    ---- | Convert a linked list of @t f@s applied to themselves (stored in
    ---- the 'Chain' type) into @'MF' t f@, the data type representing multiple
    ---- applications of @t f@ to itself.
    ----
    ---- @'Chain' i ('I' t)@ can be thought of as a "universal" representation of
    ---- multiple-applications-to-self, and @'MF' t@ can be thought of as
    ---- a tailor-made represenation for your specific @'Tensor' t@.
    ----
    ---- @
    ---- 'fromF' . 'toF' == id
    ---- 'toF' . 'fromF' == id
    ---- @
    ----
    ---- 'fromF', 'toF', and 'appendF' are a way to completely define
    ---- a 'Monoidal' instance; all other methods can be inferred from them.
    ---- In some cases, it can be easier to define these instead of the other
    ---- ones.
    --fromF :: Chain t (I t) f ~> MF t f
    --fromF = \case
    --  Done x  -> nilMF @t x
    --  More xs -> consMF . hright fromF $ xs

    ---- | The inverse of 'fromF': convert a @'MF' t f@ into a linked list of
    ---- @t f@s applied to themselves.  See 'fromF' for more information.
    ----
    ---- 'fromF', 'toF', and 'appendF' are a way to completely define
    ---- a 'Monoidal' instance; all other methods can be inferred from them.
    ---- In some cases, it can be easier to define these instead of the other
    ---- ones.
    --toF :: MF t f ~> Chain t (I t) f
    --toF x = case unconsMF x of
    --  L1 y -> Done y
    --  R1 z -> More . hright toF $ z

    ---- | Append two linked lists of @t f@ applied to itself together.
    ----
    ---- 'fromF', 'toF', and 'appendF' are a way to completely define
    ---- a 'Monoidal' instance; all other methods can be inferred from them.
    ---- In some cases, it can be easier to define these instead of the other
    ---- ones.
    --appendF  :: t (Chain t (I t) f) (Chain t (I t) f) ~> Chain t (I t) f
    --appendF = toF . appendMF . hbimap fromF fromF

    -- {-# MINIMAL nilMF, consMF, unconsMF, appendMF | fromF, toF, appendF #-}

unrollingMF :: forall t f. Monoidal t => MF t f <~> Chain t (I t) f
unrollingMF = isoF unrollMF rerollMF

unrollMF :: forall t f. Monoidal t => MF t f ~> Chain t (I t) f
unrollMF = unfoldChain (unconsMF @t)

rerollMF :: forall t f. Monoidal t => Chain t (I t) f ~> MF t f
rerollMF = foldChain (nilMF @t) consMF

matchMF :: forall t f. Monoidal t => MF t f ~> I t :+: SF t f
matchMF = viewF (matchingMF @t)

unmatchMF :: forall t f. Monoidal t => I t :+: SF t f ~> MF t f
unmatchMF = reviewF (matchingMF @t)

splitChain1
    :: forall t f. (Monoidal t, Functor f)
    => Chain1 t f <~> t f (Chain t (I t) f)
splitChain1 = fromF unrollingSF
        . splittingSF @t
        . overHBifunctor id unrollingMF

matchChain
    :: forall t f. (Monoidal t, Functor f)
    => Chain t (I t) f <~> I t :+: Chain1 t f
matchChain = fromF unrollingMF
           . matchingMF @t
           . overHBifunctor id unrollingSF

-- | Convenient wrapper over 'intro1' that lets us introduce an arbitrary
-- functor @g@ to the right of an @f@.
inL
    :: forall t f g a. (Monoidal t, C (MF t) g)
    => f a
    -> t f g a
inL = hright (pureT @t) . intro1 @t

-- | Convenient wrapper over 'intro2' that lets us introduce an arbitrary
-- functor @f@ to the right of a @g@.
inR
    :: forall t f g a. (Monoidal t, C (MF t) f)
    => g a
    -> t f g a
inR = hleft (pureT @t) . intro2 @t

instance Tensor (:*:) where
    type I (:*:) = Proxy

    intro1 = (:*: Proxy)
    intro2 = (Proxy :*:)

    elim1 (x :*: _) = x
    elim2 (_ :*: y) = y

instance Monoidal (:*:) where
    type MF (:*:) = ListF

    splittingSF = isoF nonEmptyProd ProdNonEmpty
    appendMF (ListF xs :*: ListF ys) = ListF (xs ++ ys)

    matchingMF  = isoF fromListF $ \case
      L1 ~Proxy -> ListF []
      R1 x      -> toListF x
    splittingMF = isoF to_ from_
      where
        to_ = \case
          ListF []     -> L1 Proxy
          ListF (x:xs) -> R1 (x :*: ListF xs)
        from_ = \case
          L1 ~Proxy           -> ListF []
          R1 (x :*: ListF xs) -> ListF (x:xs)

    toMF   (x :*: y       ) = ListF [x, y]
    pureT          _         = zero

instance Tensor Day where
    type I Day = Identity

    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1

instance Monoidal Day where
    type MF Day = Ap

    splittingSF          = isoF ap1Day DayAp1
    appendMF (Day x y z) = z <$> x <*> y

    matchingMF  = isoF fromAp $ \case
      L1 (Identity x) -> pure x
      R1 x            -> toAp x
    splittingMF = isoF to_ from_
      where
        to_ = \case
          Pure x  -> L1 (Identity x)
          Ap x xs -> R1 (Day x xs (&))
        from_ = \case
          L1 (Identity x) -> Pure x
          R1 (Day x xs f) -> Ap x (flip f <$> xs)

    toMF   (Day x y z) = z <$> liftAp x <*> liftAp y
    pureT                      = pure . runIdentity


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

instance Monoidal (:+:) where
    type MF (:+:) = Step

    splittingSF = stepping
    appendMF    = appendSF

    matchingMF  = voidLeftIdentity
    splittingMF = stepping . voidLeftIdentity

    toMF     = toSF
    pureT      = absurd1

voidLeftIdentity :: f <~> Void1 :+: f
voidLeftIdentity = isoF R1 (absurd1 !*! id)

voidRightIdentity :: f <~> Void1 :+: f
voidRightIdentity = isoF R1 (absurd1 !*! id)

instance Tensor Comp where
    type I Comp = Identity

    intro1 = (:>>= Identity)
    intro2 = (Identity () :>>=) . const

    elim1 (x :>>= y) = runIdentity . y <$> x
    elim2 (x :>>= y) = y (runIdentity x)

instance Monoidal Comp where
    type MF Comp = Free

    splittingSF         = isoF free1Comp CompFree1
    appendMF (x :>>= y) = x >>= y

    matchingMF  = isoF fromFree $ \case
      L1 (Identity x) -> pure x
      R1 x            -> toFree x
    splittingMF = isoF to_ from_
      where
        to_ :: Free f ~> Identity :+: Comp f (Free f)
        to_ x = runFree x (L1 . Identity) $ \y n -> R1 $
            y :>>= (from_ . n)
        from_ :: Identity :+: Comp f (Free f) ~> Free f
        from_ = pure . runIdentity
            !*! (\case x :>>= f -> liftFree x >>= f)

    toMF   (x :>>= y) = liftFree x >>= (inject . y)

    pureT                     = pure . runIdentity

