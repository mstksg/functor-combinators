
-- |
-- Module      : Data.Functor.Invariant.Day
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provides an 'Invariant' version of the typical Haskell Day convolution
-- over tuples.
--
-- @since 0.3.0.0
module Data.Functor.Invariant.Day.Chain (
  -- * Chain
    DayChain(.., Gather, Knot)
  , runCoDayChain
  , runContraDayChain
  , chainAp
  , chainDiv
  , gather, gathered
  , assembleDayChain
  , assembleDayChainRec
  , concatDayChain
  , concatDayChainRec
  -- * Nonempty Chain
  , DayChain1(.., DayChain1)
  , runCoDayChain1
  , runContraDayChain1
  , chainAp1
  , chainDiv1
  , gather1, gathered1
  , assembleDayChain1
  , assembleDayChain1Rec
  , concatDayChain1
  , concatDayChain1Rec
  -- * Day Utility
  , runDayApply
  , runDayDivise
  ) where

import           Control.Applicative
import           Control.Applicative.Free                  (Ap(..))
import           Control.Applicative.ListF                 (MaybeF(..))
import           Control.Natural
import           Data.Coerce
import           Data.Functor.Apply
import           Data.Functor.Apply.Free (Ap1(..))
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Contravariant.Divisible.Free (Div(..), Div1)
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Day
import           Data.HBifunctor.Tensor hiding             (elim1, elim2, intro1, intro2)
import           Data.HFunctor
import           Data.HFunctor.Chain
import           Data.HFunctor.Chain.Internal
import           Data.SOP hiding                           (hmap)
import qualified Data.Vinyl                                as V
import qualified Data.Vinyl.Functor                        as V

-- | Interpret the covariant part of a 'Day' into a target context @h@,
-- as long as the context is an instance of 'Apply'.  The 'Apply' is used to
-- combine results back together using '<*>'.
runDayApply
    :: forall f g h. Apply h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayApply f g (Day x y j _) = liftF2 j (f x) (g y)

-- | Interpret the contravariant part of a 'Day' into a target context
-- @h@, as long as the context is an instance of 'Divise'.  The 'Divise' is
-- used to split up the input to pass to each of the actions.
runDayDivise
    :: forall f g h. Divise h
    => f ~> h
    -> g ~> h
    -> Day f g ~> h
runDayDivise f g (Day x y _ h) = divise h (f x) (g y)

-- | In the covariant direction, we can interpret out of a 'Chain1' of 'Day'
-- into any 'Apply'.
runCoDayChain1
    :: forall f g. Apply g
    => f ~> g
    -> DayChain1 f ~> g
runCoDayChain1 f = foldChain1 f (runDayApply f id) . unDayChain1

-- | In the contravariant direction, we can interpret out of a 'Chain1' of
-- 'Day' into any 'Divise'.
runContraDayChain1
    :: forall f g. Divise g
    => f ~> g
    -> DayChain1 f ~> g
runContraDayChain1 f = foldChain1 f (runDayDivise f id) . unDayChain1

-- | In the covariant direction, we can interpret out of a 'Chain' of 'Day'
-- into any 'Applicative'.
runCoDayChain
    :: forall f g. Applicative g
    => f ~> g
    -> DayChain f ~> g
runCoDayChain f = foldChain (pure . runIdentity) (\case Day x y h _ -> liftA2 h (f x) y)
                . unDayChain

-- | In the contravariant direction, we can interpret out of a 'Chain' of
-- 'Day' into any 'Divisible'.
runContraDayChain
    :: forall f g. Divisible g
    => f ~> g
    -> DayChain f ~> g
runContraDayChain f = foldChain (const conquer) (\case Day x y _ g -> divide g (f x) y)
                    . unDayChain

-- | Extract the 'Ap' part out of a 'DayChain', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
chainAp :: DayChain f ~> Ap f
chainAp = runCoDayChain inject

-- | Extract the 'Ap1' part out of a 'DayChain1', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
chainAp1 :: DayChain1 f ~> Ap1 f
chainAp1 = runCoDayChain1 inject

-- | Extract the 'Div' part out of a 'DayChain', shedding the
-- covariant bits.
--
-- @since 0.3.2.0
chainDiv :: DayChain f ~> Div f
chainDiv = runContraDayChain inject

-- | Extract the 'Div1' part out of a 'DayChain1', shedding the
-- covariant bits.
--
-- @since 0.3.2.0
chainDiv1 :: DayChain1 f ~> Div1 f
chainDiv1 = runContraDayChain1 inject

-- | Match on a non-empty 'DayChain'; contains no @f@s, but only the
-- terminal value.  Analogous to the 'Control.Applicative.Free.Ap'
-- constructor.
pattern Gather :: (a -> (b, c)) -> (b -> c -> a) -> f b -> DayChain f c -> DayChain f a
pattern Gather f g x xs <- (unGather_->MaybeF (Just (Day x xs g f)))

unGather_ :: DayChain f ~> MaybeF (Day f (DayChain f))
unGather_ = \case
  DayChain (More (Day x xs g f)) -> MaybeF . Just $ Day x (DayChain xs) g f
  DayChain (Done _             ) -> MaybeF Nothing

-- | Match on an "empty" 'DayChain'; contains no @f@s, but only the
-- terminal value.  Analogous to 'Control.Applicative.Free.Pure'.
pattern Knot :: a -> DayChain f a
pattern Knot x = DayChain (Done (Identity x))
{-# COMPLETE Gather, Knot #-}

-- | Match on a 'DayChain1' to get the head and the rest of the items.
-- Analogous to the 'Data.Functor.Apply.Free.Ap1' constructor.
pattern DayChain1 :: Invariant f => (a -> (b, c)) -> (b -> c -> a) -> f b -> DayChain f c -> DayChain1 f a
pattern DayChain1 f g x xs <- (coerce splitChain1->Day x xs g f)
  where
    DayChain1 f g x xs = unsplitNE $ Day x xs g f
{-# COMPLETE DayChain1 #-}

-- | Invariantly combine two 'DayChain's.
--
-- Analogous to 'liftA2' and 'divise'.  If there was some typeclass that
-- represented semigroups on invariant 'Day', this would be the method of
-- that typeclass.
--
-- The identity of this is 'Knot'.
--
-- @since 0.3.4.0
gather
    :: (a -> (b, c))
    -> (b -> c -> a)
    -> DayChain f b
    -> DayChain f c
    -> DayChain f a
gather f g x y = coerce appendChain (Day x y g f)

-- | Convenient wrapper over 'gather' that simply combines the two options
-- in a tuple.  Analogous to 'divised'.
--
-- @since 0.3.4.0
gathered
    :: DayChain f a
    -> DayChain f b
    -> DayChain f (a, b)
gathered = gather id (,)

-- | Invariantly combine two 'DayChain1's.
--
-- Analogous to 'liftA2' and 'divise'.  If there was some typeclass that
-- represented semigroups on invariant 'Day', this would be the method of
-- that typeclass.
--
-- @since 0.3.4.0
gather1
    :: Invariant f
    => (a -> (b, c))
    -> (b -> c -> a)
    -> DayChain1 f b
    -> DayChain1 f c
    -> DayChain1 f a
gather1 f g x y = coerce appendChain1 (Day x y g f)

-- | Convenient wrapper over 'gather1' that simply combines the two options
-- in a tuple.  Analogous to 'divised'.
--
-- @since 0.3.4.0
gathered1
    :: Invariant f
    => DayChain1 f a
    -> DayChain1 f b
    -> DayChain1 f (a, b)
gathered1 = gather1 id (,)

-- | Convenient wrapper to build up a 'DayChain' by providing each
-- component of it.  This makes it much easier to build up longer chains
-- because you would only need to write the splitting/joining functions in
-- one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MT Int Bool String
-- @
--
-- and an invariant functor @Prim@ (representing, say, a bidirectional
-- parser, where @Prim Int@ is a bidirectional parser for an 'Int'@),
-- then you could assemble a bidirectional parser for a @MyType@ using:
--
-- @
-- invmap (\(MyType x y z) -> I x :* I y :* I z :* Nil)
--        (\(I x :* I y :* I z :* Nil) -> MyType x y z) $
--   assembleDayChain $ intPrim
--                   :* boolPrim
--                   :* stringPrim
--                   :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'Knot' directly.
-- *    If you have 1 component, use 'inject' or 'injectChain' directly.
-- *    If you have 2 components, use 'toListBy' or 'toChain'.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off tuples one-by-one.
assembleDayChain
    :: NP f as
    -> DayChain f (NP I as)
assembleDayChain = \case
    Nil     -> DayChain $ Done $ Identity Nil
    x :* xs -> DayChain $ More $ Day
      x
      (unDayChain (assembleDayChain xs))
      consNPI
      unconsNPI

-- | A version of 'assembleDayChain' where each component is itself
-- a 'DayChain'.
--
-- @
-- assembleDayChain (x :* y :* z :* Nil)
--   = concatDayChain (injectChain x :* injectChain y :* injectChain z :* Nil)
-- @
concatDayChain
    :: NP (DayChain f) as
    -> DayChain f (NP I as)
concatDayChain = \case
    Nil     -> DayChain $ Done $ Identity Nil
    x :* xs -> coerce appendChain $ Day
      x
      (concatDayChain xs)
      consNPI
      unconsNPI

-- | A version of 'assembleDayChain' but for 'DayChain1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Divise' or 'Apply' instance, but no 'Divisible' or 'Applicative'.
assembleDayChain1
    :: Invariant f
    => NP f (a ': as)
    -> DayChain1 f (NP I (a ': as))
assembleDayChain1 = \case
    x :* xs -> DayChain1_ $ case xs of
      Nil    -> Done1 $ invmap ((:* Nil) . I) (unI . hd) x
      _ :* _ -> More1 $ Day
        x
        (unDayChain1 (assembleDayChain1 xs))
        consNPI
        unconsNPI

-- | A version of 'concatDayChain' but for 'DayChain1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Divise' or 'Apply' instance, but no 'Divisible' or 'Applicative'.
concatDayChain1
    :: Invariant f
    => NP (DayChain1 f) (a ': as)
    -> DayChain1 f (NP I (a ': as))
concatDayChain1 = \case
    x :* xs -> case xs of
      Nil    -> invmap ((:* Nil) . I) (unI . hd) x
      _ :* _ -> coerce appendChain1 $ Day
        x
        (concatDayChain1 xs)
        consNPI
        unconsNPI

unconsNPI :: NP I (a ': as) -> (a, NP I as)
unconsNPI (I y :* ys) = (y, ys)

consNPI :: a -> NP I as -> NP I (a ': as)
consNPI y ys = I y :* ys

-- | A version of 'assembleDayChain' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @
-- data MyType = MT Int Bool String
--
-- invmap (\(MyType x y z) -> x ::& y ::& z ::& RNil)
--        (\(x ::& y ::& z ::& RNil) -> MyType x y z) $
--   assembleDayChainRec $ intPrim
--                      :& boolPrim
--                      :& stringPrim
--                      :& Nil
-- @
assembleDayChainRec
    :: V.Rec f as
    -> DayChain f (V.XRec V.Identity as)
assembleDayChainRec = \case
    V.RNil    -> DayChain $ Done $ Identity V.RNil
    x V.:& xs -> DayChain $ More $ Day
      x
      (unDayChain (assembleDayChainRec xs))
      (V.::&)
      unconsRec

-- | A version of 'concatDayChain' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
concatDayChainRec
    :: V.Rec (DayChain f) as
    -> DayChain f (V.XRec V.Identity as)
concatDayChainRec = \case
    V.RNil    -> DayChain $ Done $ Identity V.RNil
    x V.:& xs -> coerce appendChain $ Day
      x
      (concatDayChainRec xs)
      (V.::&)
      unconsRec

-- | A version of 'assembleDayChain1' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
assembleDayChain1Rec
    :: Invariant f
    => V.Rec f (a ': as)
    -> DayChain1 f (V.XRec V.Identity (a ': as))
assembleDayChain1Rec = \case
    x V.:& xs -> case xs of
      V.RNil   -> DayChain1_ $ Done1 $ invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
      _ V.:& _ -> DayChain1_ $ More1 $ Day
        x
        (unDayChain1 (assembleDayChain1Rec xs))
        (V.::&)
        unconsRec

-- | A version of 'concatDayChain1' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
concatDayChain1Rec
    :: Invariant f
    => V.Rec (DayChain1 f) (a ': as)
    -> DayChain1 f (V.XRec V.Identity (a ': as))
concatDayChain1Rec = \case
    x V.:& xs -> case xs of
      V.RNil   -> invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
      _ V.:& _ -> coerce appendChain1 $ Day
        x
        (concatDayChain1Rec xs)
        (V.::&)
        unconsRec

unconsRec :: V.XRec V.Identity (a ': as) -> (a, V.XRec V.Identity as)
unconsRec (y V.::& ys) = (y, ys)
