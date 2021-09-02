{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      : Data.Functor.Invariant.Day
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provide an invariant functor combinator sequencer, like a combination of
-- 'Ap' and 'Div'.
--
-- @since 0.3.5.0
module Data.Functor.Invariant.DivAp (
  -- * Chain
    DivAp(.., Gather, Knot)
  , runCoDivAp
  , runContraDivAp
  , divApAp
  , divApDiv
  , foldDivAp
  , assembleDivAp
  , assembleDivApRec
  , concatDivAp
  , concatDivApRec
  -- * Nonempty Chain
  , DivAp1(.., DivAp1)
  , runCoDivAp1
  , runContraDivAp1
  , divApAp1
  , divApDiv1
  , foldDivAp1
  , assembleDivAp1
  , assembleDivAp1Rec
  , concatDivAp1
  , concatDivAp1Rec
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
import           Data.Functor.Invariant.Inplicative
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
runCoDivAp1
    :: forall f g. Apply g
    => f ~> g
    -> DivAp1 f ~> g
runCoDivAp1 f = foldDivAp1 f (runDayApply f id)

-- | In the contravariant direction, we can interpret out of a 'Chain1' of
-- 'Day' into any 'Divise'.
runContraDivAp1
    :: forall f g. Divise g
    => f ~> g
    -> DivAp1 f ~> g
runContraDivAp1 f = foldDivAp1 f (runDayDivise f id)

-- | In the covariant direction, we can interpret out of a 'Chain' of 'Day'
-- into any 'Applicative'.
runCoDivAp
    :: forall f g. Applicative g
    => f ~> g
    -> DivAp f ~> g
runCoDivAp f = foldDivAp pure (\case Day x y h _ -> liftA2 h (f x) y)

-- | In the contravariant direction, we can interpret out of a 'Chain' of
-- 'Day' into any 'Divisible'.
runContraDivAp
    :: forall f g. Divisible g
    => f ~> g
    -> DivAp f ~> g
runContraDivAp f = foldDivAp (const conquer) (\case Day x y _ g -> divide g (f x) y)

-- | General-purpose folder of 'DivAp'.  Provide a way to handle the
-- identity ('pure'/'conquer'/'Knot') and a way to handle a cons
-- ('liftA2'/'divide'/'Gather').
--
-- @since 0.3.5.0
foldDivAp
    :: (forall x. x -> g x)
    -> (Day f g ~> g)
    -> DivAp f ~> g
foldDivAp f g = foldChain (f . runIdentity) g . unDivAp

-- | General-purpose folder of 'DivAp1'.  Provide a way to handle the
-- individual leaves and a way to handle a cons ('liftF2/'divise'/'Gather').
--
-- @since 0.3.5.0
foldDivAp1
    :: (f ~> g)
    -> (Day f g ~> g)
    -> DivAp1 f ~> g
foldDivAp1 f g = foldChain1 f g . unDivAp1





-- | Extract the 'Ap' part out of a 'DivAp', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
divApAp :: DivAp f ~> Ap f
divApAp = runCoDivAp inject

-- | Extract the 'Ap1' part out of a 'DivAp1', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
divApAp1 :: DivAp1 f ~> Ap1 f
divApAp1 = runCoDivAp1 inject

-- | Extract the 'Div' part out of a 'DivAp', shedding the
-- covariant bits.
--
-- @since 0.3.2.0
divApDiv :: DivAp f ~> Div f
divApDiv = runContraDivAp inject

-- | Extract the 'Div1' part out of a 'DivAp1', shedding the
-- covariant bits.
--
-- @since 0.3.2.0
divApDiv1 :: DivAp1 f ~> Div1 f
divApDiv1 = runContraDivAp1 inject

-- | Match on a non-empty 'DivAp'; contains no @f@s, but only the
-- terminal value.  Analogous to the 'Control.Applicative.Free.Ap'
-- constructor.
pattern Gather :: (b -> c -> a) -> (a -> (b, c)) -> f b -> DivAp f c -> DivAp f a
pattern Gather f g x xs <- (unGather_->MaybeF (Just (Day x xs f g)))
  where
    Gather f g x xs = DivAp $ More $ Day x (unDivAp xs) f g

unGather_ :: DivAp f ~> MaybeF (Day f (DivAp f))
unGather_ = \case
  DivAp (More (Day x xs g f)) -> MaybeF . Just $ Day x (DivAp xs) g f
  DivAp (Done _             ) -> MaybeF Nothing

-- | Match on an "empty" 'DivAp'; contains no @f@s, but only the
-- terminal value.  Analogous to 'Control.Applicative.Free.Pure'.
pattern Knot :: a -> DivAp f a
pattern Knot x = DivAp (Done (Identity x))
{-# COMPLETE Gather, Knot #-}

instance Inply (DivAp f) where
    gather = coerce (gather @(Chain Day Identity _))

instance Inplicative (DivAp f) where
    knot = coerce (knot @(Chain Day Identity _))

-- | Match on a 'DivAp1' to get the head and the rest of the items.
-- Analogous to the 'Data.Functor.Apply.Free.Ap1' constructor.
pattern DivAp1 :: Invariant f => (b -> c -> a) -> (a -> (b, c)) -> f b -> DivAp f c -> DivAp1 f a
pattern DivAp1 f g x xs <- (coerce splitChain1->Day x xs f g)
  where
    DivAp1 f g x xs = unsplitNE $ Day x xs f g
{-# COMPLETE DivAp1 #-}

instance Invariant f => Inply (DivAp1 f) where
    gather = coerce (gather @(Chain1 Day _))

-- | Convenient wrapper to build up a 'DivAp' by providing each
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
--   assembleDivAp $ intPrim
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
assembleDivAp
    :: NP f as
    -> DivAp f (NP I as)
assembleDivAp = \case
    Nil     -> DivAp $ Done $ Identity Nil
    x :* xs -> DivAp $ More $ Day
      x
      (unDivAp (assembleDivAp xs))
      consNPI
      unconsNPI

-- | A version of 'assembleDivAp' where each component is itself
-- a 'DivAp'.
--
-- @
-- assembleDivAp (x :* y :* z :* Nil)
--   = concatDivAp (injectChain x :* injectChain y :* injectChain z :* Nil)
-- @
concatDivAp
    :: NP (DivAp f) as
    -> DivAp f (NP I as)
concatDivAp = \case
    Nil     -> DivAp $ Done $ Identity Nil
    x :* xs -> coerce appendChain $ Day
      x
      (concatDivAp xs)
      consNPI
      unconsNPI

-- | A version of 'assembleDivAp' but for 'DivAp1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Divise' or 'Apply' instance, but no 'Divisible' or 'Applicative'.
assembleDivAp1
    :: Invariant f
    => NP f (a ': as)
    -> DivAp1 f (NP I (a ': as))
assembleDivAp1 = \case
    x :* xs -> DivAp1_ $ case xs of
      Nil    -> Done1 $ invmap ((:* Nil) . I) (unI . hd) x
      _ :* _ -> More1 $ Day
        x
        (unDivAp1 (assembleDivAp1 xs))
        consNPI
        unconsNPI

-- | A version of 'concatDivAp' but for 'DivAp1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Divise' or 'Apply' instance, but no 'Divisible' or 'Applicative'.
concatDivAp1
    :: Invariant f
    => NP (DivAp1 f) (a ': as)
    -> DivAp1 f (NP I (a ': as))
concatDivAp1 = \case
    x :* xs -> case xs of
      Nil    -> invmap ((:* Nil) . I) (unI . hd) x
      _ :* _ -> coerce appendChain1 $ Day
        x
        (concatDivAp1 xs)
        consNPI
        unconsNPI

unconsNPI :: NP I (a ': as) -> (a, NP I as)
unconsNPI (I y :* ys) = (y, ys)

consNPI :: a -> NP I as -> NP I (a ': as)
consNPI y ys = I y :* ys

-- | A version of 'assembleDivAp' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
--
-- @
-- data MyType = MT Int Bool String
--
-- invmap (\(MyType x y z) -> x ::& y ::& z ::& RNil)
--        (\(x ::& y ::& z ::& RNil) -> MyType x y z) $
--   assembleDivApRec $ intPrim
--                      :& boolPrim
--                      :& stringPrim
--                      :& Nil
-- @
assembleDivApRec
    :: V.Rec f as
    -> DivAp f (V.XRec V.Identity as)
assembleDivApRec = \case
    V.RNil    -> DivAp $ Done $ Identity V.RNil
    x V.:& xs -> DivAp $ More $ Day
      x
      (unDivAp (assembleDivApRec xs))
      (V.::&)
      unconsRec

-- | A version of 'concatDivAp' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
concatDivApRec
    :: V.Rec (DivAp f) as
    -> DivAp f (V.XRec V.Identity as)
concatDivApRec = \case
    V.RNil    -> DivAp $ Done $ Identity V.RNil
    x V.:& xs -> coerce appendChain $ Day
      x
      (concatDivApRec xs)
      (V.::&)
      unconsRec

-- | A version of 'assembleDivAp1' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
assembleDivAp1Rec
    :: Invariant f
    => V.Rec f (a ': as)
    -> DivAp1 f (V.XRec V.Identity (a ': as))
assembleDivAp1Rec = \case
    x V.:& xs -> case xs of
      V.RNil   -> DivAp1_ $ Done1 $ invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
      _ V.:& _ -> DivAp1_ $ More1 $ Day
        x
        (unDivAp1 (assembleDivAp1Rec xs))
        (V.::&)
        unconsRec

-- | A version of 'concatDivAp1' using 'V.XRec' from /vinyl/ instead of
-- 'NP' from /sop-core/.  This can be more convenient because it doesn't
-- require manual unwrapping/wrapping of components.
concatDivAp1Rec
    :: Invariant f
    => V.Rec (DivAp1 f) (a ': as)
    -> DivAp1 f (V.XRec V.Identity (a ': as))
concatDivAp1Rec = \case
    x V.:& xs -> case xs of
      V.RNil   -> invmap (V.::& V.RNil) (\case z V.::& _ -> z) x
      _ V.:& _ -> coerce appendChain1 $ Day
        x
        (concatDivAp1Rec xs)
        (V.::&)
        unconsRec

unconsRec :: V.XRec V.Identity (a ': as) -> (a, V.XRec V.Identity as)
unconsRec (y V.::& ys) = (y, ys)
