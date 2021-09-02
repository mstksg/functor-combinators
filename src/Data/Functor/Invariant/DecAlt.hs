{-# OPTIONS_GHC -fno-warn-orphans #-}

-- |
-- Module      : Data.Functor.Invariant.DecAlt
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Provide an invariant functor combinator choice-collector, like a combination of
-- 'ListF' and 'Dec'.
--
-- @since 0.3.5.0
module Data.Functor.Invariant.DecAlt (
  -- * Chain
    DecAlt(.., Swerve, Reject)
  , runCoDecAlt
  , runContraDecAlt
  , decAltListF
  , decAltListF_
  , decAltDec
  , foldDecAlt
  , assembleDecAlt
  , concatDecAlt
  -- * Nonempty Chain
  , DecAlt1(.., DecAlt1)
  , runCoDecAlt1
  , runContraDecAlt1
  , decAltNonEmptyF
  , decAltNonEmptyF_
  , decAltDec1
  , foldDecAlt1
  , assembleDecAlt1
  , concatDecAlt1
  ) where

import           Control.Applicative.ListF
import           Control.Natural
import           Data.Coerce
import           Data.Functor.Alt
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible.Free
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Internative
import           Data.Functor.Invariant.Night
import           Data.Functor.Plus
import           Data.HBifunctor.Tensor hiding             (elim1, elim2, intro1, intro2)
import           Data.HFunctor
import           Data.HFunctor.Chain
import           Data.HFunctor.Chain.Internal
import           Data.SOP
import           Data.Void
import qualified Control.Monad.Trans.Compose               as CT
import qualified Data.Functor.Coyoneda                     as CY
import qualified Data.List.NonEmpty                        as NE


-- | In the covariant direction, we can interpret out of a 'Chain1' of 'Night'
-- into any 'Alt'.
runCoDecAlt1
    :: forall f g. Alt g
    => f ~> g
    -> DecAlt1 f ~> g
runCoDecAlt1 f = foldDecAlt1 f (runNightAlt f id)

-- | In the contravariant direction, we can interpret out of a 'Chain1' of
-- 'Night' into any 'Decide'.
runContraDecAlt1
    :: forall f g. Decide g
    => f ~> g
    -> DecAlt1 f ~> g
runContraDecAlt1 f = foldDecAlt1 f (runNightDecide f id)

-- | Extract the 'Dec' part out of a 'DecAlt', shedding the
-- covariant bits.
decAltDec :: DecAlt f ~> Dec f
decAltDec = runContraDecAlt inject

-- | Extract the 'Dec1' part out of a 'DecAlt1', shedding the
-- covariant bits.
decAltDec1 :: DecAlt1 f ~> Dec1 f
decAltDec1 = runContraDecAlt1 inject

-- | In the covariant direction, we can interpret out of a 'Chain' of 'Night'
-- into any 'Plus'.
runCoDecAlt
    :: forall f g. Plus g
    => f ~> g
    -> DecAlt f ~> g
runCoDecAlt f = foldDecAlt (const zero) (runNightAlt f id)

-- | In the contravariant direction, we can interpret out of a 'Chain' of
-- 'Night' into any 'Conclude'.
runContraDecAlt
    :: forall f g. Conclude g
    => f ~> g
    -> DecAlt f ~> g
runContraDecAlt f = foldDecAlt conclude (runNightDecide f id)

-- | Extract the 'ListF' part out of a 'DecAlt', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
decAltListF :: Functor f => DecAlt f ~> ListF f
decAltListF = runCoDecAlt inject

-- | Extract the 'ListF' part out of a 'DecAlt', shedding the
-- contravariant bits.
--
-- This version does not require a 'Functor' constraint because it converts
-- to the coyoneda-wrapped product, which is more accurately the true
-- conversion to a covariant chain.
--
-- @since 0.3.2.0
decAltListF_ :: DecAlt f ~> CT.ComposeT ListF CY.Coyoneda f
decAltListF_ = foldDecAlt (const (CT.ComposeT (ListF []))) $ \case
    Night x (CT.ComposeT (ListF xs)) f g _ -> CT.ComposeT . ListF $
      CY.Coyoneda f x : (map . fmap) g xs

-- | Extract the 'NonEmptyF' part out of a 'DecAlt1', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
decAltNonEmptyF :: Functor f => DecAlt1 f ~> NonEmptyF f
decAltNonEmptyF = runCoDecAlt1 inject

-- | Extract the 'NonEmptyF' part out of a 'DecAlt1', shedding the
-- contravariant bits.
--
-- This version does not require a 'Functor' constraint because it converts
-- to the coyoneda-wrapped product, which is more accurately the true
-- conversion to a covariant chain.
--
-- @since 0.3.2.0
decAltNonEmptyF_ :: DecAlt1 f ~> CT.ComposeT NonEmptyF CY.Coyoneda f
decAltNonEmptyF_ = foldDecAlt1 inject $ \case
    Night x (CT.ComposeT (NonEmptyF xs)) f g _ -> CT.ComposeT . NonEmptyF $
      CY.Coyoneda f x NE.<| (fmap . fmap) g xs

-- | General-purpose folder of 'DecAlt'.  Provide a way to handle the
-- identity ('empty'/'conclude'/'Reject') and a way to handle a cons
-- ('<!>'/'decide'/'swerve').
--
-- @since 0.3.5.0
foldDecAlt
    :: (forall x. (x -> Void) -> g x)
    -> (Night f g ~> g)
    -> DecAlt f ~> g
foldDecAlt f g = foldChain (f . refute) g . unDecAlt

-- | General-purpose folder of 'DecAlt1'.  Provide a way to handle the
-- individual leaves and a way to handle a cons ('<!>'/'decide'/'swerve1').
--
-- @since 0.3.5.0
foldDecAlt1
    :: (f ~> g)
    -> (Night f g ~> g)
    -> DecAlt1 f ~> g
foldDecAlt1 f g = foldChain1 f g . unDecAlt1

-- | Match on a non-empty 'DecAlt'; contains the splitting function,
-- the two rejoining functions, the first @f@, and the rest of the chain.
-- Analogous to the 'Data.Functor.Contravariant.Divisible.Free.Choose'
-- constructor.
pattern Swerve :: (b -> a) -> (c -> a) -> (a -> Either b c) -> f b -> DecAlt f c -> DecAlt f a
pattern Swerve f g h x xs <- (unSwerve_->MaybeF (Just (Night x xs f g h)))
  where
    Swerve f g h x xs = DecAlt $ More $ Night x (unDecAlt xs) f g h

unSwerve_ :: DecAlt f ~> MaybeF (Night f (DecAlt f))
unSwerve_ = \case
  DecAlt (More (Night x xs g f h)) -> MaybeF . Just $ Night x (DecAlt xs) g f h
  DecAlt (Done _                 ) -> MaybeF Nothing


-- | Match on an "empty" 'DecAlt'; contains no @f@s, but only the
-- terminal value.  Analogous to the
-- 'Data.Functor.Contravariant.Divisible.Free.Lose' constructor.
pattern Reject :: (a -> Void) -> DecAlt f a
pattern Reject x = DecAlt (Done (Not x))
{-# COMPLETE Swerve, Reject #-}

instance Inalt (DecAlt f) where
    swerve = coerce (swerve @(Chain Night Not _))

instance Inplus (DecAlt f) where
    reject = coerce (reject @(Chain Night Not _))

-- | Match on a 'DecAlt1' to get the head and the rest of the items.
-- Analogous to the 'Data.Functor.Contravariant.Divisible.Free.Dec1'
-- constructor.
pattern DecAlt1 :: Invariant f => (b -> a) -> (c -> a) -> (a -> Either b c) -> f b -> DecAlt f c -> DecAlt1 f a
pattern DecAlt1 f g h x xs <- (coerce splitChain1->Night x xs f g h)
  where
    DecAlt1 f g h x xs = unsplitNE $ Night x xs f g h
{-# COMPLETE DecAlt1 #-}

instance Invariant f => Inalt (DecAlt1 f) where
    swerve = coerce (swerve @(Chain1 Night _))

-- | Convenient wrapper to build up a 'DecAlt' on by providing each
-- component of it.  This makes it much easier to build up longer chains
-- because you would only need to write the splitting/joining functions in
-- one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MTI Int | MTB Bool | MTS String
-- @
--
-- and an invariant functor @Prim@ (representing, say, a bidirectional
-- parser, where @Prim Int@ is a bidirectional parser for an 'Int'@),
-- then you could assemble a bidirectional parser for a @MyType@ using:
--
-- @
-- invmap (\case MTI x -> Z (I x); MTB y -> S (Z (I y)); MTS z -> S (S (Z (I z))))
--        (\case Z (I x) -> MTI x; S (Z (I y)) -> MTB y; S (S (Z (I z))) -> MTS z) $
--   assembleDecAlt $ intPrim
--                     :* boolPrim
--                     :* stringPrim
--                     :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'Reject' directly.
-- *    If you have 1 component, use 'inject' or 'injectChain' directly.
-- *    If you have 2 components, use 'toListBy' or 'toChain'.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off eithers one-by-one.
assembleDecAlt
    :: NP f as
    -> DecAlt f (NS I as)
assembleDecAlt = \case
    Nil     -> DecAlt $ Done $ Not (\case {})
    x :* xs -> DecAlt $ More $ Night
      x
      (unDecAlt $ assembleDecAlt xs)
      (Z . I)
      S
      unconsNSI

-- | A version of 'assembleDecAlt' where each component is itself
-- a 'DecAlt'.
--
-- @
-- assembleDecAlt (x :* y :* z :* Nil)
--   = concatDecAlt (injectChain x :* injectChain y :* injectChain z :* Nil)
-- @
concatDecAlt
    :: NP (DecAlt f) as
    -> DecAlt f (NS I as)
concatDecAlt = \case
    Nil     -> DecAlt $ Done $ Not (\case {})
    x :* xs -> coerce appendChain $ Night
      x
      (unDecAlt $ concatDecAlt xs)
      (Z . I)
      S
      unconsNSI

-- | A version of 'assembleDecAlt' but for 'DecAlt1' instead.  Can
-- be useful if you intend on interpreting it into something with only
-- a 'Decide' or 'Alt' instance, but no
-- 'Data.Functor.Contravariant.Divisible.Decidable' or 'Plus' or
-- 'Control.Applicative.Alternative'.
assembleDecAlt1
    :: Invariant f
    => NP f (a ': as)
    -> DecAlt1 f (NS I (a ': as))
assembleDecAlt1 = \case
    x :* xs -> DecAlt1_ $ case xs of
      Nil    -> Done1 $ invmap (Z . I) (unI . unZ) x
      _ :* _ -> More1 $ Night
        x
        (unDecAlt1 $ assembleDecAlt1 xs)
        (Z . I)
        S
        unconsNSI

-- | A version of 'concatDecAlt' but for 'DecAlt1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Decide' or 'Alt' instance, but no
-- 'Data.Functor.Contravariant.Divisible.Decidable' or 'Plus' or
-- 'Control.Applicative.Alternative'.
concatDecAlt1
    :: Invariant f
    => NP (DecAlt1 f) (a ': as)
    -> DecAlt1 f (NS I (a ': as))
concatDecAlt1 = \case
    x :* xs -> case xs of
      Nil    -> invmap (Z . I) (unI . unZ) x
      _ :* _ -> coerce appendChain1 $ Night
        x
        (unDecAlt1 $ concatDecAlt1 xs)
        (Z . I)
        S
        unconsNSI

unconsNSI :: NS I (a ': as) -> Either a (NS I as)
unconsNSI = \case
  Z (I x) -> Left x
  S xs    -> Right xs
