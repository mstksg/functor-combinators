
module Data.Functor.Invariant.Night.Chain (
  -- * Chain
    NightChain
  , pattern Swerve, pattern Reject
  , runCoNightChain
  , runContraNightChain
  , chainListF
  , chainListF_
  , chainDec
  , swerve, swerved
  , assembleNightChain
  , concatNightChain
  -- * Nonempty Chain
  , NightChain1
  , pattern NightChain1
  , runCoNightChain1
  , runContraNightChain1
  , chainNonEmptyF
  , chainNonEmptyF_
  , chainDec1
  , swerve1, swerved1
  , assembleNightChain1
  , concatNightChain1
  ) where

import           Control.Applicative.ListF
import           Control.Natural
import           Data.Coerce
import           Data.Functor.Alt
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divisible.Free
import           Data.Functor.Invariant
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
runCoNightChain1
    :: forall f g. Alt g
    => f ~> g
    -> NightChain1 f ~> g
runCoNightChain1 f = foldChain1 f (runNightAlt f id)
                   . unNightChain1

-- | In the contravariant direction, we can interpret out of a 'Chain1' of
-- 'Night' into any 'Decide'.
runContraNightChain1
    :: forall f g. Decide g
    => f ~> g
    -> NightChain1 f ~> g
runContraNightChain1 f = foldChain1 f (runNightDecide f id)
                       . unNightChain1

-- | Extract the 'Dec' part out of a 'NightChain', shedding the
-- covariant bits.
chainDec :: NightChain f ~> Dec f
chainDec = runContraNightChain inject

-- | Extract the 'Dec1' part out of a 'NightChain1', shedding the
-- covariant bits.
chainDec1 :: NightChain1 f ~> Dec1 f
chainDec1 = runContraNightChain1 inject

-- | In the covariant direction, we can interpret out of a 'Chain' of 'Night'
-- into any 'Plus'.
runCoNightChain
    :: forall f g. Plus g
    => f ~> g
    -> NightChain f ~> g
runCoNightChain f = foldChain (const zero) (runNightAlt f id)
                  . unNightChain

-- | In the contravariant direction, we can interpret out of a 'Chain' of
-- 'Night' into any 'Conclude'.
runContraNightChain
    :: forall f g. Conclude g
    => f ~> g
    -> NightChain f ~> g
runContraNightChain f = foldChain (conclude . refute) (runNightDecide f id)
                      . unNightChain

-- | Extract the 'ListF' part out of a 'NightChain', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
chainListF :: Functor f => NightChain f ~> ListF f
chainListF = runCoNightChain inject

-- | Extract the 'ListF' part out of a 'NightChain', shedding the
-- contravariant bits.
--
-- This version does not require a 'Functor' constraint because it converts
-- to the coyoneda-wrapped product, which is more accurately the true
-- conversion to a covariant chain.
--
-- @since 0.3.2.0
chainListF_ :: NightChain f ~> CT.ComposeT ListF CY.Coyoneda f
chainListF_ = foldChain (const (CT.ComposeT (ListF []))) (\case
    Night x (CT.ComposeT (ListF xs)) _ f g -> CT.ComposeT . ListF $
      CY.Coyoneda f x : (map . fmap) g xs
    ) . unNightChain

-- | Extract the 'NonEmptyF' part out of a 'NightChain1', shedding the
-- contravariant bits.
--
-- @since 0.3.2.0
chainNonEmptyF :: Functor f => NightChain1 f ~> NonEmptyF f
chainNonEmptyF = runCoNightChain1 inject

-- | Extract the 'NonEmptyF' part out of a 'NightChain1', shedding the
-- contravariant bits.
--
-- This version does not require a 'Functor' constraint because it converts
-- to the coyoneda-wrapped product, which is more accurately the true
-- conversion to a covariant chain.
--
-- @since 0.3.2.0
chainNonEmptyF_ :: NightChain1 f ~> CT.ComposeT NonEmptyF CY.Coyoneda f
chainNonEmptyF_ = foldChain1 inject (\case
    Night x (CT.ComposeT (NonEmptyF xs)) _ f g -> CT.ComposeT . NonEmptyF $
      CY.Coyoneda f x NE.<| (fmap . fmap) g xs
    ) . unNightChain1


-- | Match on a non-empty 'NightChain'; contains the splitting function,
-- the two rejoining functions, the first @f@, and the rest of the chain.
-- Analogous to the 'Data.Functor.Contravariant.Divisible.Free.Choose'
-- constructor.
pattern Swerve :: (a -> Either b c) -> (b -> a) -> (c -> a) -> f b -> NightChain f c -> NightChain f a
pattern Swerve f g h x xs <- (unSwerve_->MaybeF (Just (Night x xs f g h)))
  where
    Swerve f g h x xs = NightChain $ More $ Night x (unNightChain xs) f g h

unSwerve_ :: NightChain f ~> MaybeF (Night f (NightChain f))
unSwerve_ = \case
  NightChain (More (Night x xs g f h)) -> MaybeF . Just $ Night x (NightChain xs) g f h
  NightChain (Done _                 ) -> MaybeF Nothing


-- | Match on an "empty" 'NightChain'; contains no @f@s, but only the
-- terminal value.  Analogous to the
-- 'Data.Functor.Contravariant.Divisible.Free.Lose' constructor.
pattern Reject :: (a -> Void) -> NightChain f a
pattern Reject x = NightChain (Done (Not x))
{-# COMPLETE Swerve, Reject #-}

-- | Match on a 'NightChain1' to get the head and the rest of the items.
-- Analogous to the 'Data.Functor.Contravariant.Divisible.Free.Dec1'
-- constructor.
pattern NightChain1 :: Invariant f => (a -> Either b c) -> (b -> a) -> (c -> a) -> f b -> NightChain f c -> NightChain1 f a
pattern NightChain1 f g h x xs <- (coerce splitChain1->Night x xs f g h)
  where
    NightChain1 f g h x xs = unsplitNE $ Night x xs f g h
{-# COMPLETE NightChain1 #-}

-- | Invariantly combine two 'NightChain's.
--
-- Analogous to '<|>' and 'decide'.  If there was some typeclass that
-- represented semigroups on invariant 'Night', this would be the method of that
-- typeclass.
--
-- The identity of this is 'Reject'.
--
-- @since 0.3.4.0
swerve
    :: (a -> Either b c)
    -> (b -> a)
    -> (c -> a)
    -> NightChain f b
    -> NightChain f c
    -> NightChain f a
swerve f g h x y = coerce appendChain (Night x y f g h)

-- | Convenient wrapper over 'swerve' that simply combines the two options
-- in an 'Either'.  Analogous to '<|>' and 'decided'.
--
-- @since 0.3.4.0
swerved
    :: NightChain f a
    -> NightChain f b
    -> NightChain f (Either a b)
swerved = swerve id Left Right

-- | Invariantly combine two 'NightChain1's.
--
-- Analogous to '<|>' and 'decide'.  If there was some typeclass that
-- represented semigroups on invariant 'Night', this would be the method of that
-- typeclass.
--
-- @since 0.3.4.0
swerve1
    :: Invariant f
    => (a -> Either b c)
    -> (b -> a)
    -> (c -> a)
    -> NightChain1 f b
    -> NightChain1 f c
    -> NightChain1 f a
swerve1 f g h x y = coerce appendChain1 (Night x y f g h)

-- | Convenient wrapper over 'swerve1' that simply combines the two options
-- in an 'Either'.  Analogous to '<|>' and 'decided'.
--
-- @since 0.3.4.0
swerved1
    :: Invariant f
    => NightChain1 f a
    -> NightChain1 f b
    -> NightChain1 f (Either a b)
swerved1 = swerve1 id Left Right

-- | Convenient wrapper to build up a 'NightChain' on by providing each
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
--   assembleNightChain $ intPrim
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
assembleNightChain
    :: NP f as
    -> NightChain f (NS I as)
assembleNightChain = \case
    Nil     -> NightChain $ Done $ Not (\case {})
    x :* xs -> NightChain $ More $ Night
      x
      (unNightChain $ assembleNightChain xs)
      unconsNSI
      (Z . I)
      S

-- | A version of 'assembleNightChain' where each component is itself
-- a 'NightChain'.
--
-- @
-- assembleNightChain (x :* y :* z :* Nil)
--   = concatNightChain (injectChain x :* injectChain y :* injectChain z :* Nil)
-- @
concatNightChain
    :: NP (NightChain f) as
    -> NightChain f (NS I as)
concatNightChain = \case
    Nil     -> NightChain $ Done $ Not (\case {})
    x :* xs -> coerce appendChain $ Night
      x
      (unNightChain $ concatNightChain xs)
      unconsNSI
      (Z . I)
      S

-- | A version of 'assembleNightChain' but for 'NightChain1' instead.  Can
-- be useful if you intend on interpreting it into something with only
-- a 'Decide' or 'Alt' instance, but no
-- 'Data.Functor.Contravariant.Divisible.Decidable' or 'Plus' or
-- 'Control.Applicative.Alternative'.
assembleNightChain1
    :: Invariant f
    => NP f (a ': as)
    -> NightChain1 f (NS I (a ': as))
assembleNightChain1 = \case
    x :* xs -> NightChain1_ $ case xs of
      Nil    -> Done1 $ invmap (Z . I) (unI . unZ) x
      _ :* _ -> More1 $ Night
        x
        (unNightChain1 $ assembleNightChain1 xs)
        unconsNSI
        (Z . I)
        S

-- | A version of 'concatNightChain' but for 'NightChain1' instead.  Can be
-- useful if you intend on interpreting it into something with only
-- a 'Decide' or 'Alt' instance, but no
-- 'Data.Functor.Contravariant.Divisible.Decidable' or 'Plus' or
-- 'Control.Applicative.Alternative'.
concatNightChain1
    :: Invariant f
    => NP (NightChain1 f) (a ': as)
    -> NightChain1 f (NS I (a ': as))
concatNightChain1 = \case
    x :* xs -> case xs of
      Nil    -> invmap (Z . I) (unI . unZ) x
      _ :* _ -> coerce appendChain1 $ Night
        x
        (unNightChain1 $ concatNightChain1 xs)
        unconsNSI
        (Z . I)
        S

unconsNSI :: NS I (a ': as) -> Either a (NS I as)
unconsNSI = \case
  Z (I x) -> Left x
  S xs    -> Right xs
