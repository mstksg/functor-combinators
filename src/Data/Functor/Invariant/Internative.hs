{-# LANGUAGE DerivingVia #-}

-- |
-- Module      : Data.Functor.Invariant.Internative
-- Copyright   : (c) Justin Le 2021
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Contains the classes 'Inalt' and 'Inplus', the invariant
-- counterparts to 'Alt'/'Plus' and 'Decide'/'Conclude' and
-- 'Alternative'/'Decidable'.
--
-- @since 0.4.0.0
module Data.Functor.Invariant.Internative (
  -- * Typeclass
    Inalt(..)
  , Inplus(..)
  , Internative
  -- * Assembling Helpers
  , swervedN
  , swervedNMap
  , swervedN1
  , swervedN1Map
  ) where

import           Control.Applicative
import           Control.Applicative.Backwards        (Backwards(..))
import           Control.Arrow                        (ArrowPlus)
import           Control.Monad
import           Control.Monad.Trans.Identity         (IdentityT(..))
import           Data.Functor.Alt
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Invariant
import           Data.Functor.Invariant.Inplicative
import           Data.Functor.Plus
import           Data.Functor.Product                 (Product(..))
import           Data.Functor.Reverse                 (Reverse(..))
import           Data.Hashable                        (Hashable)
import           Data.Kind
import           Data.List.NonEmpty                   (NonEmpty)
import           Data.SOP hiding                      (hmap)
import           Data.Sequence                        (Seq)
import           Data.StateVar                        (SettableStateVar)
import           Data.Void
import qualified Data.HashMap.Lazy                    as HM
import qualified Data.IntMap                          as IM
import qualified Data.IntMap.NonEmpty                 as NEIM
import qualified Data.Map                             as M
import qualified Data.Map.NonEmpty                    as NEM
import qualified Data.Monoid                          as Monoid
import qualified Data.Semigroup                       as Semigroup
import qualified Data.Sequence.NonEmpty               as NESeq
import qualified GHC.Generics                         as Generics

-- | The invariant counterpart of 'Alt' and 'Decide'.
--
-- Conceptually you can think of 'Alt' as, given a way to "inject" @a@ and
-- @b@ as @c@, lets you merge @f a@ (producer of @a@) and @f b@ (producer
-- of @b@) into a @f c@ (producer of @c@), in an "either-or" fashion.
-- 'Decide' can be thought of as, given a way to "discriminate" a @c@ as
-- either a @a@ or a @b@, lets you merge @f a@ (consumer of @a@) and @f b@
-- (consumder of @b@) into a @f c@ (consumer of @c@) in an "either-or"
-- forking fashion (split the @c@ into @a@ or @b@, and use the appropriate
-- handler).
--
-- 'Inalt', for 'swerve', requires both an injecting function and
-- a choosing function in order to merge @f b@ (producer and consumer of
-- @b@) and @f c@ (producer and consumer of @c@) into a @f a@ in an
-- either-or manner.  You can think of it as, for the @f a@, it "chooses"
-- if the @a@ is actually a @b@ or a @c@ with the @a -> 'Either' b c@,
-- feeds it to either the original @f b@ or the original @f c@, and then
-- re-injects the output back into a @a@ with the @b -> a@ or the @c -> a@.
--
-- @since 0.4.0.0
class Invariant f => Inalt f where
    -- | Like '<!>', 'decide', or 'choose', but requires both
    -- an injecting and a choosing function.
    --
    -- It is used to merge @f b@ (producer and consumer of @b@) and @f c@
    -- (producer and consumer of @c@) into a @f a@ in an either-or manner.
    -- You can think of it as, for the @f a@, it "chooses" if the @a@ is
    -- actually a @b@ or a @c@ with the @a -> 'Either' b c@, feeds it to
    -- either the original @f b@ or the original @f c@, and then re-injects
    -- the output back into a @a@ with the @b -> a@ or the @c -> a@.
    --
    -- An important property is that it will only ever use exactly @one@ of
    -- the options given in order to fulfil its job.  If you swerve an @f
    -- a@ and an @f b@ into an @f c@, in order to consume/produdce the @c@,
    -- it will only use either the @f a@ or the @f b@ -- exactly one of
    -- them.
    --
    -- @since 0.4.0.0
    swerve
        :: (b -> a)
        -> (c -> a)
        -> (a -> Either b c)
        -> f b
        -> f c
        -> f a
    swerve f g h x y = invmap (either f g) h (swerved x y)
    -- | A simplified version of 'swerive' that splits to and from an
    -- 'Either'. You can then use 'invmap' to reshape it into the proper
    -- shape.
    --
    -- @since 0.4.0.0
    swerved
        :: f a
        -> f b
        -> f (Either a b)
    swerved = swerve Left Right id
    {-# MINIMAL swerve | swerved #-}

-- | The invariant counterpart of 'Alt' and 'Conclude'.
--
-- The main important action is described in 'Inalt', but this adds 'reject',
-- which is the counterpart to 'empty' and 'conclude' and 'conquer'.  It's the identity to
-- 'swerve'; if combine two @f a@s with 'swerve', and one of them is
-- 'reject', then that banch will never be taken.
--
-- Conceptually, if you think of 'swerve' as "choosing one path and
-- re-injecting back", then 'reject' introduces a branch that is impossible
-- to take.

-- @since 0.4.0.0
class Inalt f => Inplus f where
    reject :: (a -> Void) -> f a

-- | The invariant counterpart to 'Alternative' and 'Decidable': represents
-- a combination of both 'Applicative' and 'Alt', or 'Divisible' and
-- 'Conclude'.  There are laws?

-- @since 0.4.0.0
class (Inplus f, Inplicative f) => Internative f

-- | Ignores the contravariant part of 'swerve'
instance Alt f => Inalt (WrappedFunctor f) where
    swerved (WrapFunctor x) (WrapFunctor y) = WrapFunctor $
        (Left <$> x) <!> (Right <$> y)
-- | @'reject' _ = 'zero'@
instance Plus f => Inplus (WrappedFunctor f) where
    reject _ = WrapFunctor zero
instance (Alternative f, Plus f, Apply f) => Internative (WrappedFunctor f)

-- | Ignores the covariant part of 'gather'
instance Decide f => Inalt (WrappedContravariant f) where
    swerve _ _ h (WrapContravariant x) (WrapContravariant y) = WrapContravariant (decide h x y)
-- | @'reject' = 'conclude'@
instance Conclude f => Inplus (WrappedContravariant f) where
    reject f = WrapContravariant (conclude f)
instance (Conclude f, Divisible f, Divise f) => Internative (WrappedContravariant f)

-- | Ignores the covariant part of 'gather'
instance Decide f => Inalt (WrappedDivisible f) where
    swerve _ _ h (WrapDivisible x) (WrapDivisible y) = WrapDivisible (decide h x y)
-- | @'reject' = 'conclude'@
instance Conclude f => Inplus (WrappedDivisible f) where
    reject f = WrapDivisible (conclude f)
instance (Conclude f, Divisible f, Divise f) => Internative (WrappedDivisible f)

-- | Ignores the covariant part of 'gather'
instance (Decidable f, Invariant f) => Inalt (WrappedDivisibleOnly f) where
    swerve _ _ h (WrapDivisibleOnly x) (WrapDivisibleOnly y) = WrapDivisibleOnly (choose h x y)
-- | @'reject' = 'lose'@
instance (Decidable f, Invariant f) => Inplus (WrappedDivisibleOnly f) where
    reject f = WrapDivisibleOnly (lose f)
instance (Decidable f, Invariant f) => Internative (WrappedDivisibleOnly f)

-- | @since 0.4.1.0
deriving via WrappedFunctor (Proxy :: Type -> Type) instance Inalt Proxy
-- | @since 0.4.1.0
deriving via WrappedFunctor (Proxy :: Type -> Type) instance Inplus Proxy
-- | @since 0.4.1.0
deriving via WrappedFunctor (Proxy :: Type -> Type) instance Internative Proxy
-- | @since 0.4.1.0
deriving via WrappedFunctor [] instance Inalt []
-- | @since 0.4.1.0
deriving via WrappedFunctor [] instance Inplus []
-- | @since 0.4.1.0
deriving via WrappedFunctor [] instance Internative []
-- | @since 0.4.1.0
deriving via WrappedFunctor Maybe instance Inalt Maybe
-- | @since 0.4.1.0
deriving via WrappedFunctor Maybe instance Inplus Maybe
-- | @since 0.4.1.0
deriving via WrappedFunctor Maybe instance Internative Maybe
-- | @since 0.4.1.0
deriving via WrappedFunctor (Either e) instance Inalt (Either e)
-- | @since 0.4.1.0
deriving via WrappedFunctor IO instance Inalt IO
-- | @since 0.4.1.0
deriving via WrappedFunctor IO instance Inplus IO
-- | @since 0.4.1.0
deriving via WrappedFunctor IO instance Internative IO

-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.U1 :: Type -> Type) instance Inalt Generics.U1
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.U1 :: Type -> Type) instance Inplus Generics.U1
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.U1 :: Type -> Type) instance Internative Generics.U1

-- | @since 0.4.1.0
instance Inalt f => Inalt (Generics.M1 i t f) where
    swerve f g h (Generics.M1 x) (Generics.M1 y) = Generics.M1 (swerve f g h x y)
-- | @since 0.4.1.0
instance Inplus f => Inplus (Generics.M1 i t f) where
    reject = Generics.M1 . reject
-- | @since 0.4.1.0
instance Internative f => Internative (Generics.M1 i t f)

-- | @since 0.4.1.0
instance (Inalt f, Inalt g) => Inalt (f Generics.:*: g) where
    swerve f g h (x1 Generics.:*: y1) (x2 Generics.:*: y2) =
        swerve f g h x1 x2 Generics.:*: swerve f g h y1 y2
-- | @since 0.4.1.0
instance (Inplus f, Inplus g) => Inplus (f Generics.:*: g) where
    reject f = reject f Generics.:*: reject f
-- | @since 0.4.1.0
instance (Internative f, Internative g) => Internative (f Generics.:*: g)

-- | @since 0.4.1.0
instance (Inalt f, Inalt g) => Inalt (Product f g) where
    swerve f g h (Pair x1 y1) (Pair x2 y2) =
        swerve f g h x1 x2 `Pair` swerve f g h y1 y2
-- | @since 0.4.1.0
instance (Inplus f, Inplus g) => Inplus (Product f g) where
    reject f = reject f `Pair` reject f
-- | @since 0.4.1.0
instance (Internative f, Internative g) => Internative (Product f g)

-- | @since 0.4.1.0
instance Inalt f => Inalt (Generics.Rec1 f) where
    swerve f g h (Generics.Rec1 x) (Generics.Rec1 y) = Generics.Rec1 (swerve f g h x y)
-- | @since 0.4.1.0
instance Inplus f => Inplus (Generics.Rec1 f) where
    reject = Generics.Rec1 . reject
-- | @since 0.4.1.0
instance Internative f => Internative (Generics.Rec1 f)

-- | @since 0.4.1.0
instance Inalt f => Inalt (IdentityT f) where
    swerve f g h (IdentityT x) (IdentityT y) = IdentityT (swerve f g h x y)
-- | @since 0.4.1.0
instance Inplus f => Inplus (IdentityT f) where
    reject = IdentityT . reject
-- | @since 0.4.1.0
instance Internative f => Internative (IdentityT f) where

-- | @since 0.4.1.0
instance Inalt f => Inalt (Reverse f) where
    swerve f g h (Reverse x) (Reverse y) = Reverse (swerve f g h x y)
-- | @since 0.4.1.0
instance Inplus f => Inplus (Reverse f) where
    reject = Reverse . reject
-- | @since 0.4.1.0
instance Internative f => Internative (Reverse f) where

-- | @since 0.4.1.0
instance Inalt f => Inalt (Backwards f) where
    swerve f g h (Backwards x) (Backwards y) = Backwards (swerve f g h x y)
-- | @since 0.4.1.0
instance Inplus f => Inplus (Backwards f) where
    reject = Backwards . reject
-- | @since 0.4.1.0
instance Internative f => Internative (Backwards f) where

-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.First instance Inalt Semigroup.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Last instance Inalt Semigroup.Last
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Option instance Inalt Semigroup.Option
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Option instance Inplus Semigroup.Option
-- | @since 0.4.1.0
deriving via WrappedFunctor Semigroup.Option instance Internative Semigroup.Option
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.First instance Inalt Monoid.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.First instance Inplus Monoid.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.First instance Internative Monoid.First
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Last instance Inalt Monoid.Last
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Last instance Inplus Monoid.Last
-- | @since 0.4.1.0
deriving via WrappedFunctor Monoid.Last instance Internative Monoid.Last
-- | @since 0.4.1.0
deriving via WrappedFunctor NonEmpty instance Inalt NonEmpty
-- | @since 0.4.1.0
deriving via WrappedFunctor Seq instance Inalt Seq
-- | @since 0.4.1.0
deriving via WrappedFunctor Seq instance Inplus Seq
-- | @since 0.4.1.0
deriving via WrappedFunctor Seq instance Internative Seq
-- | @since 0.4.1.0
deriving via WrappedFunctor NESeq.NESeq instance Inalt NESeq.NESeq
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedArrow a b) instance ArrowPlus a => Inalt (WrappedArrow a b)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedArrow a b) instance ArrowPlus a => Inplus (WrappedArrow a b)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedArrow a b) instance ArrowPlus a => Internative (WrappedArrow a b)
-- | @since 0.4.1.0
deriving via WrappedFunctor (Generics.V1 :: Type -> Type) instance Inalt Generics.V1
-- | @since 0.4.1.0
deriving via WrappedFunctor IM.IntMap instance Inalt IM.IntMap
-- | @since 0.4.1.0
deriving via WrappedFunctor NEIM.NEIntMap instance Inalt NEIM.NEIntMap
-- | @since 0.4.1.0
deriving via WrappedFunctor (M.Map k) instance Ord k => Inalt (M.Map k)
-- | @since 0.4.1.0
deriving via WrappedFunctor (NEM.NEMap k) instance Ord k => Inalt (NEM.NEMap k)
-- | @since 0.4.1.0
deriving via WrappedFunctor (HM.HashMap k) instance (Hashable k, Eq k) => Inalt (HM.HashMap k)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedMonad m) instance MonadPlus m => Inalt (WrappedMonad m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedMonad m) instance MonadPlus m => Inplus (WrappedMonad m)
-- | @since 0.4.1.0
deriving via WrappedFunctor (WrappedMonad m) instance MonadPlus m => Internative (WrappedMonad m)

-- | @since 0.4.1.0
deriving via WrappedDivisible SettableStateVar instance Inalt SettableStateVar
-- | @since 0.4.1.0
deriving via WrappedDivisible SettableStateVar instance Inplus SettableStateVar
-- | @since 0.4.1.0
deriving via WrappedDivisible SettableStateVar instance Internative SettableStateVar
-- | @since 0.4.1.0
deriving via WrappedDivisible Predicate instance Inalt Predicate
-- | @since 0.4.1.0
deriving via WrappedDivisible Predicate instance Inplus Predicate
-- | @since 0.4.1.0
deriving via WrappedDivisible Predicate instance Internative Predicate
-- | @since 0.4.1.0
deriving via WrappedDivisible Comparison instance Inalt Comparison
-- | @since 0.4.1.0
deriving via WrappedDivisible Comparison instance Inplus Comparison
-- | @since 0.4.1.0
deriving via WrappedDivisible Comparison instance Internative Comparison
-- | @since 0.4.1.0
deriving via WrappedDivisible Equivalence instance Inalt Equivalence
-- | @since 0.4.1.0
deriving via WrappedDivisible Equivalence instance Inplus Equivalence
-- | @since 0.4.1.0
deriving via WrappedDivisible Equivalence instance Internative Equivalence
-- | @since 0.4.1.0
deriving via WrappedDivisible (Op r) instance Inalt (Op r)
-- | @since 0.4.1.0
deriving via WrappedDivisible (Op r) instance Inplus (Op r)
-- | @since 0.4.1.0
deriving via WrappedDivisible (Op r) instance Monoid r => Internative (Op r)



-- | Convenient wrapper to build up an 'Inplus' instance on by providing
-- each branch of it.  This makes it much easier to build up longer chains
-- because you would only need to write the splitting/joining functions in
-- one place.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MTI Int | MTB Bool | MTS String
-- @
--
-- and an invariant functor and 'Inplus' instance @Prim@ (representing, say,
-- a bidirectional parser, where @Prim Int@ is a bidirectional parser for
-- an 'Int'@), then you could assemble a bidirectional parser for
-- a @MyType@ using:
--
-- @
-- invmap (\case MTI x -> Z (I x); MTB y -> S (Z (I y)); MTS z -> S (S (Z (I z))))
--        (\case Z (I x) -> MTI x; S (Z (I y)) -> MTB y; S (S (Z (I z))) -> MTS z) $
--   swervedN $ intPrim
--               :* boolPrim
--               :* stringPrim
--               :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'reject' directly.
-- *    If you have 1 component, use 'inject' directly.
-- *    If you have 2 components, use 'swerve' directly.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off eithers one-by-one.
--
-- @since 0.4.1.0
swervedN
    :: Inplus f
    => NP f as
    -> f (NS I as)
swervedN = \case
    Nil     -> reject $ \case {}
    x :* xs -> swerve
      (Z . I)
      S
      (\case Z (I y) -> Left y; S ys -> Right ys)
      x
      (swervedN xs)

-- | Given a function to "discern out" a data type into possible 'NS'
-- (multi-way Either) branches and one to re-assemble each brann, 'swerve'
-- all of the components together.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MTI Int | MTB Bool | MTS String
-- @
--
-- and an invariant functor and 'Inplus' instance @Prim@ (representing, say,
-- a bidirectional parser, where @Prim Int@ is a bidirectional parser for
-- an 'Int'@), then you could assemble a bidirectional parser for
-- a @MyType@ using:
--
-- @
-- swervedNMap
--      (\case MTI x -> Z (I x); MTB y -> S (Z (I y)); MTS z -> S (S (Z (I z))))
--      (\case Z (I x) -> MTI x; S (Z (I y)) -> MTB y; S (S (Z (I z))) -> MTS z) $
--      $ intPrim
--     :* boolPrim
--     :* stringPrim
--     :* Nil
-- @
--
-- Some notes on usefulness depending on how many components you have:
--
-- *    If you have 0 components, use 'reject' directly.
-- *    If you have 1 component, you don't need anything.
-- *    If you have 2 components, use 'swerve' directly.
-- *    If you have 3 or more components, these combinators may be useful;
--      otherwise you'd need to manually peel off eithers one-by-one.
--
-- See notes on 'swervedNMap' for more details and caveats.
--
-- @since 0.4.1.0
swervedNMap
    :: Inplus f
    => (NS I as -> b)
    -> (b -> NS I as)
    -> NP f as
    -> f b
swervedNMap f g = invmap f g . swervedN

-- | A version of 'swervedN' for non-empty 'NP', but only
-- requiring an 'Inalt' instance.
--
-- @since 0.4.1.0
swervedN1
    :: Inalt f
    => NP f (a ': as)
    -> f (NS I (a ': as))
swervedN1 (x :* xs) = case xs of
    Nil    -> invmap (Z . I) (\case Z (I y) -> y; S ys -> case ys of {}) x
    _ :* _ -> swerve
      (Z . I)
      S
      (\case Z (I y) -> Left y; S ys -> Right ys)
      x
      (swervedN1 xs)

-- | A version of 'swervedNMap' for non-empty 'NS', but only
-- requiring an 'Inalt' instance.
--
-- @since 0.4.1.0
swervedN1Map
    :: Inalt f
    => (NS I (a ': as) -> b)
    -> (b -> NS I (a ': as))
    -> NP f (a ': as)
    -> f b
swervedN1Map f g = invmap f g . swervedN1

