{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE ConstraintKinds            #-}
{-# LANGUAGE DefaultSignatures          #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
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
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TupleSections              #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

-- |
-- Module      : Data.HBifunctor.Associative
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides tools for working with binary functor combinators
-- that represent interpretable schemas.
--
-- These are types @'HBifunctor' t@ that take two functors @f@ and @g@ and returns a new
-- functor @t f g@, that "mixes together" @f@ and @g@ in some way.
--
-- The high-level usage of this is
--
-- @
-- 'biretract' :: t f f ~> f
-- @
--
-- which lets you fully "mix" together the two input functors.
--
-- This class also associates each 'HBifunctor' with its "semigroup functor
-- combinator", so we can "squish together" repeated applications of @t@.
--
-- That is, an @'SF' t f a@ is either:
--
-- *   @f a@
-- *   @t f f a@
-- *   @t f (t f f) a@
-- *   @t f (t f (t f f)) a@
-- *   .. etc.
--
-- which means we can have "list-like" schemas that represent multiple
-- copies of @f@.
--
-- See "Data.HBifunctor.Tensor" for a version that also provides an analogy
-- to 'inject', and a more flexible "squished" combinator
-- 'Data.HBifunctor.Tensor.MF' that has an "empty" element.
module Data.HBifunctor.Associative (
  -- * 'Associative'
    Associative(..)
  , assoc
  , disassoc
  -- * 'Semigroupoidal'
  , Semigroupoidal(..)
  , CS
  , matchingSF
  -- ** Utility
  , biget
  , bicollect
  , (!*!)
  , (!$!)
  ) where

-- import           Data.Constraint
-- import           Data.Finite
-- import           Data.Functor.Classes
-- import           Data.Map.NonEmpty        (NEMap)
-- import           GHC.TypeLits.Witnesses
-- import           GHC.TypeNats
-- import           Unsafe.Coerce
import qualified Data.Map.NonEmpty        as NEM
import           Control.Applicative
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Comonad.Trans.Env
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Bifunctor.Joker
import           Data.Coerce
import           Data.Data
import           Data.Foldable
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
import           Data.Functor.Day            (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.HBifunctor
import           Data.HFunctor
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
import           Data.Kind
import           Data.List.NonEmpty          (NonEmpty(..))
import           Data.Semigroup              (Any(..))
import           GHC.Generics hiding         (C)
import qualified Data.Functor.Day            as D

-- | An 'HBifunctor' where it doesn't matter which binds first is
-- 'Associative'.  Knowing this gives us a lot of power to rearrange the
-- internals of our 'HFunctor' at will.
--
-- For example, for the functor product:
--
-- @
-- data (f ':*:' g) a = f a :*: g a
-- @
--
-- We know that @f :*: (g :*: h)@ is the same as @(f :*: g) :*: h@.
class HBifunctor t => Associative t where
    -- | The isomorphism between @t f (t g h) a@ and @t (t f g) h a@.  To
    -- use this isomorphism, see 'assoc' and 'disassoc'.
    associating
        :: (Functor f, Functor g, Functor h)
        => t f (t g h) <~> t (t f g) h
    {-# MINIMAL associating #-}

-- | Reassociate an application of @t@.
assoc
    :: (Associative t, Functor f, Functor g, Functor h)
    => t f (t g h)
    ~> t (t f g) h
assoc = viewF associating

-- | Reassociate an application of @t@.
disassoc
    :: (Associative t, Functor f, Functor g, Functor h)
    => t (t f g) h
    ~> t f (t g h)
disassoc = reviewF associating

-- | For some @t@s, you can represent the act of applying a functor @f@ to
-- @t@ many times, as a single type.  That is, there is some type @'SF'
-- t f@ that is equivalent to one of:
--
-- *  @f a@                             -- 1 time
-- *  @t f f a@                         -- 2 times
-- *  @t f (t f f) a@                   -- 3 times
-- *  @t f (t f (t f f)) a@             -- 4 times
-- *  @t f (t f (t f (t f f))) a@       -- 5 times
-- *  .. etc
--
-- This typeclass associates each @t@ with its "induced semigroupoidal
-- functor combinator" @'SF' t@.
--
-- This is useful because sometimes you might want to describe a type that
-- can be @t f f@, @t f (t f f)@, @t f (t f (t f f))@, etc.; "f applied to
-- itself", with at least one @f@.  This typeclass lets you use a type like
-- 'NonEmptyF' in terms of repeated applications of ':*:', or 'Ap1' in
-- terms of repeated applications of 'Day', or 'Free1' in terms of repeated
-- applications of 'Comp', etc.
--
-- For example, @f ':*:' f@ can be interpreted as "a free selection of two
-- @f@s", allowing you to specify "I have to @f@s that I can use".  If you
-- want to specify "I want 1, 2, or many different @f@s that I can use",
-- you can use @'NonEmptyF' f@.
--
-- At the high level, the main way to /use/ a 'Semigroupoidal' is with
-- 'biretract' and 'binterpret':
--
-- @
-- 'biretract' :: t f f '~>' f
-- 'binterpret' :: (f ~> h) -> (g ~> h) -> t f g ~> h
-- @
--
-- which are like the 'HBifunctor' versions of 'retract' and 'interpret':
-- they fully "mix" together the two inputs of @t@.
--
-- Also useful is:
--
-- @
-- 'toSF' :: t f f a -> SF t f a
-- @
--
-- Which converts a @t@ into its aggregate type 'SF'.
--
-- In reality, most 'Semigroupoidal' instances are also
-- 'Data.HBifunctor.Tensor.Monoidal' instances, so you can think of the
-- separation as mostly to help organize functionality.  However, there are
-- two non-monoidal semigroupoidal instances of note: 'HClown' and
-- 'HJoker', which are higher order analogues of the 'Data.Semigroup.First'
-- and 'Data.Semigroup.Last' semigroups, roughly.
class (Associative t, Interpret (SF t)) => Semigroupoidal t where
    -- | The "semigroup functor combinator" generated by @t@.
    --
    -- A value of type @SF t f a@ is /equivalent/ to one of:
    --
    -- *  @f a@
    -- *  @t f f a@
    -- *  @t f (t f f) a@
    -- *  @t f (t f (t f f)) a@
    -- *  @t f (t f (t f (t f f))) a@
    -- *  .. etc
    --
    -- For example, for ':*:', we have 'NonEmptyF'.  This is because:
    --
    -- @
    -- x             ~ 'NonEmptyF' (x ':|' [])      ~ 'inject' x
    -- x ':*:' y       ~ NonEmptyF (x :| [y])     ~ 'toSF' (x :*: y)
    -- x :*: y :*: z ~ NonEmptyF (x :| [y,z])
    -- -- etc.
    -- @
    --
    -- You can create an "singleton" one with 'inject', or else one from
    -- a single @t f f@ with 'toSF'.
    type SF t :: (Type -> Type) -> Type -> Type

    -- | If a @'SF' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'SF' t f@s applied to
    -- themselves into one giant @'SF' t f@ containing all of the @t f@s.
    appendSF :: t (SF t f) (SF t f) ~> SF t f
    matchSF  :: Functor f => SF t f ~> f :+: t f (SF t f)

    -- | Prepend an application of @t f@ to the front of a @'SF' t f@.
    consSF :: t f (SF t f) ~> SF t f
    consSF = appendSF . hleft inject

    -- | Embed a direct application of @f@ to itself into a @'SF' t f@.
    toSF :: t f f ~> SF t f
    toSF = consSF . hright inject

    -- | The 'HBifunctor' analogy of 'retract'. It retracts /both/ @f@s
    -- into a single @f@, effectively fully mixing them together.
    biretract :: CS t f => t f f ~> f
    biretract = retract . toSF

    -- | The 'HBifunctor' analogy of 'interpret'.  It takes two
    -- interpreting functions, and mixes them together into a target
    -- functor @h@.
    binterpret
        :: CS t h
        => f ~> h
        -> g ~> h
        -> t f g ~> h
    binterpret f g = retract . toSF . hbimap f g

    {-# MINIMAL appendSF, matchSF #-}

-- | Convenient alias for the constraint required for 'biretract',
-- 'binterpret', etc.
--
-- It's usually a constraint on the target/result context of interpretation
-- that allows you to "exit" or "run" a @'Semigroupoidal' t@.
type CS t = C (SF t)

-- | An @'SF' t f@ represents the successive application of @t@ to @f@,
-- over and over again.   So, that means that an @'SF' t f@ must either be
-- a single @f@, or an @t f (SF t f)@.
--
-- 'matchingSF' states that these two are isomorphic.  Use 'matchSF' and
-- @'inject' '!*!' 'consSF'@ to convert between one and the other.
matchingSF :: (Semigroupoidal t, Functor f) => SF t f <~> f :+: t f (SF t f)
matchingSF = isoF matchSF (inject !*! consSF)

-- | Useful wrapper over 'binterpret' to allow you to directly extract
-- a value @b@ out of the @t f a@, if you can convert @f x@ into @b@.
--
-- Note that depending on the constraints on the interpretation of @t@, you
-- may have extra constraints on @b@.
--
-- *    If @'C' ('SF' t)@ is 'Data.Constraint.Trivial.Unconstrained', there
--      are no constraints on @b@
-- *    If @'C' ('SF' t)@ is 'Apply', @b@ needs to be an instance of 'Semigroup'
-- *    If @'C' ('SF' t)@ is 'Applicative', @b@ needs to be an instance of 'Monoid'
--
-- For some constraints (like 'Monad'), this will not be usable.
--
-- @
-- -- Return the length of either the list, or the Map, depending on which
-- --   one s in the '+'
-- 'biget' 'length' length
--     :: ([] :+: 'Data.Map.Map' 'Int') 'Char'
--     -> Int
--
-- -- Return the length of both the list and the map, added together
-- 'biget' ('Data.Monoid.Sum' . length) (Sum . length)
--     :: 'Day' [] (Map Int) Char
--     -> Sum Int
-- @
biget
    :: (Semigroupoidal t, CS t (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
biget f g = getConst . binterpret (Const . f) (Const . g)

-- | Infix alias for 'biget'
--
-- @
-- -- Return the length of either the list, or the Map, depending on which
-- --   one s in the '+'
-- 'length' '!$!' length
--     :: ([] :+: 'Data.Map.Map' 'Int') 'Char'
--     -> Int
--
-- -- Return the length of both the list and the map, added together
-- 'Data.Monoid.Sum' . length !$! Sum . length
--     :: 'Day' [] (Map Int) Char
--     -> Sum Int
-- @
(!$!)
    :: (Semigroupoidal t, CS t (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
(!$!) = biget
infixr 5 !$!

-- | Infix alias for 'binterpret'
(!*!)
    :: (Semigroupoidal t, CS t h)
    => (f ~> h)
    -> (g ~> h)
    -> t f g
    ~> h
(!*!) = binterpret
infixr 5 !*!

-- | Useful wrapper over 'biget' to allow you to collect a @b@ from all
-- instances of @f@ and @g@ inside a @t f g a@.
--
-- This will work if @'C' t@ is 'Data.Constraint.Trivial.Unconstrained',
-- 'Apply', or 'Applicative'.
bicollect
    :: (Semigroupoidal t, CS t (Const [b]))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> [b]
bicollect f g = biget ((:[]) . f) ((:[]) . g)

instance Associative (:*:) where
    associating = isoF to_ from_
      where
        to_   (x :*: (y :*: z)) = (x :*: y) :*: z
        from_ ((x :*: y) :*: z) = x :*: (y :*: z)

instance Associative Product where
    associating = isoF to_ from_
      where
        to_   (Pair x (Pair y z)) = Pair (Pair x y) z
        from_ (Pair (Pair x y) z) = Pair x (Pair y z)

instance Associative Day where
    associating = isoF D.assoc D.disassoc

instance Associative (:+:) where
    associating = isoF to_ from_
      where
        to_ = \case
          L1 x      -> L1 (L1 x)
          R1 (L1 y) -> L1 (R1 y)
          R1 (R1 z) -> R1 z
        from_ = \case
          L1 (L1 x) -> L1 x
          L1 (R1 y) -> R1 (L1 y)
          R1 z      -> R1 (R1 z)

instance Associative Sum where
    associating = isoF to_ from_
      where
        to_ = \case
          InL x       -> InL (InL x)
          InR (InL y) -> InL (InR y)
          InR (InR z) -> InR z
        from_ = \case
          InL (InL x) -> InL x
          InL (InR y) -> InR (InL y)
          InR z       -> InR (InR z)

instance Associative These1 where
    associating = isoF to_ from_
      where
        to_ = \case
          This1  x              -> This1  (This1  x  )
          That1    (This1  y  ) -> This1  (That1    y)
          That1    (That1    z) -> That1               z
          That1    (These1 y z) -> These1 (That1    y) z
          These1 x (This1  y  ) -> This1  (These1 x y)
          These1 x (That1    z) -> These1 (This1  x  ) z
          These1 x (These1 y z) -> These1 (These1 x y) z
        from_ = \case
          This1  (This1  x  )   -> This1  x
          This1  (That1    y)   -> That1    (This1  y  )
          This1  (These1 x y)   -> These1 x (This1  y  )
          That1               z -> That1    (That1    z)
          These1 (This1  x  ) z -> These1 x (That1    z)
          These1 (That1    y) z -> That1    (These1 y z)
          These1 (These1 x y) z -> These1 x (These1 y z)

instance Associative Void3 where
    associating = isoF coerce coerce

instance Associative Comp where
    associating = isoF to_ from_
      where
        to_   (x :>>= y) = (x :>>= (unComp . y)) :>>= id
        from_ ((x :>>= y) :>>= z) = x :>>= ((:>>= z) . y)

-- | This is only a true 'Associative' when @t f@ can fit at most one @f@
-- (like 'MaybeF', 'Control.Applicative.Lift.Lift').  Otherwise, 'disassoc'
-- loses some of the nested structure.
instance HBind t => Associative (HClown t) where
    associating = isoF runHClown                HClown
                . isoF (hmap (HClown . inject)) (hbind runHClown)
                . isoF HClown                   runHClown


-- | This is only a true 'Associative' when @t f@ can fit at most one @f@
-- (like 'MaybeF', 'Control.Applicative.Lift.Lift').  Otherwise, 'assoc'
-- loses some of the nested structure.
instance HBind t => Associative (HJoker t) where
    associating = isoF runHJoker         HJoker
                . isoF (hbind runHJoker) (hmap (HJoker . inject))
                . isoF HJoker            runHJoker

instance Semigroupoidal (:*:) where
    type SF (:*:) = NonEmptyF

    appendSF (NonEmptyF xs :*: NonEmptyF ys) = NonEmptyF (xs <> ys)
    matchSF x = case ys of
        L1 ~Proxy -> L1 y
        R1 zs     -> R1 $ y :*: zs
      where
        y :*: ys = fromListF `hright` nonEmptyProd x

    consSF (x :*: NonEmptyF xs) = NonEmptyF $ x :| toList xs
    toSF   (x :*: y           ) = NonEmptyF $ x :| [y]

    biretract (x :*: y) = x <!> y
    binterpret f g (x :*: y) = f x <!> g y

instance Semigroupoidal Product where
    type SF Product = NonEmptyF

    appendSF (NonEmptyF xs `Pair` NonEmptyF ys) = NonEmptyF (xs <> ys)
    matchSF x = case ys of
        L1 ~Proxy -> L1 y
        R1 zs     -> R1 $ Pair y zs
      where
        y :*: ys = fromListF `hright` nonEmptyProd x

    consSF (x `Pair` NonEmptyF xs) = NonEmptyF $ x :| toList xs
    toSF   (x `Pair` y           ) = NonEmptyF $ x :| [y]

    biretract (Pair x y) = x <!> y
    binterpret f g (Pair x y) = f x <!> g y

instance Semigroupoidal Day where
    type SF Day = Ap1

    appendSF (Day x y z) = z <$> x <.> y
    matchSF a = case fromAp `hright` ap1Day a of
      Day x y z -> case y of
        L1 (Identity y') -> L1 $ (`z` y') <$> x
        R1 ys            -> R1 $ Day x ys z

    consSF (Day x y z) = Ap1 x $ flip z <$> toAp y
    toSF   (Day x y z) = z <$> inject x <.> inject y

    biretract (Day x y z) = z <$> x <.> y
    binterpret f g (Day x y z) = z <$> f x <.> g y

instance Semigroupoidal (:+:) where
    type SF (:+:) = Step

    appendSF = \case
      L1 (Step i x) -> Step (i + 1) x
      R1 (Step i y) -> Step (i + 2) y
    matchSF = hright stepDown . stepDown

    consSF = stepUp . R1 . stepUp
    toSF = \case
      L1 x -> Step 1 x
      R1 y -> Step 2 y

    biretract = \case
      L1 x -> x
      R1 y -> y
    binterpret f g = \case
      L1 x -> f x
      R1 y -> g y

instance Semigroupoidal Sum where
    type SF Sum = Step

    appendSF = \case
      InL (Step i x) -> Step (i + 1) x
      InR (Step i y) -> Step (i + 2) y
    matchSF = hright (viewF sumSum . stepDown) . stepDown

    consSF = stepUp . R1 . stepUp . reviewF sumSum
    toSF = \case
      InL x -> Step 1 x
      InR y -> Step 2 y

    biretract = \case
      InR x -> x
      InL y -> y
    binterpret f g = \case
      InL x -> f x
      InR y -> g y

-- data TC f a = TCA (f a) Bool
--             | TCB (Maybe (f a)) (TC f a)
                -- sparse, non-empty list
                -- and the last item has a Bool
                -- aka sparse non-empty list tagged with a bool

instance Semigroupoidal These1 where
    type SF These1 = ComposeT (EnvT Any) Steps

    appendSF s = ComposeT $ case s of
        This1  (ComposeT (EnvT _ q))                       ->
          EnvT (Any True) q
        That1                        (ComposeT (EnvT b q)) ->
          EnvT b        (stepsUp (That1 q))
        These1 (ComposeT (EnvT a q)) (ComposeT (EnvT b r)) ->
          EnvT (a <> b) (q <> r)
    matchSF (ComposeT (EnvT a@(Any isImpure) q)) = case stepsDown q of
      This1  x
        | isImpure  -> R1 $ This1 x
        | otherwise -> L1 x
      That1    y    -> R1 . That1 . ComposeT $ EnvT a y
      These1 x y    -> R1 . These1 x .  ComposeT $ EnvT a y

    consSF s = ComposeT $ case s of
      This1  x                       -> EnvT (Any True) (inject x)
      That1    (ComposeT (EnvT b y)) -> EnvT b          (stepsUp (That1    y))
      These1 x (ComposeT (EnvT b y)) -> EnvT b          (stepsUp (These1 x y))
    toSF  s = ComposeT $ case s of
      This1  x   -> EnvT (Any True ) . Steps $ NEM.singleton 0 x
      That1    y -> EnvT (Any False) . Steps $ NEM.singleton 1 y
      These1 x y -> EnvT (Any False) . Steps $ NEM.fromDistinctAscList $ (0, x) :| [(1, y)]

    biretract = \case
      This1  x   -> x
      That1    y -> y
      These1 x y -> x <!> y
    binterpret f g = \case
      This1  x   -> f x
      That1    y -> g y
      These1 x y -> f x <!> g y

instance Semigroupoidal Comp where
    type SF Comp = Free1

    appendSF (x :>>= y) = x >>- y
    matchSF = matchFree1

    consSF (x :>>= y) = liftFree1 x >>- y
    toSF   (x :>>= g) = liftFree1 x >>- inject . g

    biretract      (x :>>= y) = x >>- y
    binterpret f g (x :>>= y) = f x >>- (g . y)

instance (Interpret t, HBind t) => Semigroupoidal (HClown t) where
    type SF (HClown t) = HLift t

    appendSF = hbind id . HOther . runHClown
    matchSF  = \case
      HPure  x -> L1 x
      HOther x -> R1 $ HClown x

instance (Interpret t, HBind t) => Semigroupoidal (HJoker t) where
    type SF (HJoker t) = HFree t

    appendSF = HJoin . runHJoker
    matchSF  = \case
      HReturn x -> L1 x
      HJoin   x -> R1 $ HJoker x

instance Associative Joker where
    associating = isoF (Joker . Joker    . runJoker)
                       (Joker . runJoker . runJoker)

instance Associative LeftF where
    associating = isoF (LeftF . LeftF    . runLeftF)
                       (LeftF . runLeftF . runLeftF)

instance Associative RightF where
    associating = isoF (RightF . runRightF . runRightF)
                       (RightF . RightF    . runRightF)

-- | Somewhat ironically, 'Joker' is also @'HClown'
-- 'Control.Monad.Trans.Identity.IdentityT'@, or 'LeftF'.
instance Semigroupoidal Joker where
    type SF Joker = EnvT Any

    appendSF (Joker (EnvT _ x)) = EnvT (Any True) x
    matchSF (EnvT (Any False) x) = L1 x
    matchSF (EnvT (Any True ) x) = R1 $ Joker x

instance Semigroupoidal LeftF where
    type SF LeftF = EnvT Any

    appendSF = hbind (EnvT (Any True)) . runLeftF
    matchSF (EnvT (Any False) x) = L1 x
    matchSF (EnvT (Any True ) x) = R1 $ LeftF x

    consSF = EnvT (Any True) . runLeftF
    toSF   = EnvT (Any True) . runLeftF

    biretract      = runLeftF
    binterpret f _ = f . runLeftF

instance Semigroupoidal RightF where
    type SF RightF = Step

    appendSF = stepUp . R1 . runRightF
    matchSF  = hright RightF . stepDown

    consSF   = stepUp . R1 . runRightF
    toSF     = Step 1 . runRightF

    biretract      = runRightF
    binterpret _ g = g . runRightF
