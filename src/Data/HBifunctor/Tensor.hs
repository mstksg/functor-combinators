{-# OPTIONS_GHC -Wno-orphans #-}

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
-- 'Tensor' gives some extra properties of your binary functor combinator:
-- associativity and identity (see docs for 'Tensor' for more details).
--
-- The binary analog of 'Interpret' is 'MonoidIn'.  If your combinator @t@
-- and target functor @f@ is an instance of @'MonoidIn' t f@, it means you
-- can "interpret" out of your tensored values, and also "generate" values
-- of @f@.
--
-- @
-- 'biretract' :: (f ':+:' f) a -> f a
-- 'pureT'     :: 'V1' a -> f a
--
-- biretract :: 'Plus' f => (f ':*:' f) a -> f a
-- pureT     :: Plus f => 'Proxy' a -> f a
--
-- biretract :: 'Applicative' f => 'Day' f f a -> f a
-- pureT     :: Applicative f => 'Identity' a -> f a
--
-- biretract :: 'Monad' f => 'Comp' f f a -> f a
-- pureT     :: Monad f => 'Identity' a -> f a
-- @
--
module Data.HBifunctor.Tensor (
  -- * 'Tensor'
    Tensor(..)
  , rightIdentity
  , leftIdentity
  , sumLeftIdentity
  , sumRightIdentity
  , prodLeftIdentity
  , prodRightIdentity
  -- * 'MonoidIn'
  , MonoidIn(..)
  , nilLB
  , consLB
  , unconsLB
  , retractLB
  , interpretLB
  -- ** Utility
  , inL
  , inR
  , outL
  , outR
  , prodOutL
  , prodOutR
  , WrapF(..)
  , WrapLB(..)
  -- * 'Matchable'
  , Matchable(..)
  , splittingNE
  , matchingLB
  ) where

import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Coerce
import           Data.Data
import           Data.Function
import           Data.Functor.Apply.Free
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Contravariant.Divisible.Free
import           Data.Functor.Contravariant.Night          (Night(..), Not(..))
import           Data.Functor.Day                          (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Invariant
import           Data.Functor.Plus
import           Data.Functor.Product
import           Data.Functor.Sum
import           Data.Functor.These
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor.Internal
import           Data.HFunctor
import           Data.HFunctor.Chain.Internal
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
import           Data.List.NonEmpty                        (NonEmpty(..))
import           GHC.Generics
import qualified Data.Functor.Contravariant.Coyoneda       as CCY
import qualified Data.Functor.Contravariant.Day            as CD
import qualified Data.Functor.Contravariant.Night          as N
import qualified Data.Functor.Day                          as D
import qualified Data.Functor.Invariant.Day                as ID
import qualified Data.Map.NonEmpty                         as NEM

-- | @f@ is isomorphic to @t f i@: that is, @i@ is the identity of @t@, and
-- leaves @f@ unchanged.
rightIdentity :: (Tensor t i, FunctorBy t f) => f <~> t f i
rightIdentity = isoF intro1 elim1

-- | @g@ is isomorphic to @t i g@: that is, @i@ is the identity of @t@, and
-- leaves @g@ unchanged.
leftIdentity  :: (Tensor t i, FunctorBy t g) => g <~> t i g
leftIdentity = isoF intro2 elim2

-- | 'leftIdentity' ('intro1' and 'elim1') for ':+:' actually does not
-- require 'Functor'.  This is the more general version.
sumLeftIdentity :: f <~> V1 :+: f
sumLeftIdentity = isoF R1 (absurd1 !+! id)

-- | 'rightIdentity' ('intro2' and 'elim2') for ':+:' actually does not
-- require 'Functor'.  This is the more general version.
sumRightIdentity :: f <~> f :+: V1
sumRightIdentity = isoF L1 (id !+! absurd1)

-- | 'leftIdentity' ('intro1' and 'elim1') for ':*:' actually does not
-- require 'Functor'.  This is the more general version.
prodLeftIdentity :: f <~> Proxy :*: f
prodLeftIdentity = isoF (Proxy :*:) (\case _ :*: y -> y)

-- | 'rightIdentity' ('intro2' and 'elim2') for ':*:' actually does not
-- require 'Functor'.  This is the more general version.
prodRightIdentity :: g <~> g :*: Proxy
prodRightIdentity = isoF (:*: Proxy) (\case x :*: _ -> x)

-- | A poly-kinded version of 'outL' for ':*:'.
prodOutL :: f :*: g ~> f
prodOutL (x :*: _) = x

-- | A poly-kinded version of 'outR' for ':*:'.
prodOutR :: f :*: g ~> g
prodOutR (_ :*: y) = y

-- | This class effectively gives us a way to generate a value of @f a@
-- based on an @i a@, for @'Tensor' t i@.  Having this ability makes a lot
-- of interesting functions possible when used with 'biretract' from
-- 'SemigroupIn' that weren't possible without it: it gives us a "base
-- case" for recursion in a lot of cases.
--
-- Essentially, we get an @i ~> f@, 'pureT', where we can introduce an @f
-- a@ as long as we have an @i a@.
--
-- Formally, if we have @'Tensor' t i@, we are enriching the category of
-- endofunctors with monoid structure, turning it into a monoidal category.
-- Different choices of @t@ give different monoidal categories.
--
-- A functor @f@ is known as a "monoid in the (monoidal) category
-- of endofunctors on @t@" if we can 'biretract':
--
-- @
-- t f f ~> f
-- @
--
-- and also 'pureT':
--
-- @
-- i ~> f
-- @
--
-- This gives us a few interesting results in category theory, which you
-- can stil reading about if you don't care:
--
-- *  /All/ functors are monoids in the monoidal category
--    on ':+:'
-- *  The class of functors that are monoids in the monoidal
--    category on ':*:' is exactly the functors that are instances of
--    'Plus'.
-- *  The class of functors that are monoids in the monoidal
--    category on 'Day' is exactly the functors that are instances of
--    'Applicative'.
-- *  The class of functors that are monoids in the monoidal
--    category on 'Comp' is exactly the functors that are instances of
--    'Monad'.
--
--    This is the meaning behind the common adage, "monads are just monoids
--    in the category of endofunctors".  It means that if you enrich the
--    category of endofunctors to be monoidal with 'Comp', then the class
--    of functors that are monoids in that monoidal category are exactly
--    what monads are.  However, the adage is a little misleading: there
--    are many other ways to enrich the category of endofunctors to be
--    monoidal, and 'Comp' is just one of them.  Similarly, the class of
--    functors that are monoids in the category of endofunctors enriched by
--    'Day' are 'Applicative'.
--
-- Note that instances of this class are /intended/ to be written with @t@
-- and @i@ to be fixed type constructors, and @f@ to be allowed to vary
-- freely:
--
-- @
-- instance Monad f => MonoidIn Comp Identity f
-- @
--
-- Any other sort of instance and it's easy to run into problems with type
-- inference.  If you want to write an instance that's "polymorphic" on
-- tensor choice, use the 'WrapHBF' and 'WrapF' newtype wrappers over type
-- variables, where the third argument also uses a type constructor:
--
-- @
-- instance MonoidIn (WrapHBF t) (WrapF i) (MyFunctor t i)
-- @
--
-- This will prevent problems with overloaded instances.
class (Tensor t i, SemigroupIn t f) => MonoidIn t i f where

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

    default pureT :: Interpret (ListBy t) f => i ~> f
    pureT  = retract . reviewF (splittingLB @t) . L1

-- | An implementation of 'retract' that works for any instance of
-- @'MonoidIn' t i@ for @'ListBy' t@.
--
-- Can be useful as a default implementation if you already have 'MonoidIn'
-- implemented.
retractLB :: forall t i f. MonoidIn t i f => ListBy t f ~> f
retractLB = (pureT @t !*! biretract @t . hright (retractLB @t))
              . unconsLB @t

-- | An implementation of 'interpret' that works for any instance of
-- @'MonoidIn' t i@ for @'ListBy' t@.
--
-- Can be useful as a default implementation if you already have 'MonoidIn'
-- implemented.
interpretLB :: forall t i g f. MonoidIn t i f => (g ~> f) -> ListBy t g ~> f
interpretLB f = retractLB @t . hmap f

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
    :: (Tensor t Proxy, FunctorBy t f)
    => t f g ~> f
outL = elim1 . hright absorb

-- | Convenient wrapper over 'elim2' that lets us drop one of the arguments
-- of a 'Tensor' for free, without requiring any constraints (like for
-- 'binterpret').
--
-- See 'prodOutR' for a version that does not require @'Functor' g@,
-- specifically for ':*:'.
outR
    :: (Tensor t Proxy, FunctorBy t g)
    => t f g ~> g
outR = elim2 . hleft absorb

-- | For some @t@, we have the ability to "statically analyze" the @'ListBy' t@
-- and pattern match and manipulate the structure without ever
-- interpreting or retracting.  These are 'Matchable'.
class Tensor t i => Matchable t i where
    -- | The inverse of 'splitNE'.  A consing of @f@ to @'ListBy' t f@ is
    -- non-empty, so it can be represented as an @'NonEmptyBy' t f@.
    --
    -- This is analogous to a function @'uncurry' ('Data.List.NonEmpty.:|')
    -- :: (a, [a]) -> 'Data.List.NonEmpty.NonEmpty' a@.
    unsplitNE :: FunctorBy t f => t f (ListBy t f) ~> NonEmptyBy t f

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
    --
    -- Note that you can recursively "unroll" a 'ListBy' completely into
    -- a 'Data.HFunctor.Chain.Chain' by using
    -- 'Data.HFunctor.Chain.unrollLB'.
    matchLB   :: FunctorBy t f => ListBy t f ~> i :+: NonEmptyBy t f

-- | An @'NonEmptyBy' t f@ is isomorphic to an @f@ consed with an @'ListBy' t f@, like
-- how a @'Data.List.NonEmpty.NonEmpty' a@ is isomorphic to @(a, [a])@.
splittingNE
    :: (Matchable t i, FunctorBy t f)
    => NonEmptyBy t f <~> t f (ListBy t f)
splittingNE = isoF splitNE unsplitNE

-- | An @'ListBy' t f@ is isomorphic to either the empty case (@i@) or the
-- non-empty case (@'NonEmptyBy' t f@), like how @[a]@ is isomorphic to @'Maybe'
-- ('Data.List.NonEmpty.NonEmpty' a)@.
matchingLB
    :: forall t i f. (Matchable t i, FunctorBy t f)
    => ListBy t f <~> i :+: NonEmptyBy t f
matchingLB = isoF (matchLB @t) (nilLB @t !*! fromNE @t)

instance Tensor (:*:) Proxy where
    type ListBy (:*:) = ListF
    intro1 = (:*: Proxy)
    intro2 = (Proxy :*:)
    elim1 (x      :*: ~Proxy) = x
    elim2 (~Proxy :*: y     ) = y

    appendLB (ListF xs :*: ListF ys) = ListF (xs ++ ys)
    splitNE     = nonEmptyProd
    splittingLB = isoF to_ from_
      where
        to_ = \case
          ListF []     -> L1 Proxy
          ListF (x:xs) -> R1 (x :*: ListF xs)
        from_ = \case
          L1 ~Proxy           -> ListF []
          R1 (x :*: ListF xs) -> ListF (x:xs)

    toListBy (x :*: y) = ListF [x, y]

-- | Instances of 'Plus' are monoids in the monoidal category on
-- ':*:'.
instance Plus f => MonoidIn (:*:) Proxy f where
    pureT _        = zero

instance Tensor Product Proxy where
    type ListBy Product = ListF
    intro1 = (`Pair` Proxy)
    intro2 = (Proxy `Pair`)
    elim1 (Pair x ~Proxy) = x
    elim2 (Pair ~Proxy y) = y

    appendLB (ListF xs `Pair` ListF ys) = ListF (xs ++ ys)
    splitNE     = viewF prodProd . nonEmptyProd
    splittingLB = isoF to_ from_
      where
        to_ = \case
          ListF []     -> L1 Proxy
          ListF (x:xs) -> R1 (x `Pair` ListF xs)
        from_ = \case
          L1 ~Proxy              -> ListF []
          R1 (x `Pair` ListF xs) -> ListF (x:xs)

    toListBy (Pair x y) = ListF [x, y]

-- | Instances of 'Plus' are monoids in the monoidal category on
-- 'Product'.
instance Plus f => MonoidIn Product Proxy f where
    pureT _         = zero

instance Tensor Day Identity where
    type ListBy Day = Ap
    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1

    appendLB (Day x y z) = z <$> x <*> y
    splitNE     = ap1Day
    splittingLB = isoF to_ from_
      where
        to_ = \case
          Pure x  -> L1 (Identity x)
          Ap x xs -> R1 (Day x xs (&))
        from_ = \case
          L1 (Identity x) -> Pure x
          R1 (Day x xs f) -> Ap x (flip f <$> xs)

    toListBy (Day x y z) = Ap x (Ap y (Pure (flip z)))

-- | Instances of 'Applicative' are monoids in the monoidal category on
-- the covariant 'Day'.
--
-- Note that because of typeclass constraints, this requires 'Apply' as
-- well as 'Applicative'.  But, you can get a "local" instance of 'Apply'
-- for any 'Applicative' using
-- 'Data.Functor.Combinators.Unsafe.unsafeApply'.
instance (Apply f, Applicative f) => MonoidIn Day Identity f where
    pureT            = generalize

-- | @since 0.3.0.0
instance Tensor CD.Day Proxy where
    type ListBy CD.Day = Div
    intro1 = CD.intro2
    intro2 = CD.intro1
    elim1 = CD.day1
    elim2 = CD.day2

    appendLB (CD.Day x y z) = divide z x y
    splitNE = go . splitNE @(:*:) . NonEmptyF . unDiv1
      where
        go (CCY.Coyoneda f x :*: ListF xs) = CD.Day x (Div xs) (\y -> (f y, y))
    splittingLB = isoF (ListF . unDiv) (Div . runListF) . splittingLB @(:*:) . isoF (hright to_) (hright from_)
      where
        to_   (CCY.Coyoneda f x :*: ListF xs) = CD.Day x (Div xs) (\y -> (f y, y))
        from_ (CD.Day x (Div xs) f) = CCY.Coyoneda (fst . f) x :*: contramap (snd . f) (ListF xs)

    toListBy (CD.Day x y f) = Div . runListF . toListBy $
        CCY.Coyoneda (fst . f) x :*: CCY.Coyoneda (snd . f) y

-- | Instances of 'Divisible' are monoids in the monoidal category on
-- contravariant 'CD.Day'.
--
-- Note that because of typeclass constraints, this requires 'Divise' as
-- well as 'Divisible'.  But, you can get a "local" instance of 'Divise'
-- for any 'Divisible' using
-- 'Data.Functor.Combinators.Unsafe.unsafeDivise'.
--
-- @since 0.3.0.0
instance (Divise f, Divisible f) => MonoidIn CD.Day Proxy f where
    pureT _ = conquer

instance Tensor ID.Day Identity where
    type ListBy ID.Day = DayChain

    intro1 = ID.intro2
    intro2 = ID.intro1
    elim1 = ID.elim2
    elim2 = ID.elim1

    appendLB = coerce appendChain
    splitNE = coerce splitChain1
    splittingLB = coercedF . splittingChain . coercedF

    toListBy = DayChain . More . hright (unDayChain . inject)

instance Matchable ID.Day Identity where
    unsplitNE = coerce unsplitNEIDay_
    matchLB = coerce matchLBIDay_

unsplitNEIDay_ :: Invariant f => ID.Day f (Chain ID.Day Identity f) ~> Chain1 ID.Day f
unsplitNEIDay_ (ID.Day x xs g f) = case xs of
  Done (Identity r) -> Done1 $ invmap (`g` r) (fst . f) x
  More ys           -> More1 $ ID.Day x (unsplitNEIDay_ ys) g f

matchLBIDay_ :: Invariant f => Chain ID.Day Identity f ~> (Identity :+: Chain1 ID.Day f)
matchLBIDay_ = \case
  Done x  -> L1 x
  More xs -> R1 $ unsplitNEIDay_ xs

-- | @since 0.3.0.0
instance Tensor Night Not where
    type ListBy Night = Dec
    intro1 = N.intro2
    intro2 = N.intro1
    elim1 = N.elim2
    elim2 = N.elim1

    appendLB (Night x y z) = decide z x y
    splitNE (Dec1 f x xs) = Night x xs f
    splittingLB = isoF to_ from_
      where
        to_ = \case
          Lose   f      -> L1 (Not f)
          Choose f x xs -> R1 (Night x xs f)
        from_ = \case
          L1 (Not f)    -> Lose f
          R1 (Night x xs f) -> Choose f x xs

    toListBy (Night x y z) = Choose z x (inject y)

-- | Instances of 'Conclude' are monoids in the monoidal category on 'Night'.
instance Conclude f => MonoidIn Night Not f where
    pureT (Not x) = conclude x

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
    splitNE     = stepDown
    splittingLB = stepping . sumLeftIdentity

    toListBy  = \case
      L1 x -> Step 0 x
      R1 x -> Step 1 x

-- | All functors are monoids in the monoidal category on ':+:'.
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
    splitNE     = viewF sumSum . stepDown
    splittingLB = stepping
                . sumLeftIdentity
                . overHBifunctor id sumSum

    toListBy  = \case
      InL x -> Step 0 x
      InR x -> Step 1 x

-- | All functors are monoids in the monoidal category on 'Sum'.
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
    splitNE     = stepsDown . flaggedVal . getComposeT
    splittingLB = steppings . sumLeftIdentity

    toListBy  = \case
      This1  x   -> Steps $ NEM.singleton 0 x
      That1    y -> Steps $ NEM.singleton 1 y
      These1 x y -> Steps $ NEM.fromDistinctAscList ((0, x) :| [(1, y)])

instance Alt f => MonoidIn These1 V1 f where
    pureT = absurd1

instance Tensor Comp Identity where
    type ListBy Comp = Free

    intro1 = (:>>= Identity)
    intro2 = (Identity () :>>=) . const

    elim1 (x :>>= y) = runIdentity . y <$> x
    elim2 (x :>>= y) = y (runIdentity x)

    appendLB (x :>>= y) = x >>= y
    splitNE             = free1Comp
    splittingLB = isoF to_ from_
      where
        to_ :: Free f ~> Identity :+: Comp f (Free f)
        to_ = foldFree' (L1 . Identity) $ \y n -> R1 $
            y :>>= (from_ . n)
        from_ :: Identity :+: Comp f (Free f) ~> Free f
        from_ = generalize
            !*! (\case x :>>= f -> liftFree x >>= f)

    toListBy (x :>>= y) = liftFree x >>= (inject . y)

-- | Instances of 'Monad' are monoids in the monoidal category on
-- 'Comp'.
--
-- This instance is the "proof" that "monads are the monoids in the
-- category of endofunctors (enriched with 'Comp')"
--
-- Note that because of typeclass constraints, this requires 'Bind' as
-- well as 'Monad'.  But, you can get a "local" instance of 'Apply'
-- for any 'Monad' using
-- 'Data.Functor.Combinators.Unsafe.unsafeBind'.
instance (Bind f, Monad f) => MonoidIn Comp Identity f where
    pureT           = generalize

instance Matchable (:*:) Proxy where
    unsplitNE = ProdNonEmpty
    matchLB   = fromListF

instance Matchable Product Proxy where
    unsplitNE = ProdNonEmpty . reviewF prodProd
    matchLB   = fromListF

instance Matchable Day Identity where
    unsplitNE = DayAp1
    matchLB   = fromAp

-- | Instances of 'Conclude' are monoids in the monoidal category on 'Night'.
--
-- @since 0.3.0.0
instance Matchable CD.Day Proxy where
    unsplitNE (CD.Day x (Div xs) f) = Div1 . runNonEmptyF . unsplitNE $
      CCY.Coyoneda (fst . f) x :*: contramap (snd . f) (ListF xs)
    matchLB = hright (Div1 . runNonEmptyF) . matchLB @(:*:) . ListF . unDiv

-- | @since 0.3.0.0
instance Matchable Night Not where
    unsplitNE (Night x xs f) = Dec1 f x xs
    matchLB = \case
      Lose   f      -> L1 (Not f)
      Choose f x xs -> R1 (Dec1 f x xs)

instance Matchable (:+:) V1 where
    unsplitNE   = stepUp
    matchLB     = R1

instance Matchable Sum V1 where
    unsplitNE   = stepUp . reviewF sumSum
    matchLB     = R1

-- We can't write this until we get an isomorphism between MF These1 and SF These1
-- instance Matchable These1 where
--     unsplitNE = stepsUp
--     matchLB   = R1

-- | A newtype wrapper meant to be used to define polymorphic 'MonoidIn'
-- instances.  See documentation for 'MonoidIn' for more information.
--
-- Please do not ever define an instance of 'MonoidIn' "naked" on the
-- third parameter:
--
-- @
-- instance MonidIn (WrapHBF t) (WrapF i) f
-- @
--
-- As that would globally ruin everything using 'WrapHBF'.
newtype WrapF f a = WrapF { unwrapF :: f a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

instance Show1 f => Show1 (WrapF f) where
    liftShowsPrec sp sl d (WrapF x) = showsUnaryWith (liftShowsPrec sp sl) "WrapF" d x

instance Eq1 f => Eq1 (WrapF f) where
    liftEq eq (WrapF x) (WrapF y) = liftEq eq x y

instance Ord1 f => Ord1 (WrapF f) where
    liftCompare c (WrapF x) (WrapF y) = liftCompare c x y

instance Tensor t i => Tensor (WrapHBF t) (WrapF i) where
    type ListBy (WrapHBF t) = ListBy t

    intro1 = WrapHBF . hright WrapF .  intro1
    intro2 = WrapHBF . hleft WrapF . intro2
    elim1 = elim1 . hright unwrapF . unwrapHBF
    elim2 = elim2 . hleft unwrapF . unwrapHBF
    appendLB = appendLB . unwrapHBF
    splitNE = WrapHBF . splitNE
    splittingLB = splittingLB @t
                . overHBifunctor (isoF WrapF unwrapF) (isoF WrapHBF unwrapHBF)
    toListBy = toListBy . unwrapHBF
    fromNE = fromNE @t

-- | Any @'ListBy' t f@ is a @'SemigroupIn' t@ and a @'MonoidIn' t i@, if we
-- have @'Tensor' t i@. This newtype wrapper witnesses that fact.  We
-- require a newtype wrapper to avoid overlapping instances.
newtype WrapLB t f a = WrapLB { unwrapLB :: ListBy t f a }

instance Functor (ListBy t f) => Functor (WrapLB t f) where
    fmap f (WrapLB x) = WrapLB (fmap f x)

-- | @since 0.3.0.0
instance Contravariant (ListBy t f) => Contravariant (WrapLB t f) where
    contramap f (WrapLB x) = WrapLB (contramap f x)

-- | @since 0.3.0.0
instance Invariant (ListBy t f) => Invariant (WrapLB t f) where
    invmap f g (WrapLB x) = WrapLB (invmap f g x)

instance (Tensor t i, FunctorBy t f, FunctorBy t (WrapLB t f)) => SemigroupIn (WrapHBF t) (WrapLB t f) where
    biretract = WrapLB . appendLB . hbimap unwrapLB unwrapLB . unwrapHBF
    binterpret f g = biretract . hbimap f g

instance (Tensor t i, FunctorBy t f, FunctorBy t (WrapLB t f)) => MonoidIn (WrapHBF t) (WrapF i) (WrapLB t f) where
    pureT = WrapLB . nilLB @t . unwrapF
