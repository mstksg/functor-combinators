
module Data.HBifunctor.Tensor.Internal (
    Tensor(..)
  , unconsLB
  , nilLB
  , consLB
  , appendChain
  , unroll
  , reroll
  , rerollNE
  , splitChain1
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HFunctor
import           Data.HFunctor.Chain.Internal
import           Data.Kind
import           GHC.Generics


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
--
-- Formally, we can say that @t@ enriches a the category of
-- endofunctors with monoid strcture: it turns our endofunctor category
-- into a "monoidal category".
--
-- Different instances of @t@ each enrich the endofunctor category in
-- different ways, giving a different monoidal category.
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
    -- x :*: y       ~ ListF [x,y]      ~ 'toListBy' (x :*: y)
    -- x :*: y :*: z ~ ListF [x,y,z]
    -- -- etc.
    -- @
    --
    -- You can create an "empty" one with 'nilLB', a "singleton" one with
    -- 'inject', or else one from a single @t f f@ with 'toListBy'.
    --
    -- See 'Data.HBifunctor.Associative.NonEmptyBy' for a "non-empty"
    -- version of this type.
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

    -- | Witnesses the property that @i@ is the identity of @t@: @t
    -- f i@ always leaves @f@ unchanged, so we can always just drop the
    -- @i@.
    elim1 :: FunctorBy t f => t f i ~> f

    -- | Witnesses the property that @i@ is the identity of @t@: @t i g@
    -- always leaves @g@ unchanged, so we can always just drop the @i t@.
    elim2 :: FunctorBy t g => t i g ~> g

    -- | If a @'ListBy' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'ListBy' t f@s applied to
    -- themselves into one giant @'ListBy' t f@ containing all of the @t f@s.
    --
    -- Note that this essentially gives an instance for @'SemigroupIn'
    -- t (ListBy t f)@, for any functor @f@; this is witnessed by
    -- 'WrapLB'.
    appendLB    :: t (ListBy t f) (ListBy t f) ~> ListBy t f

    -- | Lets you convert an @'NonEmptyBy' t f@ into a single application of @f@ to
    -- @'ListBy' t f@.
    --
    -- Analogous to a function @'Data.List.NonEmpty.NonEmpty' a -> (a,
    -- [a])@
    --
    -- Note that this is not reversible in general unless we have
    -- @'Matchable' t@.
    splitNE     :: NonEmptyBy t f ~> t f (ListBy t f)

    -- | An @'ListBy' t f@ is either empty, or a single application of @t@ to @f@
    -- and @ListBy t f@ (the "head" and "tail").  This witnesses that
    -- isomorphism.
    --
    -- To /use/ this property, see 'nilLB', 'consLB', and 'unconsLB'.
    splittingLB :: ListBy t f <~> i :+: t f (ListBy t f)

    -- | Embed a direct application of @f@ to itself into a @'ListBy' t f@.
    toListBy   :: t f f ~> ListBy t f
    toListBy   = reviewF (splittingLB @t)
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
    -- 'fromNE' \@(':*:') :: 'NonEmptyF' f a -> 'ListF' f a
    -- fromNE \@'Comp'  :: 'Free1' f a -> 'Free' f a
    -- @
    fromNE :: NonEmptyBy t f ~> ListBy t f
    fromNE = reviewF (splittingLB @t) . R1 . splitNE @t

    {-# MINIMAL intro1, intro2, elim1, elim2, appendLB, splitNE, splittingLB #-}

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
--
-- Note that this essentially gives an instance for @'MonoidIn' t i (ListBy
-- t f)@, for any functor @f@; this is witnessed by 'WrapLB'.
nilLB    :: forall t i f. Tensor t i => i ~> ListBy t f
nilLB    = reviewF (splittingLB @t) . L1

-- | Lets us "cons" an application of @f@ to the front of an @'ListBy' t f@.
consLB   :: Tensor t i => t f (ListBy t f) ~> ListBy t f
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


-- | 'Chain' is a monoid with respect to @t@: we can "combine" them in
-- an associative way.  The identity here is anything made with the 'Done'
-- constructor.
--
-- This is essentially 'biretract', but only requiring @'Tensor' t i@: it
-- comes from the fact that @'Chain1' t i@ is the "free @'MonoidIn' t i@".
-- 'pureT' is 'Done'.
--
-- @since 0.1.1.0
appendChain
    :: forall t i f. Tensor t i
    => t (Chain t i f) (Chain t i f) ~> Chain t i f
appendChain = unroll
            . appendLB
            . hbimap reroll reroll

-- | A type @'ListBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'unroll' makes that successive application explicit,
-- buy converting it to a literal 'Chain' of applications of @t@ to
-- itself.
--
-- @
-- 'unroll' = 'unfoldChain' 'unconsLB'
-- @
unroll
    :: Tensor t i
    => ListBy t f ~> Chain t i f
unroll = unfoldChain unconsLB

-- | A type @'ListBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollNE' takes an explicit 'Chain' of applications of
-- @t@ to itself and rolls it back up into an @'ListBy' t@.
--
-- @
-- 'reroll' = 'foldChain' 'nilLB' 'consLB'
-- @
--
-- Because @t@ cannot be inferred from the input or output, you should call
-- this with /-XTypeApplications/:
--
-- @
-- 'reroll' \@'Control.Monad.Freer.Church.Comp'
--     :: 'Chain' Comp 'Data.Functor.Identity.Identity' f a -> 'Control.Monad.Freer.Church.Free' f a
-- @
reroll
    :: forall t i f. Tensor t i
    => Chain t i f ~> ListBy t f
reroll = foldChain (nilLB @t) consLB

-- | A type @'NonEmptyBy' t@ is supposed to represent the successive application of
-- @t@s to itself.  'rerollNE' takes an explicit 'Chain1' of applications
-- of @t@ to itself and rolls it back up into an @'NonEmptyBy' t@.
--
-- @
-- 'rerollNE' = 'foldChain1' 'inject' 'consNE'
-- @
rerollNE :: Associative t => Chain1 t f ~> NonEmptyBy t f
rerollNE = foldChain1 inject consNE

-- | The "forward" function representing 'splittingChain1'.  Provided here
-- as a separate function because it does not require @'Functor' f@.
splitChain1
    :: forall t i f. Tensor t i
    => Chain1 t f ~> t f (Chain t i f)
splitChain1 = hright (unroll @t) . splitNE @t . rerollNE

