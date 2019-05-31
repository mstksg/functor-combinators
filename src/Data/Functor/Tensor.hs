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
    Tensor(..)
  , rightIdentity
  , leftIdentity
  , Monoidal(..)
    -- HBifunctor(..)
  -- , Tensor(..)
  -- , Monoidal(..)
  -- , F(..)
  , (!$!)
  , inL, inR
  , reconsMF
  , extractT
  , getT, (!*!)
  , collectT
  -- , injectF
  -- , WrappedHBifunctor(..)
  -- , JoinT(..)
  -- , TannenT(..)
  -- , BiffT(..)
  -- , ClownT(..)
  -- , JokerT(..)
  ) where

-- import           Control.Applicative.Lift
-- import           Data.Coerce
-- import           Data.Constraint.Trivial
-- import           Data.Functor.HFunctor
import           Control.Applicative
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Copointed
import           Data.Functor.Apply.Free
import           Data.Functor.Associative
import           Data.Functor.Day               (Day(..))
import           Data.Functor.HFunctor.Internal
import           Data.Functor.HFunctor.IsoF
import           Data.Functor.Identity
import           Data.Functor.Interpret
import           Data.Functor.Plus
import           Data.Kind
import           Data.Proxy
import           GHC.Generics hiding            (C)
import           GHC.Natural
import qualified Data.Functor.Day               as D

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


---- | A useful construction that works like a "linked list" of @t f@ applied
---- to itself multiple times.  That is, it contains @t f f@, @t f (t f f)@,
---- @t f (t f (t f f))@, etc.
----
---- If @t@ is 'Monoidal', then it means we can "collapse" this linked list
---- into some final type @'MF' t@ ('fromF'), and also extract it back into a linked
---- list ('toF').
--data F t i f a = Done (i a)
--               | More (t f (F t i f) a)

--instance (Functor i, Functor (t f (F t i f))) => Functor (F t i f) where
--    fmap f = \case
--      Done x  -> Done (fmap f x)
--      More xs -> More (fmap f xs)

--deriving instance (Show (i a), Show (t f (F t i f) a)) => Show (F t i f a)
--deriving instance (Read (i a), Read (t f (F t i f) a)) => Read (F t i f a)

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

    splitSF  :: SF t f <~> t f (MF t f)
    splitMF  :: MF t f <~> I t :+: SF t f
    -- splitMF = isoF
    --     (hright (_ . consMF @t) . unconsMF @t)
    --     (\case L1 x -> nilMF @t x; R1 y -> fromSF @t y)
    appendMF :: t (MF t f) (MF t f) ~> MF t f

    fromSF   :: SF t f ~> MF t f
    fromSF   = consMF @t . viewF (splitSF @t)
    nilMF    :: I t ~> MF t f
    nilMF    = reviewF (splitMF @t) . L1
    consMF   :: t f (MF t f) ~> MF t f
    consMF   = appendMF . hleft inject
    unconsMF :: MF t f ~> I t :+: t f (MF t f)
    unconsMF = hright (viewF (splitSF @t))
             . viewF (splitMF @t)
    toMF     :: t f f ~> MF t f
    toMF     = appendMF @t . hbimap inject inject

    retractT :: C (MF t) f => t f f ~> f
    retractT = retract . toMF
    interpretT :: C (MF t) h => (f ~> h) -> (g ~> h) -> t f g ~> h
    interpretT f g = retract . toMF . hbimap f g
    pureT  :: C (MF t) f => I t ~> f
    pureT  = retract . nilMF @t

    {-# MINIMAL splitSF, splitMF, appendMF #-}

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

    ---- | A version of 'retract' that works for a 'Tensor'.  It retracts
    ---- /both/ @f@s into a single @f@.
    --retractT :: C (MF t) f => t f f ~> f
    --retractT = retract . toMF

    ---- | A version of 'interpret' that works for a 'Tensor'.  It takes two
    ---- interpreting functions, and interprets both joined functors one
    ---- after the other into @h@.
    --interpretT :: C (MF t) h => (f ~> h) -> (g ~> h) -> t f g ~> h
    --interpretT f g = retract . toMF . hbimap f g

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
    ---- the 'F' type) into @'MF' t f@, the data type representing multiple
    ---- applications of @t f@ to itself.
    ----
    ---- @'F' i ('I' t)@ can be thought of as a "universal" representation of
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
    --fromF :: F t (I t) f ~> MF t f
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
    --toF :: MF t f ~> F t (I t) f
    --toF x = case unconsMF x of
    --  L1 y -> Done y
    --  R1 z -> More . hright toF $ z

    ---- | Append two linked lists of @t f@ applied to itself together.
    ----
    ---- 'fromF', 'toF', and 'appendF' are a way to completely define
    ---- a 'Monoidal' instance; all other methods can be inferred from them.
    ---- In some cases, it can be easier to define these instead of the other
    ---- ones.
    --appendF  :: t (F t (I t) f) (F t (I t) f) ~> F t (I t) f
    --appendF = toF . appendMF . hbimap fromF fromF

    -- {-# MINIMAL nilMF, consMF, unconsMF, appendMF | fromF, toF, appendF #-}

--instance HBifunctor t => HFunctor (F t i) where
--    hmap f = \case
--      Done x  -> Done x
--      More xs -> More . hbimap f (hmap f) $ xs

---- | We can collapse and interpret an @'F' t i@ if we have @'Tensor' i@.
----
---- Note that 'inject' only requires @'Tensor' t@.  This is given as
---- 'injectF'.
--instance (Monoidal t, i ~ I t) => Interpret (F t i) where
--    type C (F t i) = C (MF t)
--    inject    = injectF
--    retract   = \case
--      Done x  -> pureT @t x
--      More xs -> retractT . hright retract $ xs
--    interpret f = \case
--      Done x  -> pureT @t x
--      More xs -> interpretT @t f (interpret f) xs

-- | The inverse of 'unconsMF'.  Calls 'nilMF' on the left (nil) branch,
-- and 'consMF' on the right (cons) branch.
reconsMF :: forall t f. Monoidal t => I t :+: t f (MF t f) ~> MF t f
reconsMF = nilMF @t !*! consMF @t

---- | If we have @'Tensor' t@, we can make a singleton 'F'.
----
---- We can also 'retract' and 'interpret' an 'F' using its 'Interpret'
---- instance.
--injectF :: forall t f. Tensor t => f ~> F t (I t) f
--injectF = More . hright Done . intro1

-- | Useful wrapper over 'retractT' to allow you to directly extract an @a@
-- from a @t f f a@, if @f@ is a valid retraction from @t@, and @f@ is an
-- instance of 'Copointed'.
--
-- Useful @f@s include 'Identity' or related newtype wrappers from
-- base:
--
-- @
-- 'extractT'
--     :: ('Monoidal' t, 'C' ('MF' t) 'Identity')
--     => t 'Identity' 'Identity' a
--     -> a
-- @
extractT
    :: (Monoidal t, C (MF t) f, Copointed f)
    => t f f a
    -> a
extractT = copoint . retractT

-- | Useful wrapper over 'interpret' to allow you to directly extract
-- a value @b@ out of the @t f a@, if you can convert @f x@ into @b@.
--
-- Note that depending on the constraints on the interpretation of @t@, you
-- may have extra constraints on @b@.
--
-- *    If @'C' ('MF' t)@ is 'Data.Constraint.Trivial.Unconstrained', there
--      are no constraints on @b@
-- *    If @'C' ('MF' t)@ is 'Apply', @b@ needs to be an instance of 'Semigroup'
-- *    If @'C' ('MF' t)@ is 'Applicative', @b@ needs to be an instance of 'Monoid'
--
-- For some constraints (like 'Monad'), this will not be usable.
--
-- @
-- -- Return the length of either the list, or the Map, depending on which
-- --   one s in the '+'
-- length !*! length
--     :: ([] :+: Map Int) Char
--     -> Int
--
-- -- Return the length of both the list and the map, added together
-- (Sum . length) !*! (Sum . length)
--     :: Day [] (Map Int) Char
--     -> Sum Int
-- @
getT
    :: (Monoidal t, C (MF t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
getT f g = getConst . interpretT (Const . f) (Const . g)

-- | Infix alias for 'getT'
(!$!)
    :: (Monoidal t, C (MF t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
(!$!) = getT
infixr 5 !$!

-- | Infix alias for 'interpretT'
(!*!)
    :: (Monoidal t, C (MF t) h)
    => (f ~> h)
    -> (g ~> h)
    -> t f g
    ~> h
(!*!) = interpretT
infixr 5 !*!

-- | Useful wrapper over 'getT' to allow you to collect a @b@ from all
-- instances of @f@ and @g@ inside a @t f g a@.
--
-- This will work if @'C' t@ is 'Data.Constraint.Trivial.Unconstrained',
-- 'Apply', or 'Applicative'.
collectT
    :: (Monoidal t, C (MF t) (Const [b]))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> [b]
collectT f g = getConst . interpretT (Const . (:[]) . f) (Const . (:[]) . g)

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

    splitSF = isoF nonEmptyProd ProdNonEmpty
    splitMF = isoF fromListF $ \case
      L1 ~Proxy -> ListF []
      R1 x      -> toListF x
    appendMF (ListF xs :*: ListF ys) = ListF (xs ++ ys)

    nilMF ~Proxy            = ListF []
    consMF (x :*: ListF xs) = ListF $ x : xs
    unconsMF                = hright nonEmptyProd . fromListF
    toMF   (x :*: y       ) = ListF [x, y]

    retractT       (x :*: y) = x <!> y
    interpretT f g (x :*: y) = f x <!> g y
    pureT          _         = zero

instance Tensor Day where
    type I Day = Identity

    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1

instance Monoidal Day where
    type MF Day = Ap

    splitSF = isoF ap1Day DayAp1
    splitMF = isoF fromAp $ \case
      L1 (Identity x) -> pure x
      R1 x            -> toAp x
    appendMF (Day x y z) = z <$> x <*> y

    nilMF              = pure . runIdentity
    consMF (Day x y z) = z <$> inject x <*> y
    unconsMF           = hright ap1Day . fromAp
    toMF   (Day x y z) = z <$> liftAp x <*> liftAp y

    retractT       (Day x y z) = z <$> x <*> y
    interpretT f g (Day x y z) = z <$> f x <*> g y
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

    splitSF  = shiftStep
    splitMF  = isoF R1 (\case L1 v -> absurd1 v; R1 x -> x)
    appendMF = appendSF

    nilMF    = absurd1
    consMF   = consSF
    unconsMF = R1 . stepDown
    toMF     = toSF

    retractT   = retractS
    interpretT = interpretS
    pureT      = absurd1

instance Tensor Comp where
    type I Comp = Identity

    intro1 = (:>>= Identity)
    intro2 = (Identity () :>>=) . const

    elim1 (x :>>= y) = runIdentity . y <$> x
    elim2 (x :>>= y) = y (runIdentity x)

instance Monoidal Comp where
    type MF Comp = Free

    splitSF = isoF free1Comp CompFree1
    splitMF = isoF fromFree $ \case
      L1 (Identity x) -> pure x
      R1 x            -> toFree x
    appendMF (x :>>= y) = x >>= y

    nilMF             = pure . runIdentity
    consMF (x :>>= y) = Free $ \p b -> b x $ \z -> runFree (y z) p b
    unconsMF x        = runFree x (L1 . Identity) $ \y n -> R1 $
      y :>>= ( ( pure . runIdentity
             !*! (\case z :>>= h -> liftFree z >>= h)
               )
             . n
             )
    toMF   (x :>>= y) = liftFree x >>= (inject . y)

    retractT       (x :>>= y) = x >>= y
    interpretT f g (x :>>= y) = f x >>= (g . y)
    pureT                     = pure . runIdentity

---- | Form an 'HFunctor' by applying the same input twice to an
---- 'HBifunctor'.
--newtype JoinT t f a = JoinT { runJoinT :: t f f a }

--deriving instance Functor (t f f) => Functor (JoinT t f)

--instance HBifunctor t => HFunctor (JoinT t) where
--    hmap f (JoinT x) = JoinT $ hbimap f f x

---- | Form an 'HBifunctor' by wrapping another 'HBifunctor' in a 'HFunctor'.
--newtype TannenT t p f g a = TannenT { runTannenT :: t (p f g) a }

--deriving instance Functor (t (p f g)) => Functor (TannenT t p f g)

--instance (HFunctor t, HBifunctor p) => HBifunctor (TannenT t p) where
--    hbimap f g (TannenT x) = TannenT (hmap (hbimap f g) x)

--deriving via (WrappedHBifunctor (TannenT (t :: (Type -> Type) -> Type -> Type) p) f)
--    instance (HFunctor t, HBifunctor p) => HFunctor (TannenT t p f)

---- | Form an 'HBifunctor' over two 'HFunctor's.
--newtype BiffT p s t f g a = BiffT { runBiffT :: p (s f) (t g) a }

--deriving instance Functor (p (s f) (t g)) => Functor (BiffT p s t f g)

--instance (HBifunctor p, HFunctor s, HFunctor t) => HBifunctor (BiffT p s t) where
--    hbimap f g (BiffT x) = BiffT (hbimap (hmap f) (hmap g) x)

--deriving via (WrappedHBifunctor (BiffT (p :: (Type -> Type) -> (Type -> Type) -> Type -> Type) s t) f)
--    instance (HBifunctor p, HFunctor s, HFunctor t) => HFunctor (BiffT p s t f)

---- | Form an 'HBifunctor' over a 'HFunctor' by ignoring the second
---- argument.
--newtype ClownT t f g a = ClownT { runClownT :: t f a }

--deriving instance Functor (t f) => Functor (ClownT t f g)

--instance HFunctor t => HBifunctor (ClownT t) where
--    hbimap f _ (ClownT x) = ClownT (hmap f x)

--deriving via (WrappedHBifunctor (ClownT t) f)
--    instance HFunctor t => HFunctor (ClownT t f)

---- | Form an 'HBifunctor' over a 'HFunctor' by ignoring the first
---- argument.
--newtype JokerT t f g a = JokerT { runJokerT :: t g a }

--deriving instance Functor (t g) => Functor (JokerT t f g)

--instance HFunctor t => HBifunctor (JokerT t) where
--    hbimap _ g (JokerT x) = JokerT (hmap g x)

--deriving via (WrappedHBifunctor (JokerT t) f)
--    instance HFunctor t => HFunctor (JokerT t f)
