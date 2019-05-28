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
-- with combinators that combine two functors "together".
--
-- The binary analog of 'HFunctor' is 'HBifunctor': we can map
-- a structure-transforming function over both of the transformed functors.
--
-- The binary analog of 'Interpret' is 'Monoidal' (and 'Tensor').  If your
-- combinator is an instance of 'Monoidal', it means that you can "squish"
-- both arguments together into an 'Interpret'.  For example:
--
-- @
-- 'toTM' :: (f ':*:' f) a -> 'ListF' f a
-- 'toTM' :: 'Comp' f f a -> 'Free' f a
-- 'toTM' :: 'Day' f f a -> 'Ap' f a
-- @
module Data.Functor.Tensor (
    HBifunctor(..)
  , Tensor(..)
  , Monoidal(..)
  , F(..)
  , (!$!)
  , inL, inR
  , reconsTM
  , extractT
  , getT, (!*!)
  , collectT
  , injectF
  , WrappedHBifunctor(..)
  , JoinT(..)
  , TannenT(..)
  , BiffT(..)
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Control.Natural
import           Data.Copointed
import           Data.Functor.Apply.Free
import           Data.Functor.Day               (Day(..))
import           Data.Functor.HFunctor
import           Data.Functor.HFunctor.Internal
import           Data.Functor.Identity
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
class HBifunctor t => Tensor t where
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

    elim1  :: Functor f => t f (I t) ~> f
    elim2  :: Functor g => t (I t) g ~> g

    assoc    :: (Functor f, Functor g, Functor h) => t f (t g h) ~> t (t f g) h
    disassoc :: (Functor f, Functor g, Functor h) => t (t f g) h ~> t f (t g h)

    {-# MINIMAL intro1, intro2, elim1, elim2, assoc, disassoc #-}

-- | A useful construction that works like a "linked list" of @t f@ applied
-- to itself multiple times.  That is, it contains @t f f@, @t f (t f f)@,
-- @t f (t f (t f f))@, etc.
--
-- If @t@ is 'Monoidal', then it means we can "collapse" this linked list
-- into some final type @'TM' t@ ('fromF'), and also extract it back into a linked
-- list ('toF').
data F t i f a = Done (i a)
               | More (t f (F t i f) a)

instance (Functor i, Functor (t f (F t i f))) => Functor (F t i f) where
    fmap f = \case
      Done x  -> Done (fmap f x)
      More xs -> More (fmap f xs)

deriving instance (Show (i a), Show (t f (F t i f) a)) => Show (F t i f a)
deriving instance (Read (i a), Read (t f (F t i f) a)) => Read (F t i f a)

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
-- type 'TM' is the "repeated aplications of @t@" type.
--
-- See documentation of "Data.Functor.Tensor" for information on how to
-- define instances of this typeclass.
class (Tensor t, Interpret (TM t)) => Monoidal t where
    type TM t :: (Type -> Type) -> Type -> Type

    -- | If @'TM' t f@ represents multiple applications of @t f@ with
    -- itself, then @nilTM@ gives us "zero applications of @f@".
    --
    -- Note that @t@ cannot be inferred from the type of 'nilTM', so this
    -- function must always be called with -XTypeApplications:
    --
    -- @
    -- 'nilTM' \@'Day' :: 'Identity' '~>' 'Ap' f
    -- 'nilTM' \@'Comp' :: 'Identity' '~>' 'Free' f
    -- 'nilTM' \@(':*:') :: 'Proxy' '~>' 'ListF' f
    -- @
    --
    -- Together with 'consTM', forms an inverse with 'unconsTM'.
    nilTM    :: I t ~> TM t f
    nilTM    = fromF @t . Done

    -- | Prepend an application of @t f@ to the front of a @'TM' t f@.
    --
    -- Together with 'nilTM', forms an inverse with 'unconsTM'.
    consTM   :: t f (TM t f) ~> TM t f
    consTM     = fromF . More . hright toF

    -- | If a @'TM' t f@ represents multiple applications of @t f@ to itself,
    -- 'unconsTM' lets us break it up into two possibilities:
    --
    -- 1.   The @'TM' t f@ had no applications of @f@
    -- 2.   The @'TM' t f@ had at least one application of @f@; we return
    --      the "first" @f@ applied to the rest of the @f@s.
    --
    -- Should form an inverse with 'reconsTM':
    --
    -- @
    -- 'reconsTM' . 'unconsTM' == id
    -- 'unconsTM' . 'reconsTM' == id
    -- @
    --
    -- where 'reconsTM' is 'nilTM' on the left side of the ':+:', and
    -- 'consTM' on the right side of the ':+:'.
    unconsTM   :: TM t f ~> I t :+: t f (TM t f)
    unconsTM m = case toF @t m of
      Done x  -> L1 x
      More xs -> R1 . hright fromF $ xs

    -- | If a @'TM' t f@ represents multiple applications of @t f@ to
    -- itself, then we can also "append" two @'TM' t f@s applied to
    -- themselves into one giant @'TM' t f@ containing all of the @t f@s.
    appendTM :: t (TM t f) (TM t f) ~> TM t f
    appendTM = fromF . appendF . hbimap toF toF

    -- | Convert a linked list of @t f@s applied to themselves (stored in
    -- the 'F' type) into @'TM' t f@, the data type representing multiple
    -- applications of @t f@ to itself.
    --
    -- @'F' i ('I' t)@ can be thought of as a "universal" representation of
    -- multiple-applications-to-self, and @'TM' t@ can be thought of as
    -- a tailor-made represenation for your specific @'Tensor' t@.
    --
    -- @
    -- 'fromF' . 'toF' == id
    -- 'toF' . 'fromF' == id
    -- @
    --
    -- 'fromF', 'toF', and 'appendF' are a way to completely define
    -- a 'Monoidal' instance; all other methods can be inferred from them.
    -- In some cases, it can be easier to define these instead of the other
    -- ones.
    fromF :: F t (I t) f ~> TM t f
    fromF = \case
      Done x  -> nilTM @t x
      More xs -> consTM . hright fromF $ xs

    -- | The inverse of 'fromF': convert a @'TM' t f@ into a linked list of
    -- @t f@s applied to themselves.  See 'fromF' for more information.
    --
    -- 'fromF', 'toF', and 'appendF' are a way to completely define
    -- a 'Monoidal' instance; all other methods can be inferred from them.
    -- In some cases, it can be easier to define these instead of the other
    -- ones.
    toF :: TM t f ~> F t (I t) f
    toF x = case unconsTM x of
      L1 y -> Done y
      R1 z -> More . hright toF $ z

    -- | Append two linked lists of @t f@ applied to itself together.
    --
    -- 'fromF', 'toF', and 'appendF' are a way to completely define
    -- a 'Monoidal' instance; all other methods can be inferred from them.
    -- In some cases, it can be easier to define these instead of the other
    -- ones.
    appendF  :: t (F t (I t) f) (F t (I t) f) ~> F t (I t) f
    appendF = toF . appendTM . hbimap fromF fromF

    -- | A version of 'retract' that works for a 'Tensor'.  It retracts
    -- /both/ @f@s into a single @f@.
    retractT :: C (TM t) f => t f f ~> f
    retractT = retract . toTM

    -- | A version of 'interpret' that works for a 'Tensor'.  It takes two
    -- interpreting functions, and interprets both joined functors one
    -- after the other into @h@.
    interpretT :: C (TM t) h => (f ~> h) -> (g ~> h) -> t f g ~> h
    interpretT f g = retractT . hbimap f g

    -- | If we have an instance of @t@, we can generate an @f@ based on how
    -- it interacts with @t@.
    --
    -- Specialized (and simplified), this type is:
    --
    -- @
    -- 'pureT' \@'Day'   :: 'Applicative' f => a -> f a  -- 'pure'
    -- 'pureT' \@'Comp'  :: 'Monad' f => a -> f a    -- 'return'
    -- 'pureT' \@(':*:') :: 'Plus' f => f a          -- 'zero'
    -- @
    pureT  :: C (TM t) f => I t ~> f
    pureT  = retract . fromF @t . Done

    -- | Embed a direct application of @f@ to itself into a @'TM' t f@.
    toTM     :: t f f ~> TM t f
    toTM     = fromF . More . hright (More . hright Done . intro1)

    {-# MINIMAL nilTM, consTM, unconsTM, appendTM | fromF, toF, appendF #-}

instance HBifunctor t => HFunctor (F t i) where
    hmap f = \case
      Done x  -> Done x
      More xs -> More . hbimap f (hmap f) $ xs

-- | We can collapse and interpret an @'F' t i@ if we have @'Tensor' i@.
--
-- Note that 'inject' only requires @'Tensor' t@.  This is given as
-- 'injectF'.
instance (Monoidal t, i ~ I t) => Interpret (F t i) where
    type C (F t i) = C (TM t)
    inject    = injectF
    retract   = \case
      Done x  -> pureT @t x
      More xs -> retractT . hright retract $ xs
    interpret f = \case
      Done x  -> pureT @t x
      More xs -> interpretT @t f (interpret f) xs

-- | The inverse of 'unconsTM'.  Calls 'nilTM' on the left (nil) branch,
-- and 'consTM' on the right (cons) branch.
reconsTM :: forall t f. Monoidal t => I t :+: t f (TM t f) ~> TM t f
reconsTM = interpretT (nilTM @t) (consTM @t)

-- | If we have @'Tensor' t@, we can make a singleton 'F'.
--
-- We can also 'retract' and 'interpret' an 'F' using its 'Interpret'
-- instance.
injectF :: forall t f. Tensor t => f ~> F t (I t) f
injectF = More . hright Done . intro1

-- | Useful wrapper over 'retractT' to allow you to directly extract an @a@
-- from a @t f f a@, if @f@ is a valid retraction from @t@, and @f@ is an
-- instance of 'Copointed'.
--
-- Useful @f@s include 'Identity' or related newtype wrappers from
-- base:
--
-- @
-- 'extractT'
--     :: ('Monoidal' t, 'C' ('TM' t) 'Identity')
--     => t 'Identity' 'Identity' a
--     -> a
-- @
extractT
    :: (Monoidal t, C (TM t) f, Copointed f)
    => t f f a
    -> a
extractT = copoint . retractT

-- | Useful wrapper over 'interpret' to allow you to directly extract
-- a value @b@ out of the @t f a@, if you can convert @f x@ into @b@.
--
-- Note that depending on the constraints on the interpretation of @t@, you
-- may have extra constraints on @b@.
--
-- *    If @'C' ('TM' t)@ is 'Unconstrained', there are no constraints on @b@
-- *    If @'C' ('TM' t)@ is 'Apply', @b@ needs to be an instance of 'Semigroup'
-- *    If @'C' ('TM' t)@ is 'Applicative', @b@ needs to be an instance of 'Monoid'
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
    :: (Monoidal t, C (TM t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
getT f g = getConst . interpretT (Const . f) (Const . g)

-- | Infix alias for 'getT'
(!$!)
    :: (Monoidal t, C (TM t) (Const b))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> b
(!$!) = getT
infixr 5 !$!

-- | Infix alias for 'interpretT'
(!*!)
    :: (Monoidal t, C (TM t) h)
    => (f ~> h)
    -> (g ~> h)
    -> t f g
    ~> h
(!*!) = interpretT
infixr 5 !*!

-- | Useful wrapper over 'getT' to allow you to collect a @b@ from all
-- instances of @f@ and @g@ inside a @t f g a@.
--
-- This will work if @'C' t@ is 'Unconstrained', 'Apply', or 'Applicative'.
collectT
    :: (Monoidal t, C (TM t) (Const [b]))
    => (forall x. f x -> b)
    -> (forall x. g x -> b)
    -> t f g a
    -> [b]
collectT f g = getConst . interpretT (Const . (:[]) . f) (Const . (:[]) . g)

-- | Convenient wrapper over 'intro1' that lets us introduce an arbitrary
-- functor @g@ to the right of an @f@.
inL
    :: forall t f g a. (Monoidal t, C (TM t) g)
    => f a
    -> t f g a
inL = hright (pureT @t) . intro1 @t

-- | Convenient wrapper over 'intro2' that lets us introduce an arbitrary
-- functor @f@ to the right of a @g@.
inR
    :: forall t f g a. (Monoidal t, C (TM t) f)
    => g a
    -> t f g a
inR = hleft (pureT @t) . intro2 @t

instance Tensor (:*:) where
    type I (:*:) = Proxy

    intro1 = (:*: Proxy)
    intro2 = (Proxy :*:)

    elim1 (x :*: _) = x
    elim2 (_ :*: y) = y

    assoc (x :*: (y :*: z)) = (x :*: y) :*: z
    disassoc ((x :*: y) :*: z) = x :*: (y :*: z)

instance Monoidal (:*:) where
    type TM (:*:) = ListF

    nilTM ~Proxy = ListF []
    consTM (x :*: y) = ListF $ x : runListF y
    unconsTM = hright nonEmptyProd . fromListF
    appendTM (ListF xs :*: ListF ys) = ListF (xs ++ ys)

    fromF = \case
      Done ~Proxy -> ListF []
      More (x :*: y) -> ListF $ x : runListF (fromF y)
    toF = (Done !*! More . hright toF . nonEmptyProd)
        . fromListF
    appendF (x :*: y) = case x of
      Done ~Proxy       -> y
      More (x' :*: x'') -> More (x' :*: appendF (x'' :*: y))

    retractT (x :*: y) = x <!> y
    interpretT f g (x :*: y) = f x <!> g y
    toTM (x :*: y) = ListF [x, y]
    pureT _ = zero

instance Tensor Day where
    type I Day = Identity

    intro1   = D.intro2
    intro2   = D.intro1
    elim1    = D.elim2
    elim2    = D.elim1
    assoc    = D.assoc
    disassoc = D.disassoc

instance Monoidal Day where
    type TM Day = Ap

    nilTM              = pure . runIdentity
    consTM (Day x y z) = z <$> liftAp x <*> y
    unconsTM           = hright ap1Day . fromAp
    appendTM (Day x y z) = z <$> x <*> y

    fromF = \case
      Done (Identity x) -> pure x
      More (Day x y z)  -> z <$> liftAp x <*> fromF y
    toF = (Done !*! More . hright toF . ap1Day )
        . fromAp
    appendF (Day x y f) = case x of
      Done (Identity x')  -> f x' <$> y
      More (Day x' y' f') -> More $ Day x' (appendF (Day y' y (,))) $
        \a (b, c) -> f (f' a b) c

    retractT (Day x y z) = z <$> x <*> y
    interpretT f g (Day x y z) = z <$> f x <*> g y
    toTM (Day x y z) = z <$> liftAp x <*> liftAp y
    pureT = pure . runIdentity

instance Tensor (:+:) where
    type I (:+:) = VoidT

    intro1 = L1
    intro2 = R1
    elim1  = \case
      L1 x -> x
      R1 y -> absurdT y
    elim2  = \case
      L1 x -> absurdT x
      R1 y -> y
    assoc = \case
      L1 x      -> L1 (L1 x)
      R1 (L1 y) -> L1 (R1 y)
      R1 (R1 z) -> R1 z
    disassoc = \case
      L1 (L1 x) -> L1 x
      L1 (R1 y) -> R1 (L1 y)
      R1 z      -> R1 (R1 z)

instance Monoidal (:+:) where
    type TM (:+:) = Step

    nilTM = absurdT
    consTM = \case
      L1 x          -> Step 0       x
      R1 (Step n y) -> Step (n + 1) y
    unconsTM (Step n x) = R1 $ case minusNaturalMaybe n 1 of
      Nothing -> L1 x
      Just m  -> R1 (Step m x)
    appendTM = \case
      L1 x -> x
      R1 y -> y

    fromF = \case
      Done x      -> absurdT x
      More (L1 x) -> Step 0 x
      More (R1 y) ->
        let Step n z = fromF y
        in  Step (n + 1) z
    toF (Step n x) = go n
      where
        go (flip minusNaturalMaybe 1 -> i) = case i of
          Nothing -> More (L1 x)
          Just j  -> More (R1 (go j))
    appendF = \case
      L1 x -> x
      R1 y -> y

    retractT = \case
      L1 x -> x
      R1 y -> y
    interpretT f g = \case
      L1 x -> f x
      R1 y -> g y
    toTM = \case
      L1 x -> Step 0 x
      R1 y -> Step 1 y
    pureT = absurdT

instance Tensor Comp where
    type I Comp = Identity

    intro1 = (:>>= Identity)
    intro2 = (Identity () :>>=) . const

    elim1 (x :>>= y) = runIdentity . y <$> x
    elim2 (x :>>= y) = y (runIdentity x)

    assoc (x :>>= y) = (x :>>= (unComp . y)) :>>= id
    disassoc ((x :>>= y) :>>= z) = x :>>= ((:>>= z) . y)

instance Monoidal Comp where
    type TM Comp = Free

    nilTM  = pure . runIdentity
    consTM (x :>>= y) = Free $ \p b -> b x $ \z -> runFree (y z) p b

    fromF = \case
      Done x -> pure . runIdentity $ x
      More (x :>>= y) -> Free $ \p b -> b x $ \z -> runFree (fromF (y z)) p b
    toF x = runFree x (Done . Identity) $ \y z -> More (y :>>= z)
    appendF (x :>>= y) = case x of
      Done (Identity z)   -> y z
      More (z :>>= q) -> More $ z :>>= (appendF . comp . fmap y . q)

    retractT (x :>>= y) = x >>= y
    pureT = pure . runIdentity
    toTM (x :>>= y) = Free $ \p b -> b x (($ p) . b . y)

-- | Form an 'HFunctor' by applying the same input twice to an
-- 'HBifunctor'.
data JoinT t f a = JoinT { runJoinT :: t f f a }

deriving instance Functor (t f f) => Functor (JoinT t f)

instance HBifunctor t => HFunctor (JoinT t) where
    hmap f (JoinT x) = JoinT $ hbimap f f x

-- | Form an 'HBifunctor' by wrapping another 'HBifunctor' in a 'HFunctor'.
newtype TannenT t p f g a = TannenT { runTannenT :: t (p f g) a }

deriving instance Functor (t (p f g)) => Functor (TannenT t p f g)

instance (HFunctor t, HBifunctor p) => HBifunctor (TannenT t p) where
    hbimap f g (TannenT x) = TannenT (hmap (hbimap f g) x)

deriving via (WrappedHBifunctor (TannenT (t :: (Type -> Type) -> Type -> Type) p) f)
    instance (HFunctor t, HBifunctor p) => HFunctor (TannenT t p f)

-- | Form an 'HBifunctor' over two 'HFunctor's.
newtype BiffT p s t f g a = BiffT { runBiffT :: p (s f) (t g) a }

deriving instance Functor (p (s f) (t g)) => Functor (BiffT p s t f g)

instance (HBifunctor p, HFunctor s, HFunctor t) => HBifunctor (BiffT p s t) where
    hbimap f g (BiffT x) = BiffT (hbimap (hmap f) (hmap g) x)

deriving via (WrappedHBifunctor (BiffT (p :: (Type -> Type) -> (Type -> Type) -> Type -> Type) s t) f)
    instance (HBifunctor p, HFunctor s, HFunctor t) => HFunctor (BiffT p s t f)
