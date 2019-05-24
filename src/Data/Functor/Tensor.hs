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
-- There are two ways to write a 'Monoidal' instance:
--
-- 1.   Define 'nilTM', 'consTM', 'unconsTM', and 'appendTM'.  These allow
--      you to manipulate @'TM' t@ as if it were a "list" of @f@s appended
--      together with @t@.
--
-- 2.   Define 'fromF', 'toF', and 'appendF'.  'F' is a special data type
--      that literally represents a linked list of @f@s appended together
--      with @t@.  The default definitions of 'nilTM', 'consTM', etc. then
--      work on this representation.
--
-- Additionally, this class contains 'retractT', 'interpretT', 'pureT',
-- and 'toTM'.  These are useful functions of using @t@ as an interpreter
-- combinator.  They can all be derived from other methods, but they are
-- provided as a part of the typeclass to allow implementors to provide
-- more efficient versions.
module Data.Functor.Tensor (
    HBifunctor(..)
  , Tensor(..)
  , reconsTM
  , Monoidal(..)
  , F(..)
  , injectF, retractF, interpretF
  , WrappedHBifunctor(..)
  , JoinT(..)
  ) where

import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Natural
import           Data.Function
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
--      `t` h).
--
-- The methods in this class provide us useful ways of navigating
-- a @'Tensor' t@ with respect to this property.
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
    intro2 :: Functor g => g ~> t (I t) g

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
    fromF :: F t (I t) f ~> TM t f
    fromF = \case
      Done x  -> nilTM @t x
      More xs -> consTM . hright fromF $ xs

    -- | The inverse of 'fromF': convert a @'TM' t f@ into a linked list of
    -- @t f@s applied to themselves.  See 'fromF' for more information.
    toF :: TM t f ~> F t (I t) f
    toF x = case unconsTM x of
      L1 y -> Done y
      R1 z -> More . hright toF $ z

    -- | Append two linked lists of @t f@ applied to itself together.
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

-- | The inverse of 'unconsTM'.  Calls 'nilTM' on the left (nil) branch,
-- and 'consTM' on the right (cons) branch.
reconsTM :: forall t f. Monoidal t => I t :+: t f (TM t f) ~> TM t f
reconsTM = interpretT (nilTM @t) (consTM @t)

-- | If we have @'Tensor' t@, we can make a singleton 'F'.
injectF :: forall t f. Tensor t => f ~> F t (I t) f
injectF = More . hright Done . intro1

-- | If we have @'Monoidal' t@, we can collapse all @t f@s in the 'F' into
-- a single @f@.
retractF
    :: forall t f. (Monoidal t, C (TM t) f)
    => F t (I t) f ~> f
retractF = \case
    Done x  -> pureT @t x
    More xs -> retractT . hright retractF $ xs

-- | If we have @'Monoidal' t@, we can interpret all of the @f@s in the 'F'
-- into a final target context @g@, given an @f@-to-@g@ interpreting
-- function.
interpretF
    :: forall t f g. (Monoidal t, C (TM t) g)
    => (f ~> g)
    -> F t (I t) f ~> g
interpretF f = \case
    Done x  -> pureT @t x
    More xs -> interpretT @t f (interpretF f) xs

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
    unconsTM (ListF xs) = case xs of
      []   -> L1 Proxy
      y:ys -> R1 $ y :*: ListF ys
    appendTM (ListF xs :*: ListF ys) = ListF (xs ++ ys)

    fromF = \case
      Done ~Proxy -> ListF []
      More (x :*: y) -> ListF $ x : runListF (fromF y)
    toF (ListF xs) = case xs of
      []   -> Done Proxy
      y:ys -> More (y :*: toF (ListF ys))
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
    unconsTM = \case
      Pure x -> L1 $ Identity x
      Ap x y -> R1 $ Day x y (&)
    appendTM (Day x y z) = z <$> x <*> y

    fromF = \case
      Done (Identity x) -> pure x
      More (Day x y z)  -> z <$> liftAp x <*> fromF y
    toF = \case
      Pure x -> Done $ Identity x
      Ap x y -> More $ Day x (toF y) (&)
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

data JoinT t f a = JoinT { runJoinT :: t f f a }

deriving instance Functor (t f f) => Functor (JoinT t f)

instance HBifunctor t => HFunctor (JoinT t) where
    hmap f (JoinT x) = JoinT $ hbimap f f x

