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
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeFamilies               #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}
{-# LANGUAGE UndecidableInstances       #-}
{-# LANGUAGE ViewPatterns               #-}

module Data.Functor.Combinator.Class (
    type (~>)
  , HFunctor(..)
  , Interpret(..)
  , HBifunctor(..)
  , Tensor(..)
  , Monoidal(..)
  , F(..)
  , injectF, retractF, interpretF
  , WrappedHBifunctor(..)
  ) where

import           Control.Applicative
import           Control.Applicative.Free
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Monad.Freer.Church
import           Data.Function
import           Data.Functor.Coyoneda
import           Data.Functor.Day            (Day(..))
import           Data.Functor.Identity
import           Data.Functor.Plus
import           Data.Kind
import           Data.Proxy
import           GHC.Generics hiding         (C)
import           GHC.Natural
import qualified Control.Alternative.Free    as Alt
import qualified Control.Monad.Free.Church   as MC
import qualified Data.Functor.Day            as D

-- | The type of a natural transformation between @f@ and @g@.  Essentially
-- translates one functor into another, leaving its parameter unchanged.
type f ~> g = forall x. f x -> g x

infixr 0 ~>

-- | An 'HFunctor' can be thought of a unary "functor transformer" ---
-- a basic functor combinator.  It takes a functor as input and returns
-- a functor as output.
--
-- It "enhances" a functor with extra structure (sort of like how a monad
-- transformer enhances a 'Monad' with extra structure).
--
-- As a uniform inteface, we can "swap the underlying functor" (also
-- sometimes called "hoisting").  This is what 'hmap' does: it lets us swap
-- out the @f@ in a @t f@ for a @t g@.
--
-- For example, the free monad 'Free' takes a 'Functor' and returns a new
-- 'Functor'.  In the process, it provides a monadic structure over @f@.
-- 'hmap' lets us turn a @'Free' f@ into a @'Free' g@: a monad built over
-- @f@ can be turned into a monad built over @g@.
--
-- For the ability to move in and out of the enhanced functor, see
-- 'Interpret'.
class HFunctor t where
    -- | If we can turn an @f@ into a @g@, then we can turn a @t f@ into
    -- a @t g@.
    --
    -- It must be the case that
    --
    -- @
    -- 'hmap' 'id' == id
    -- @
    --
    -- Essentially, @'t' f@ adds some "extra structure" to @f@.  'hmap'
    -- must swap out the functor, /without affecting the added structure/.
    --
    -- For example, @'ListF' f a@ is essentially a list of @f a@s.  If we
    -- 'hmap' to swap out the @f a@s for @g a@s, then we must ensure that
    -- the "added structure" (here, the number of items in the list)
    -- remains the same.  So, 'hmap' must preserve the number of items in
    -- the list.
    --
    -- The law @'hmap' 'id' == id@ is a way of formalizing this informal
    -- property.
    --
    hmap :: f ~> g -> t f ~> t g

    {-# MINIMAL hmap #-}

-- | An 'Interpret' lets us move in and out of the "enhanced" 'Functor'.
--
-- For example, @'Free' f@ is @f@ enhanced with monadic structure.  We get:
--
-- @
-- 'inject'    :: f a -> 'Free' f a
-- 'interpret' :: 'Monad' m => (forall x. f x -> m x) -> 'Free' f a -> m a
-- @
--
-- 'inject' will let us use our @f@ inside the enhanced @'Free' f@.
-- 'interpret' will let us "extract" the @f@ from a @'Free' f@ if
-- we can give an /interpreting function/ that interprets @f@ into some
-- target 'Monad'.
--
-- The type family 'C' tells us the typeclass constraint of the "target"
-- functor.  For 'Free', it is 'Monad', but for other 'Interpret'
-- instances, we might have other constraints.
--
-- We enforce that:
--
-- @
-- 'interpret' id . 'inject' == id
-- @
--
-- That is, if we lift a value into our structure, then immediately
-- interpret it out as itself, it should lave the value unchanged.
class HFunctor t => Interpret t where
    -- | The constraint on the target context of 'interpret'.
    type C t :: (Type -> Type) -> Constraint

    -- | Lift an @f@ into the enhanced @t f@ structure.
    -- Analogous to 'lift' from 'MonadTrans'.
    inject  :: f ~> t f

    -- | Remove the @f@ out of the enhanced @t f@ structure, provided that
    -- @f@ satisfies the necessary constraints.  If it doesn't, it needs to
    -- be properly 'interpret'ed out.
    retract :: C t f => t f ~> f
    retract = interpret id

    -- | Given an "interpeting function" from @f@ to @g@, interpret the @f@
    -- out of the @t f@ into a final context @g@.
    interpret :: C t g => (f ~> g) -> t f ~> g
    interpret f = retract . hmap f

    {-# MINIMAL inject, (retract | interpret) #-}

-- | A 'HBifunctor' is like an 'HFunctor', but it enhances /two/ different
-- functors instead of just one.
--
-- Usually, it enhaces them "together" in some sort of combining way.
--
-- This typeclass provides a uniform instance for "swapping out" or
-- "hoisting" the enhanced functors.   We can hoist the first one with
-- 'hleft', the second one with 'hright', or both at the same time with
-- 'hbimap'.
--
-- For example, the @f :*: g@ type gives us "both @f@ and @g@":
--
-- @
-- data (f ':*:' g) a = f a :*: g a
-- @
--
-- It combines both @f@ and @g@ into a unified structure --- here, it does
-- it by providing both @f@ and @g@.
--
-- The single law is:
--
-- @
-- 'hbimap' 'id' id == id
-- @
--
-- This ensures that 'hleft', 'hright', and 'hbimap' do not affect the
-- structure that @t@ adds on top of the underlying functors.
class HBifunctor t where
    -- | Swap out the first transformed functor.
    hleft  :: f ~> j -> t f g ~> t j g
    hleft = (`hbimap` id)

    -- | Swap out the second transformed functor.
    hright :: g ~> k -> t f g ~> t f k
    hright = hbimap id

    -- | Swap out both transformed functors at the same time.
    hbimap :: f ~> j -> g ~> k -> t f g ~> t j k
    hbimap f g = hleft f . hright g

    {-# MINIMAL hleft, hright | hbimap #-}

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

instance (Functor i, forall g. Functor g => Functor (t f g)) => Functor (F t i f) where
    fmap f = \case
      Done x  -> Done (fmap f x)
      More xs -> More (fmap f xs)

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
-- There are two ways to write an instance:
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
--      The advantage of this family of functions is that they allow you to
--      work with many different @'TM' t@ types under a uniform interface.
--      For example, @'F' 'Day' 'Identity'@ gives you 'Ap', @'F' 'Comp'
--      'Identity'@ gives you 'Free', and @'F' (':*:') 'Proxy'@ gives you
--      'ListF'.  However, most people usually don't need to deal with this
--      representation --- it's mostly useful if you are defining new
--      instances.
--
-- Additionally, this class contains 'retractT', 'interpretT', 'pureT',
-- and 'toTM'.  These are useful functions of using 't' as an interpreter
-- combinator.  They can all be derived from other methods, but they are
-- provided as a part of the typeclass to allow implementors to provide
-- more efficient versions.
class (Tensor t, Interpret (TM t)) => Monoidal t where
    type TM t :: (Type -> Type) -> Type -> Type

    -- | If @'TM' t f@ represents multiple applications of @t f@ with
    -- itself, then @nilTM@ gives us "zero applications of @f@".
    nilTM    :: I t ~> TM t f
    nilTM    = fromF @t . Done

    -- | Prepend an application of @t f@ to the front of a @'TM' t f@.
    consTM   :: t f (TM t f) ~> TM t f
    consTM     = fromF . More . hright toF

    -- | If a @'TM' t f@ represents multiple applications of @t f@ to itself,
    -- 'unconsTM' lets us break it up into two possibilities:
    --
    -- 1.   The @'TM' t f@ had no applications of @f@
    -- 2.   The @'TM' t f@ had at least one application of @f@; we return
    --      the "first" @f@ applied to the rest of the @f@s.
    unconsTM   :: TM t f ~> (I t :+: t f (TM t f))
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
    -- 'pureT' @'Day'   :: 'Applicative' f => a -> f a  -- 'pure'
    -- 'pureT' @'Comp'  :: 'Monad' f => a -> f a    -- 'return'
    -- 'pureT' @(':*:') :: 'Plus' f => f a          -- 'zero'
    -- @
    pureT  :: C (TM t) f => I t ~> f
    pureT  = retract . fromF @t . Done

    -- | Embed a direct application of @f@ to itself into a @'TM' t f@.
    --
    -- Conceptually:
    --
    -- @
    -- 'toTM' (x, y) = [x, y]
    --             = x : y : []
    -- @
    --
    -- If you 'unconsTM' the result, you'll get the first original @f@ consed
    -- with the second original @f@ consed with a 'nilTM'.
    toTM     :: t f f ~> TM t f
    toTM     = fromF . More . hright (More . hright Done . intro1)

    {-# MINIMAL nilTM, consTM, unconsTM, appendTM | fromF, toF, appendF #-}

instance HBifunctor t => HFunctor (F t i) where
    hmap f = \case
      Done x  -> Done x
      More xs -> More . hbimap f (hmap f) $ xs

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

instance HFunctor Coyoneda where
    hmap = hoistCoyoneda

instance Interpret Coyoneda where
    type C Coyoneda = Functor
    inject  = liftCoyoneda
    retract = lowerCoyoneda
    interpret f (Coyoneda g x) = g <$> f x

instance HFunctor Ap where
    hmap = hoistAp

instance Interpret Ap where
    type C Ap = Applicative
    inject    = liftAp
    interpret = runAp

instance HBifunctor (:*:) where
    hleft  f (x :*: y) = f x :*:   y
    hright g (x :*: y) =   x :*: g y
    hbimap f g (x :*: y) = f x :*: g y

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

    toTM (x :*: y) = ListF [x, y]

instance HFunctor ListF where
    hmap f (ListF xs) = ListF (map f xs)

instance Interpret ListF where
    type C ListF = Plus
    inject = ListF . (:[])
    retract = foldr (<!>) zero . runListF

instance HFunctor Alt.Alt where
    hmap = Alt.hoistAlt

instance Interpret Alt.Alt where
    type C Alt.Alt = Alternative
    inject = Alt.liftAlt
    interpret = Alt.runAlt

instance HBifunctor Day where
    hleft  = D.trans1
    hright = D.trans2
    hbimap f g (Day x y z) = Day (f x) (g y) z

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

instance HFunctor Step where
    hmap f (Step n x) = Step n (f x)

instance Interpret Step where
    type C Step = AccumNat
    inject = Step 0
    retract (Step n x)     = step n *> x
    interpret f (Step n x) = step n *> f x

instance HBifunctor (:+:) where
    hleft f = \case
      L1 x -> L1 (f x)
      R1 y -> R1 y

    hright g = \case
      L1 x -> L1 x
      R1 y -> R1 (g y)

    hbimap f g = \case
      L1 x -> L1 (f x)
      R1 y -> R1 (g y)

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
      More (R1 y) -> case fromF y of
        Step n z -> Step (n + 1) z
    toF (Step n x) = go n
      where
        go (flip minusNaturalMaybe 1 -> i) = case i of
          Nothing -> More (L1 x)
          Just j  -> More (R1 (go j))
    appendF = \case
      L1 x -> x
      R1 y -> y     -- hm, what is this?

    retractT = \case
      L1 x -> x
      R1 y -> y
    interpretT f g = \case
      L1 x -> f x
      R1 y -> g y
    toTM = \case
      L1 x -> Step 0 x
      R1 y -> Step 1 y

-- | Useful newtype to allow us to derive an 'HFunctor' instance from any
-- instance of 'HBifunctor', using -XDerivingVia.
--
-- For example, because we have @instance 'HBifunctor' 'Day'@, we can
-- write:
--
-- @
-- deriving via ('WrappedHBifunctor' 'Day' f) instance 'HFunctor' ('Day' f)
-- @
--
-- to give us an automatic 'HFunctor' instance and save us some work.
newtype WrappedHBifunctor t (f :: Type -> Type) (g :: Type -> Type) a
    = WrappedHBifunctor { unwrapHBifunctor :: t f g a }
  deriving Functor

instance HBifunctor t => HFunctor (WrappedHBifunctor t f) where
    hmap f = WrappedHBifunctor . hright f . unwrapHBifunctor

deriving via (WrappedHBifunctor Day f)    instance HFunctor (Day f)
deriving via (WrappedHBifunctor (:*:) f)  instance HFunctor ((:*:) f)
deriving via (WrappedHBifunctor (:+:) f)  instance HFunctor ((:+:) f)

instance HFunctor MC.F where
    hmap = MC.hoistF

instance HFunctor Free where
    hmap f x = Free $ \p b -> runFree x p $ \y z -> b (f y) z

instance Interpret Free where
    type C Free = Monad

    inject x = Free $ \p b -> b x p
    retract x = runFree x pure (>>=)
    interpret f x = runFree x pure ((>>=) . f)

