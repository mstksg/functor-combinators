-- |
-- Module      : Control.Monad.Freer.Church
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- The church-encoded "Freer" Monad.  Basically provides the free monad in
-- a way that is compatible with 'Data.Functor.HFunctor.HFunctor' and
-- 'Data.Functor.HFunctor.Interpret'.  We also have the "semigroup" version
-- 'Free1', which is the free  'Bind'.
--
-- The module also provides a version of 'GHC.Generics.:.:' (or
-- 'Data.Functor.Compose'), 'Comp', in a way that is compatible with
-- 'Data.Functor.Tensor.HBifunctor' and the related typeclasses.
module Control.Monad.Freer.Church (
  -- * 'Free'
    Free(..), reFree
  -- ** Interpretation
  , liftFree, interpretFree, retractFree, hoistFree
  -- ** Folding
  , foldFree, foldFree', foldFreeC
  -- * 'Free1'
  , Free1(.., DoneF1, MoreF1)
  , reFree1, toFree
  -- ** Interpretation
  , liftFree1, interpretFree1, retractFree1, hoistFree1
  -- ** Conversion
  , free1Comp, matchFree1
  -- ** Folding
  , foldFree1, foldFree1', foldFree1C
  -- * 'Comp'
  , Comp(.., Comp, unComp), comp
  ) where

import           Control.Applicative
import           Data.Functor.Plus
import           Control.Monad
import           Control.Natural
import           Data.Foldable
import           Data.Functor
import           Data.Functor.Bind
import           Data.Functor.Classes
import           Data.Functor.Coyoneda
import           Data.Pointed
import           Data.Semigroup.Foldable
import           Data.Semigroup.Traversable
import           GHC.Generics
import           Text.Read
import qualified Control.Monad.Free         as M

-- | A @'Free' f@ is @f@ enhanced with "sequential binding" capabilities.
-- It allows you to sequence multiple @f@s one after the other, and also to
-- determine "what @f@ to sequence" based on the result of the computation
-- so far.
--
-- Essentially, you can think of this as "giving @f@ a 'Monad' instance",
-- with all that that entails ('return', '>>=', etc.).
--
-- Lift @f@ into it with @'Data.Functor.HFunctor.inject' :: f a -> Free
-- f a@.  When you finally want to "use" it, you can interpret it into any
-- monadic context:
--
-- @
-- 'Data.Functor.HFunctor.interpret'
--     :: 'Monad' g
--     => (forall x. f x -> g x)
--     -> 'Free' f a
--     -> g a
-- @
--
-- Structurally, this is equivalent to many "nested" f's.  A value of type
-- @'Free' f a@ is either:
--
-- *   @a@
-- *   @f a@
-- *   @f (f a)@
-- *   @f (f (f a))@
-- *   .. etc.
--
-- Under the hood, this is the Church-encoded Freer monad.  It's
-- 'Control.Monad.Free.Free', or 'Control.Monad.Free.Church.F', but in
-- a way that is compatible with 'Data.Functor.HFunctor.HFunctor' and
-- 'Data.Functor.HFunctor.Interpret'.
newtype Free f a = Free
    { runFree :: forall r. (a -> r) -> (forall s. f s -> (s -> r) -> r) -> r
    }

instance Functor (Free f) where
    fmap f x = Free $ \p b -> runFree x (p . f) b

instance Apply (Free f) where
    (<.>) = ap

instance Applicative (Free f) where
    pure  = return
    (<*>) = (<.>)

instance Pointed (Free f) where
    point = pure

instance Bind (Free f) where
    x >>- f  = Free $ \p b -> runFree x (\y -> runFree (f y) p b) b

instance Monad (Free f) where
    return x = Free $ \p _ -> p x
    (>>=)    = (>>-)

instance M.MonadFree f (Free f) where
    wrap x = Free $ \p b -> b x $ \y -> runFree y p b

instance Foldable f => Foldable (Free f) where
    foldMap f = foldFreeC f fold

instance Traversable f => Traversable (Free f) where
    traverse f = foldFree (fmap pure   . f        )
                          (fmap M.wrap . sequenceA)

instance (Functor f, Eq1 f) => Eq1 (Free f) where
    liftEq eq x y = liftEq @(M.Free f) eq (reFree x) (reFree y)

instance (Functor f, Ord1 f) => Ord1 (Free f) where
    liftCompare c x y = liftCompare @(M.Free f) c (reFree x) (reFree y)

instance (Functor f, Eq1 f, Eq a) => Eq (Free f a) where
    (==) = eq1

instance (Functor f, Ord1 f, Ord a) => Ord (Free f a) where
    compare = compare1

instance (Functor f, Show1 f) => Show1 (Free f) where
    liftShowsPrec sp sl d x = case reFree x of
        M.Pure y  -> showsUnaryWith sp "pure" d y
        M.Free ys -> showsUnaryWith (liftShowsPrec sp' sl') "wrap" d ys
      where
        sp' = liftShowsPrec sp sl
        sl' = liftShowList sp sl

-- | Show in terms of 'pure' and 'M.wrap'.
instance (Functor f, Show1 f, Show a) => Show (Free f a) where
    showsPrec = liftShowsPrec showsPrec showList

instance (Functor f, Read1 f) => Read1 (Free f) where
    liftReadsPrec rp rl = go
      where
        go = readsData $
            readsUnaryWith rp "pure" pure
         <> readsUnaryWith (liftReadsPrec go (liftReadList rp rl)) "wrap" M.wrap

-- | Read in terms of 'pure' and 'M.wrap'.
instance (Functor f, Read1 f, Read a) => Read (Free f a) where
    readPrec = readPrec1
    readListPrec = readListPrecDefault
    readList = readListDefault

-- | Convert a @'Free' f@ into any instance of @'M.MonadFree' f@.
reFree
    :: (M.MonadFree f m, Functor f)
    => Free f a
    -> m a
reFree = foldFree pure M.wrap

-- | Lift an @f@ into @'Free' f@, so you can use it as a 'Monad'.
--
-- This is 'Data.HFunctor.inject'.
liftFree :: f ~> Free f
liftFree x = Free $ \p b -> b x p

-- | Interpret a @'Free' f@ into a context @g@, provided that @g@ has
-- a 'Monad' instance.
--
-- This is 'Data.HFunctor.Interpret.interpret'.
interpretFree :: Monad g => (f ~> g) -> Free f ~> g
interpretFree f = foldFree' pure ((>>=) . f)

-- | Extract the @f@s back "out" of a @'Free' f@, utilizing its 'Monad'
-- instance.
--
-- This is 'Data.HFunctor.Interpret.retract'.
retractFree :: Monad f => Free f ~> f
retractFree = foldFree' pure (>>=)

-- | Swap out the underlying functor over a 'Free'.  This preserves all of
-- the structure of the 'Free'.
hoistFree :: (f ~> g) -> Free f ~> Free g
hoistFree f x = Free $ \p b -> runFree x p (b . f)

-- | A version of 'foldFree' that doesn't require @'Functor' f@, by taking
-- a RankN folding function.  This is essentially a flipped 'runFree'.
foldFree'
    :: (a -> r)
    -> (forall s. f s -> (s -> r) -> r)
    -> Free f a
    -> r
foldFree' f g x = runFree x f g

-- | A version of 'foldFree' that doesn't require @'Functor' f@, by folding
-- over a 'Coyoneda' instead.
foldFreeC
    :: (a -> r)                 -- ^ handle 'pure'
    -> (Coyoneda f r -> r)      -- ^ handle 'M.wrap'
    -> Free f a
    -> r
foldFreeC f g = foldFree' f (\y n -> g (Coyoneda n y))

-- | Recursively fold down a 'Free' by handling the 'pure' case and the
-- nested/wrapped case.
--
-- This is a catamorphism.
--
-- This requires @'Functor' f@; see 'foldFree'' and 'foldFreeC' for
-- a version that doesn't require @'Functor' f@.
foldFree
    :: Functor f
    => (a -> r)                 -- ^ handle 'pure'
    -> (f r -> r)               -- ^ handle 'M.wrap'
    -> Free f a
    -> r
foldFree f g = foldFreeC f (g . lowerCoyoneda)

-- | The Free 'Bind'.  Imbues any functor @f@ with a 'Bind' instance.
--
-- Conceptually, this is "'Free' without pure".  That is, while normally
-- @'Free' f a@ is an @a@, a @f a@, a @f (f a)@, etc., a @'Free1' f a@ is
-- an @f a@, @f (f a)@, @f (f (f a))@, etc.  It's a 'Free' with "at least
-- one layer of @f@", excluding the @a@ case.
--
-- It can be useful as the semigroup formed by ':.:' (functor composition):
-- Sometimes we want an @f :.: f@, or an @f :.: f :.: f@, or an @f :.:
-- f :.: f :.: f@...just as long as we have at least one @f@.
newtype Free1 f a = Free1
    { runFree1 :: forall r. (forall s. f s -> (s -> a) -> r)
                         -> (forall s. f s -> (s -> r) -> r)
                         -> r
    }

instance Functor (Free1 f) where
    fmap f x = Free1 $ \p b -> runFree1 x (\y c -> p y (f . c)) b

instance Apply (Free1 f) where
    (<.>) = apDefault

instance Bind (Free1 f) where
    x >>- f = Free1 $ \p b ->
        runFree1 x (\y c -> b y ((\q -> runFree1 q p b) . f . c)) b

instance Foldable f => Foldable (Free1 f) where
    foldMap f = foldFree1C (foldMap f) fold

instance Traversable f => Traversable (Free1 f) where
    traverse f = foldFree1 (fmap DoneF1 . traverse f)
                           (fmap MoreF1 . sequenceA )

instance Foldable1 f => Foldable1 (Free1 f) where
    foldMap1 f = foldFree1C (foldMap1 f) fold1

instance Traversable1 f => Traversable1 (Free1 f) where
    traverse1 f = foldFree1 (fmap DoneF1 . traverse1 f)
                            (fmap MoreF1 . sequence1  )

instance (Functor f, Eq1 f) => Eq1 (Free1 f) where
    liftEq eq x y = liftEq @(Free f) eq (toFree x) (toFree y)

instance (Functor f, Ord1 f) => Ord1 (Free1 f) where
    liftCompare c x y = liftCompare @(Free f) c (toFree x) (toFree y)

instance (Functor f, Eq1 f, Eq a) => Eq (Free1 f a) where
    (==) = eq1

instance (Functor f, Ord1 f, Ord a) => Ord (Free1 f a) where
    compare = compare1

instance (Functor f, Show1 f) => Show1 (Free1 f) where
    liftShowsPrec sp sl d = \case
        DoneF1 x -> showsUnaryWith (liftShowsPrec sp  sl ) "DoneF1" d x
        MoreF1 x -> showsUnaryWith (liftShowsPrec sp' sl') "MoreF1" d x
      where
        sp' = liftShowsPrec sp sl
        sl' = liftShowList sp sl

-- | Show in terms of 'DoneF1' and 'MoreF1'.
instance (Functor f, Show1 f, Show a) => Show (Free1 f a) where
    showsPrec = liftShowsPrec showsPrec showList

instance (Functor f, Read1 f) => Read1 (Free1 f) where
    liftReadsPrec rp rl = go
      where
        go = readsData $
            readsUnaryWith (liftReadsPrec rp rl) "DoneF1" DoneF1
         <> readsUnaryWith (liftReadsPrec go (liftReadList rp rl)) "MoreF1" MoreF1

-- | Read in terms of 'DoneF1' and 'MoreF1'.
instance (Functor f, Read1 f, Read a) => Read (Free1 f a) where
    readPrec = readPrec1
    readListPrec = readListPrecDefault
    readList = readListDefault

-- | Constructor matching on the case that a @'Free1' f@ consists of just
-- a single un-nested @f@.  Used as a part of the 'Show' and 'Read'
-- instances.
pattern DoneF1 :: Functor f => f a -> Free1 f a
pattern DoneF1 x <- (matchFree1 -> L1 x)
  where
    DoneF1 x = liftFree1 x

-- | Constructor matching on the case that a @'Free1' f@ is a nested @f
-- ('Free1' f a)@.  Used as a part of the 'Show' and 'Read' instances.
--
-- As a constructor, this is equivalent to 'M.wrap'.
pattern MoreF1 :: Functor f => f (Free1 f a) -> Free1 f a
pattern MoreF1 x <- (matchFree1 -> R1 (Comp x))
  where
    MoreF1 x = liftFree1 x >>- id
{-# COMPLETE DoneF1, MoreF1 #-}

-- | Convert a @'Free1' f@ into any instance of @'M.MonadFree' f@.
reFree1
    :: (M.MonadFree f m, Functor f)
    => Free1 f a
    -> m a
reFree1 = foldFree1 (M.wrap . fmap pure) M.wrap

-- | @'Free1' f@ is a special subset of @'Free' f@ that consists of at least one
-- nested @f@.  This converts it back into the "bigger" type.
--
-- See 'free1Comp' for a version that preserves the "one nested layer"
-- property.
toFree :: Free1 f ~> Free f
toFree x = Free $ \p b -> runFree1 x (\y c -> b y (p . c)) b

-- | Map the underlying functor under a 'Free1'.
hoistFree1 :: (f ~> g) -> Free1 f ~> Free1 g
hoistFree1 f x = Free1 $ \p b -> runFree1 x (p . f) (b . f)

-- | Because a @'Free1' f@ is just a @'Free' f@ with at least one nested
-- layer of @f@, this function converts it back into the one-nested-@f@
-- format.
free1Comp :: Free1 f ~> Comp f (Free f)
free1Comp = foldFree1' (\y c -> y :>>= (pure . c)) $ \y n ->
    y :>>= \z -> case n z of
      q :>>= m -> liftFree q >>= m

-- | Inject an @f@ into a @'Free1' f@
liftFree1 :: f ~> Free1 f
liftFree1 x = Free1 $ \p _ -> p x id

-- | Retract the @f@ out of a @'Free1' f@, as long as the @f@ implements
-- 'Bind'.  Since we always have at least one @f@, we do not need a full
-- 'Monad' constraint.
retractFree1 :: Bind f => Free1 f ~> f
retractFree1 = foldFree1' (<&>) (>>-)

-- | Interpret the @'Free1' f@ in some context @g@, provided that @g@ has
-- a 'Bind' instance.  Since we always have at least one @f@, we will
-- always have at least one @g@, so we do not need a full 'Monad'
-- constraint.
interpretFree1 :: Bind g => (f ~> g) -> Free1 f ~> g
interpretFree1 f = foldFree1' (\y c -> c <$> f y)
                              (\y n -> f y >>- n)

-- | A @'Free1' f@ is either a single un-nested @f@, or a @f@ nested with
-- another @'Free1' f@.  This decides which is the case.
matchFree1 :: forall f. Functor f => Free1 f ~> f :+: Comp f (Free1 f)
matchFree1 = foldFree1 L1 (R1 . Comp . fmap shuffle)
  where
    shuffle :: f :+: Comp f (Free1 f) ~> Free1 f
    shuffle (L1 y         ) = liftFree1 y
    shuffle (R1 (y :>>= n)) = liftFree1 y >>- n

-- | A version of 'foldFree1' that doesn't require @'Functor' f@, by taking
-- a RankN folding function.  This is essentially a flipped 'runFree'.
foldFree1'
    :: (forall s. f s -> (s -> a) -> r)
    -> (forall s. f s -> (s -> r) -> r)
    -> Free1 f a
    -> r
foldFree1' f g x = runFree1 x f g

-- | A version of 'foldFree1' that doesn't require @'Functor' f@, by
-- folding over a 'Coyoneda' instead.
foldFree1C
    :: (Coyoneda f a -> r)
    -> (Coyoneda f r -> r)
    -> Free1 f a
    -> r
foldFree1C f g = foldFree1' (\y c -> f (Coyoneda c y))
                            (\y n -> g (Coyoneda n y))

-- | Recursively fold down a 'Free1' by handling the single @f@ case and
-- the nested/wrapped case.
--
-- This is a catamorphism.
--
-- This requires @'Functor' f@; see 'foldFree'' and 'foldFreeC' for
-- a version that doesn't require @'Functor' f@.
foldFree1
    :: Functor f
    => (f a -> r)       -- ^ handle @'DoneF1'@.
    -> (f r -> r)       -- ^ handle @'MoreF1'@.
    -> Free1 f a
    -> r
foldFree1 f g = foldFree1C (f . lowerCoyoneda)
                           (g . lowerCoyoneda)

-- | Functor composition.  @'Comp' f g a@ is equivalent to @f (g a)@, and
-- the 'Comp' pattern synonym is a way of getting the @f (g a)@ in
-- a @'Comp' f g a@.
--
-- For example, @'Maybe' ('IO' 'Bool')@ is @'Comp' 'Maybe' 'IO' 'Bool'@.
--
-- This is mostly useful for its typeclass instances: in particular,
-- 'Functor', 'Applicative', 'Data.Functor.Tensor.HBifunctor', and
-- 'Data.Functor.Tensor.Monoidal'.
--
-- This is essentially a version of 'GHC.Generics.:.:' and
-- 'Data.Functor.Compose.Compose' that allows for an
-- 'Data.Functor.Tensor.HBifunctor' instance.
--
-- It is slightly less performant.  Using @'comp' . 'unComp'@ every once in
-- a while will concretize a 'Comp' value (if you have @'Functor' f@)
-- and remove some indirection if you have a lot of chained operations.
--
-- The "free monoid" over 'Comp' is 'Free', and the "free semigroup" over
-- 'Comp' is 'Free1'.
data Comp f g a =
    forall x. f x :>>= (x -> g a)

instance Functor g => Functor (Comp f g) where
    fmap f (x :>>= h) = x :>>= (fmap f . h)

-- | @since 0.3.6.0
instance (Apply f, Apply g) => Apply (Comp f g) where
    (x :>>= f) <.> (y :>>= g) = ((,) <$> x <.> y)
                           :>>= (\(x', y') -> f x' <.> g y')
    liftF2 h (x :>>= f) (y :>>= g)
            = ((,) <$> x <.> y)
         :>>= (\(x', y') -> liftF2 h (f x') (g y'))

instance (Applicative f, Applicative g) => Applicative (Comp f g) where
    pure x = pure () :>>= (pure . const x)
    (x :>>= f) <*> (y :>>= g) = ((,) <$> x <*> y)
                           :>>= (\(x', y') -> f x' <*> g y')
    liftA2 h (x :>>= f) (y :>>= g)
            = ((,) <$> x <*> y)
         :>>= (\(x', y') -> liftA2 h (f x') (g y'))

instance (Foldable f, Foldable g) => Foldable (Comp f g) where
    foldMap f (x :>>= h) = foldMap (foldMap f . h) x

instance (Traversable f, Traversable g) => Traversable (Comp f g) where
    traverse f (x :>>= h) = (:>>= id)
                        <$> traverse (traverse f . h) x

instance (Alternative f, Alternative g) => Alternative (Comp f g) where
    empty = empty :>>= id
    (x :>>= f) <|> (y :>>= g) = ((f <$> x) <|> (g <$> y)) :>>= id

-- | @since 0.3.6.0
instance (Alt f, Alt g) => Alt (Comp f g) where
    (x :>>= f) <!> (y :>>= g) = ((f <$> x) <!> (g <$> y)) :>>= id

-- | @since 0.3.6.0
instance (Plus f, Plus g) => Plus (Comp f g) where
    zero = zero :>>= id

instance (Functor f, Show1 f, Show1 g) => Show1 (Comp f g) where
    liftShowsPrec sp sl d (Comp x) =
        showsUnaryWith (liftShowsPrec sp' sl') "Comp" d x
      where
        sp' = liftShowsPrec sp sl
        sl' = liftShowList sp sl

instance (Functor f, Show1 f, Show1 g, Show a) => Show (Comp f g a) where
    showsPrec = liftShowsPrec showsPrec showList

instance (Functor f, Read1 f, Read1 g) => Read1 (Comp f g) where
    liftReadPrec rp rl = readData $
        readUnaryWith (liftReadPrec rp' rl') "Comp" Comp
      where
        rp' = liftReadPrec rp rl
        rl' = liftReadListPrec rp rl

instance (Functor f, Read1 f, Read1 g, Read a) => Read (Comp f g a) where
    readPrec = readPrec1
    readListPrec = readListPrecDefault
    readList = readListDefault

instance (Functor f, Eq1 f, Eq1 g) => Eq1 (Comp f g) where
    liftEq eq (Comp x) (Comp y) = liftEq (liftEq eq) x y

instance (Functor f, Ord1 f, Ord1 g) => Ord1 (Comp f g) where
    liftCompare c (Comp x) (Comp y) = liftCompare (liftCompare c) x y

instance (Functor f, Eq1 f, Eq1 g, Eq a) => Eq (Comp f g a) where
    (==) = eq1

instance (Functor f, Ord1 f, Ord1 g, Ord a) => Ord (Comp f g a) where
    compare = compare1

-- | "Smart constructor" for 'Comp' that doesn't require @'Functor' f@.
comp :: f (g a) -> Comp f g a
comp = (:>>= id)

-- | Pattern match on and construct a @'Comp' f g a@ as if it were @f
-- (g a)@.
pattern Comp :: Functor f => f (g a) -> Comp f g a
pattern Comp { unComp } <- ((\case x :>>= f -> f <$> x)->unComp)
  where
    Comp x = comp x
{-# COMPLETE Comp #-}

