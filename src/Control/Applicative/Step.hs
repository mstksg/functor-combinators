{-# LANGUAGE AllowAmbiguousTypes        #-}
{-# LANGUAGE DeriveDataTypeable         #-}
{-# LANGUAGE DeriveFoldable             #-}
{-# LANGUAGE DeriveFunctor              #-}
{-# LANGUAGE DeriveGeneric              #-}
{-# LANGUAGE DeriveTraversable          #-}
{-# LANGUAGE EmptyCase                  #-}
{-# LANGUAGE EmptyDataDeriving          #-}
{-# LANGUAGE ExistentialQuantification  #-}
{-# LANGUAGE FlexibleInstances          #-}
{-# LANGUAGE GADTs                      #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE LambdaCase                 #-}
{-# LANGUAGE PolyKinds                  #-}
{-# LANGUAGE ScopedTypeVariables        #-}
{-# LANGUAGE TemplateHaskell            #-}
{-# LANGUAGE TypeApplications           #-}
{-# LANGUAGE TypeInType                 #-}
{-# LANGUAGE TypeOperators              #-}

-- |
-- Module      : Control.Applicative.Step
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module provides functor combinators that are the fixed points of
-- applications of ':+:' and 'Data.Functor.These.These1'.  They are useful
-- for their 'Data.HFunctor.Interpret.Interpret' instances, along with
-- their relationship to the 'Data.HBifunctor.Tensor.Monoidal' instances of
-- ':+:' and 'Data.Functor.These.These1'.
module Control.Applicative.Step (
  -- * Fixed Points
    Step(..)
  , Steps(..)
  , Flagged(..)
  -- ** Steppers
  , stepUp
  , stepDown
  , stepping
  , stepsUp
  , stepsDown
  , steppings
  , flaggedDown
  -- * Void
  , absurd1
  , Void2
  , absurd2
  , Void3
  , absurd3
  ) where

import           Control.Natural
import           Control.Natural.IsoF
import           Data.Bifunctor
import           Data.Data
import           Data.Deriving
import           Data.Functor.Alt
import           Data.Functor.Bind
import           Data.Functor.These
import           Data.Map.NonEmpty          (NEMap)
import           Data.Semigroup
import           Data.Semigroup.Foldable
import           Data.Semigroup.Traversable
import           Data.These
import           GHC.Generics
import           GHC.Natural
import qualified Data.Map.NonEmpty          as NEM

-- | An @f a@, along with a 'Natural' index.
--
-- @
-- 'Step' f a ~ ('Natural', f a)
-- Step f   ~ ((,) Natural) ':.:' f       -- functor composition
-- @
--
-- It is the fixed point of infinite applications of ':+:' (functor sums).
--
-- Intuitively, in an infinite @f :+: f :+: f :+: f ...@, you have
-- exactly one @f@ /somewhere/.  A @'Step' f a@ has that @f@, with
-- a 'Natural' giving you "where" the @f@ is in the long chain.
--
-- Can be useful for using with the 'Data.HBifunctor.Tensor.Monoidal'
-- instance of ':+:'.
--
-- 'Data.HFunctor.Interpret.interpret'ing it requires no constraint on the
-- target context.
--
-- Note that this type and its instances equivalent to
-- @'Control.Comonad.Trans.Env.EnvT' ('Data.Semigroup.Sum' 'Natural')@.
data Step f a = Step { stepPos :: Natural, stepVal :: f a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Step
deriveRead1 ''Step
deriveEq1 ''Step
deriveOrd1 ''Step

instance Applicative f => Applicative (Step f) where
    pure = Step 0 . pure
    Step n f <*> Step m x = Step (n + m) (f <*> x)

instance Foldable1 f => Foldable1 (Step f) where
    fold1      = fold1 . stepVal
    foldMap1 f = foldMap1 f . stepVal
    toNonEmpty = toNonEmpty . stepVal

instance Traversable1 f => Traversable1 (Step f) where
    traverse1 f (Step n x) = Step n <$> traverse1 f x
    sequence1 (Step n x) = Step n <$> sequence1 x

-- | "Uncons and cons" an @f@ branch before a 'Step'.  This is basically
-- a witness that 'stepDown' and 'stepUp' form an isomorphism.
stepping :: Step f <~> f :+: Step f
stepping = isoF stepDown stepUp

-- | Pop off the first item in a 'Step'.  Because a @'Step' f@ is @f :+:
-- f :+: f :+: ...@ forever, this matches on the first branch.
--
-- You can think of it as reassociating
--
-- @
-- f :+: f :+: f :+: f :+: ...
-- @
--
-- into
--
-- @
-- f :+: ( f :+: f :+: f :+: ...)
-- @
--
-- @
-- 'stepDown' ('Step' 2 "hello")
-- -- 'R1' (Step 1 "hello")
-- stepDown (Step 0 "hello")
-- -- 'L1' "hello"
-- @
--
-- Forms an isomorphism with 'stepUp' (see 'stepping').
stepDown :: Step f ~> f :+: Step f
stepDown (Step n x) = case minusNaturalMaybe n 1 of
    Nothing -> L1 x
    Just m  -> R1 (Step m x)

-- | Unshift an item into a 'Step'.  Because a @'Step' f@ is @f :+: f :+:
-- f :+: f :+: ...@ forever, this basically conses an additional
-- possibility of @f@ to the beginning of it all.
--
-- You can think of it as reassociating
--
-- @
-- f :+: ( f :+: f :+: f :+: ...)
-- @
--
-- into
--
-- @
-- f :+: f :+: f :+: f :+: ...
-- @
--
-- @
-- 'stepUp' ('L1' "hello")
-- -- 'Step' 0 "hello"
-- stepUp ('R1' (Step 1 "hello"))
-- -- Step 2 "hello"
-- @
--
-- Forms an isomorphism with 'stepDown' (see 'stepping').
stepUp :: f :+: Step f ~> Step f
stepUp = \case
    L1 x          -> Step 0       x
    R1 (Step n y) -> Step (n + 1) y

-- | We have a natural transformation between 'V1' and any other
-- functor @f@ with no constraints.
absurd1 :: V1 a -> f a
absurd1 = \case {}

-- | A non-empty map of 'Natural' to @f a@.  Basically, contains multiple
-- @f a@s, each at a given 'Natural' index.
--
-- @
-- Steps f a ~ 'M.Map' 'Natural' (f a)
-- Steps f   ~ 'M.Map' 'Natural' ':.:' f       -- functor composition
-- @
--
-- It is the fixed point of applications of 'Data.Functor.These.TheseT'.
--
-- You can think of this as an infinite sparse array of @f a@s.
--
-- Intuitively, in an infinite @f \`TheseT\` f \`TheseT\` f \`TheseT\` f ...@,
-- each of those infinite positions may have an @f@ in them.  However,
-- because of the at-least-one nature of 'Data.Functor.These.TheseT', we know we have at least
-- one f at one position /somewhere/.
--
-- A @'Steps' f a@ has potentially many @f@s, each stored at a different
-- 'Natural' position, with the guaruntee that at least one @f@ exists.
--
-- Can be useful for using with the 'Data.HBifunctor.Tensor.Monoidal' instance
-- of 'Data.Functor.These.TheseT'.
--
-- 'Data.HFunctor.interpret'ing it requires at least an 'Alt'
-- instance in the target context, since we have to handle potentially more
-- than one @f@.
newtype Steps f a = Steps { getSteps :: NEMap Natural (f a) }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Steps
deriveRead1 ''Steps
deriveEq1 ''Steps
deriveOrd1 ''Steps

instance Foldable1 f => Foldable1 (Steps f) where
    fold1      = foldMap1 fold1 . getSteps
    foldMap1 f = (foldMap1 . foldMap1) f . getSteps
    toNonEmpty = foldMap1 toNonEmpty . getSteps

instance Traversable1 f => Traversable1 (Steps f) where
    traverse1 f = fmap Steps . (traverse1 . traverse1) f . getSteps
    sequence1   = fmap Steps . traverse1 sequence1 . getSteps

instance Semigroup (Steps f a) where
    Steps xs <> Steps ys = Steps $
      let (k, _) = NEM.findMax xs
      in  xs <> NEM.mapKeysMonotonic (+ (k + 1)) ys

instance Functor f => Alt (Steps f) where
    (<!>) = (<>)

-- | "Uncons and cons" an @f@ branch before a 'Steps'.  This is basically
-- a witness that 'stepsDown' and 'stepsUp' form an isomorphism.
steppings :: Steps f <~> These1 f (Steps f)
steppings = isoF stepsDown stepsUp

-- | Pop off the first item in a 'Steps'.  Because a @'Steps' f@ is @f
-- `These1` f `These1` f `These1` ...@ forever, this matches on the first branch.
--
-- You can think of it as reassociating
--
-- @
-- f `These1` f `These1` f `These1` f `These1` ...
-- @
--
-- into
--
-- @
-- f `These1` ( f `These1` f `These1` f `These1` ...)
-- @
--
-- It returns:
--
-- *  'This1' if the first item is the /only/ item in the 'Steps'
-- *  'That1' if the first item in the 'Steps' is empty, but there are more
--    items left.  The extra items are all shfited down.
-- *  'These1' if the first item in the 'Steps' exists, and there are also
--    more items left.  The extra items are all shifted down.
--
-- Forms an isomorphism with 'stepsUp' (see 'steppings').
stepsDown :: Steps f ~> These1 f (Steps f)
stepsDown = these This1 That1 These1
          . bimap getFirst Steps
          . NEM.foldMapWithKey decr
          . getSteps

decr :: Natural -> f a -> These (First (f a)) (NEMap Natural (f a))
decr i x = case minusNaturalMaybe i 1 of
      Nothing -> This $ First x
      Just i' -> That $ NEM.singleton i' x

-- | Unshift an item into a 'Steps'.  Because a @'Steps' f@ is @f `These1`
-- f `These1` f `These1` f `These1` ...@ forever, this basically conses an
-- additional possibility of @f@ to the beginning of it all.
--
-- You can think of it as reassociating
--
-- @
-- f `These1` ( f `These1` f `These1` f `These1` ...)
-- @
--
-- into
--
-- @
-- f `These1` f `These1` f `These1` f `These1` ...
-- @
--
-- If you give:
--
-- *  'This1', then it returns a singleton 'Steps' with one item at
--    index 0
-- *  'That1', then it shifts every item in the given 'Steps' up one
--    index.
-- *  'These1', then it shifts every item in the given 'Steps' up one
--    index, and adds the given item (the @f@) at index zero.
--
-- Forms an isomorphism with 'stepDown' (see 'stepping').
stepsUp :: These1 f (Steps f) ~> Steps f
stepsUp = \case
    This1  x    -> Steps $ NEM.singleton 0 x
    That1    xs -> Steps . NEM.mapKeysMonotonic (+ 1)
                         . getSteps
                         $ xs
    These1 x xs -> Steps . NEM.insertMapMin 0 x
                         . NEM.toMap
                         . NEM.mapKeysMonotonic (+ 1)
                         . getSteps
                         $ xs


-- | An @f a@, along with a 'Bool' flag
--
-- @
-- Step f a ~ ('Bool', f a)
-- Step f   ~ ((,) Bool) ':.:' f       -- functor composition
-- @
--
-- You can think of it as an @f a@ that is "flagged" with a boolean value,
-- and that value can indicuate whether or not it is "pure" (made with
-- 'Data.HFunctor.inject' or 'pure') as 'False', or "inpure" (made from some other
-- source) as 'True'.
--
-- You can think of it like a 'Step' that is either 0 or 1, as well.
--
-- 'Data.HFunctor.Interpret.interpret'ing it requires no constraint on the
-- target context.
--
-- This type is equivalent (along with its instances) to:
--
-- *   @'Data.HFunctor.HLift' 'Control.Monad.Trans.Identity.IdentityT'@
-- *   @'Control.COmonad.Trans.Env.EnvT' 'Data.Semigroup.Any'@
data Flagged f a = Flagged { flaggedFlag :: Bool, flaggedVal :: f a }
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Flagged
deriveRead1 ''Flagged
deriveEq1 ''Flagged
deriveOrd1 ''Flagged

instance Applicative f => Applicative (Flagged f) where
    pure = Flagged False . pure
    Flagged n f <*> Flagged m x = Flagged (n || m) (f <*> x)

instance Foldable1 f => Foldable1 (Flagged f) where
    fold1      = fold1 . flaggedVal
    foldMap1 f = foldMap1 f . flaggedVal
    toNonEmpty = toNonEmpty . flaggedVal

instance Traversable1 f => Traversable1 (Flagged f) where
    traverse1 f (Flagged n x) = Flagged n <$> traverse1 f x
    sequence1 (Flagged n x) = Flagged n <$> sequence1 x


flaggedDown :: Flagged f ~> f :+: Flagged f
flaggedDown (Flagged False x) = L1 x
flaggedDown (Flagged True  x) = R1 (Flagged False x)




-- | @'Void2' a b@ is uninhabited for all @a@ and @b@.
data Void2 a b
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Void2
deriveRead1 ''Void2
deriveEq1 ''Void2
deriveOrd1 ''Void2

instance Semigroup (Void2 a b) where
    x <> _ = case x of {}

instance Alt (Void2 a) where
    x <!> _ = absurd2 x

instance Bind (Void2 a) where
    x >>- _ = case x of {}

instance Apply (Void2 a) where
    x <.> _ = case x of {}

-- | If you treat a @'Void2' f a@ as a functor combinator, then 'absurd2'
-- lets you convert from a @'Void2' f a@ into a @t f a@ for any functor
-- combinator @t@.
absurd2 :: Void2 f a -> t f a
absurd2 = \case {}

-- | @'Void3' a b@ is uninhabited for all @a@ and @b@.
data Void3 a b c
  deriving (Show, Read, Eq, Ord, Functor, Foldable, Traversable, Typeable, Generic, Data)

deriveShow1 ''Void3
deriveRead1 ''Void3
deriveEq1 ''Void3
deriveOrd1 ''Void3

instance Semigroup (Void3 a b c) where
    x <> _ = case x of {}

instance Alt (Void3 a b) where
    x <!> _ = absurd3 x

instance Bind (Void3 a b) where
    x >>- _ = case x of {}

instance Apply (Void3 a b) where
    x <.> _ = case x of {}

-- | If you treat a @'Void3' f a@ as a binary functor combinator, then
-- 'absurd3' lets you convert from a @'Void3' f a@ into a @t f a@ for any
-- functor combinator @t@.
absurd3 :: Void3 f g a -> t f g a
absurd3 = \case {}
