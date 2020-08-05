-- |
-- Module      : Data.Functor.Combinator
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- Functor combinators and tools (typeclasses and utiility functions) to
-- manipulate them.  This is the main "entrypoint" of the library.
--
-- Classes include:
--
-- *  'HFunctor' and 'HBifunctor', used to swap out the functors that the
--    combinators modify
-- *  'Interpret', 'Associative', 'Tensor', used to inject and interpret
-- functor values with respect to their combinators.
--
-- We have some helpful utility functions, as well, built on top of these
-- typeclasses.
--
-- The second half of this module exports the various useful functor
-- combinators that can modify functors to add extra functionality, or join
-- two functors together and mix them in different ways.  Use them to build
-- your final structure by combining simpler ones in composable ways!
--
-- See <https://blog.jle.im/entry/functor-combinatorpedia.html> and the
-- README for a tutorial and a rundown on each different functor
-- combinator.
module Data.Functor.Combinator (
  -- * Classes
  -- | A lot of type signatures are stated in terms of '~>'.  '~>'
  -- represents a "natural transformation" between two functors: a value of
  -- type @f '~>' g@ is a value of type 'f a -> g a@ that works for /any/
  -- @a@.
    type (~>)
  , type (<~>)
  -- ** Single Functors
  -- | Classes that deal with single-functor combinators, that enhance
  -- a single functor.
  , HFunctor(..)
  , Inject(..)
  , Interpret(..)
  , forI
  , getI
  , collectI
  -- ** Multi-Functors
  -- | Classes that deal with two-functor combinators, that "mix" two
  -- functors together in some way.
  , HBifunctor(..)
  -- *** Associative
  , Associative(..)
  , SemigroupIn(..)
  , biget, bicollect
  , (!*!)
  , (!+!)
  , (!$!)
  -- *** Tensor
  , Tensor(..)
  , MonoidIn(..)
  , nilLB, consLB
  , inL, inR
  , outL, outR
  -- * Combinators
  -- | Functor combinators
  -- ** Single
  , Coyoneda(..)
  , ListF(..)
  , NonEmptyF(..)
  , MaybeF(..)
  , MapF(..)
  , NEMapF(..)
  , Ap
  , Ap1(..)
  , Alt
  , Free
  , Free1
  , Lift
  , Step(..)
  , Steps(..)
  , ProxyF(..)
  , ConstF(..)
  , EnvT(..)
  , ReaderT(..)
  , Flagged(..)
  , IdentityT(..)
  , Void2
  , Final(..)
  , FreeOf(..)
  , ComposeT(..)
  -- ** Multi
  , Day(..)
  , (:*:)(..), prodOutL, prodOutR
  , (:+:)(..), V1
  , These1(..)
  , Comp(Comp, unComp)
  , LeftF(..)
  , RightF(..)
  -- ** Combinator Combinators
  , HLift(..)
  , HFree(..)
  -- * Util
  -- ** Natural Transformations
  , generalize
  , absorb
  -- ** Divisible
  , divideN
  , diviseN
  , concludeN
  , decideN
  , divideNRec
  , diviseNRec
  ) where

import           Control.Alternative.Free
import           Control.Applicative.Free
import           Control.Applicative.Lift
import           Control.Applicative.ListF
import           Control.Applicative.Step
import           Control.Comonad.Trans.Env
import           Control.Monad.Freer.Church
import           Control.Monad.Trans.Compose
import           Control.Monad.Trans.Identity
import           Control.Monad.Trans.Reader
import           Control.Natural
import           Control.Natural.IsoF
import           Data.Functor.Apply.Free
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Coyoneda
import           Data.Functor.Day
import           Data.Functor.These
import           Data.HBifunctor
import           Data.HBifunctor.Associative
import           Data.HBifunctor.Tensor
import           Data.HFunctor
import           Data.HFunctor.Final
import           Data.HFunctor.Internal
import           Data.HFunctor.Interpret
import           GHC.Generics

import qualified Data.SOP           as SOP
import qualified Data.Vinyl         as V
import qualified Data.Vinyl.Functor as V


-- | Convenient helper function to build up a 'Divisible' by providing
-- each component of it.  This makes it much easier to build up longer
-- chains as opposed to nested calls to 'divide' and manually peeling off
-- tuples one-by-one.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MT Int Bool String
-- @
--
-- and a contravariant consumer @Builder@ (representing, say, a way to
-- serialize an item, where @intBuilder :: Builder Int@ is a serializer of
-- 'Int's), then you could assemble a serializer a @MyType@ using:
--
-- @
-- contramap (\(MyType x y z) -> I x :* I y :* I z :* Nil) $
--   divideN $ intBuilderj
--          :* boolBuilder
--          :* stringBuilder
--          :* Nil
-- @
divideN
    :: Divisible f
    => SOP.NP f as
    -> f (SOP.NP SOP.I as)
divideN = \case
    SOP.Nil     -> conquer
    x SOP.:* xs -> divide
      (\case SOP.I y SOP.:* ys -> (y, ys))
      x
      (divideN xs)

-- | A version of 'divideN' defined to work with 'V.XRec', which can
-- syntactically cleaner because you don't have to manually wrap/unwrap
-- 'SOP.I's.
--
-- Using the example for 'divideN':
--
-- @
-- data MyType = MT Int Bool String
--
-- contramap (\(MyType x y z) -> x ::& y ::& z ::& Nil) $
--   divideNRec $ intBuilderj
--             :& boolBuilder
--             :& stringBuilder
--             :& RNil
-- @
divideNRec
    :: Divisible f
    => V.Rec f as
    -> f (V.XRec V.Identity as)
divideNRec = \case
    V.RNil    -> conquer
    x V.:& xs -> divide
      (\case z V.::& zs -> (z, zs))
      x
      (divideNRec xs)

-- | A version of 'divideNRec' that works for non-empty records, and so only
-- requires a 'Divise' constraint.
diviseNRec
    :: Divise f
    => V.Rec f (a ': as)
    -> f (V.XRec V.Identity (a ': as))
diviseNRec = \case
    x V.:& xs -> case xs of
      V.RNil   -> contramap (\case z V.::& _ -> z) x
      _ V.:& _ -> divise
        (\case z V.::& zs -> (z,zs))
        x
        (diviseNRec xs)

-- | A version of 'divideN' that works for non-empty 'SOP.NP', and so only
-- requires a 'Divise' constraint.
diviseN
    :: Divise f
    => SOP.NP f (a ': as)
    -> f (SOP.NP SOP.I (a ': as))
diviseN = \case
    x SOP.:* xs -> case xs of
      SOP.Nil    -> contramap (SOP.unI . SOP.hd) x
      _ SOP.:* _ -> divise
        (\case SOP.I z SOP.:* zs -> (z, zs))
        x
        (diviseN xs)

-- | Convenient helper function to build up a 'Conclude' by providing
-- each component of it.  This makes it much easier to build up longer
-- chains as opposed to nested calls to 'decide' and manually peeling off
-- eithers one-by-one.
--
-- For example, if you had a data type
--
-- @
-- data MyType = MTI Int | MTB Bool | MTS String
-- @
--
-- and a contravariant consumer @Builder@ (representing, say, a way to
-- serialize an item, where @intBuilder :: Builder Int@ is a serializer of
-- 'Int's), then you could assemble a serializer a @MyType@ using:
--
-- @
-- contramap (\case MTI x -> Z (I x); MTB y -> S (Z (I y)); MTS z -> S (S (Z (I z)))) $
--   concludeN $ intBuilder
--            :* boolBuilder
--            :* stringBuilder
--            :* Nil
-- @
concludeN
    :: Conclude f
    => SOP.NP f as
    -> f (SOP.NS SOP.I as)
concludeN = \case
    SOP.Nil     -> conclude (\case {})
    x SOP.:* xs -> decide
      (\case SOP.Z y  -> Left (SOP.unI y); SOP.S ys -> Right ys)
      x
      (concludeN xs)

-- | A version of 'concludeN' that works for non-empty 'SOP.NP'/'SOP.NS',
-- and so only requires a 'Decide' constraint.
decideN
    :: Decide f
    => SOP.NP f (a ': as)
    -> f (SOP.NS SOP.I (a ': as))
decideN = \case
    x SOP.:* xs -> case xs of
      SOP.Nil    -> contramap (SOP.unI . SOP.unZ) x
      _ SOP.:* _ -> decide
        (\case SOP.Z z -> Left (SOP.unI z); SOP.S zs -> Right zs)
        x
        (decideN xs)
