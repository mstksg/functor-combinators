-- |
-- Module      : Data.HFunctor.Route
-- Copyright   : (c) Justin Le 2019
-- License     : BSD3
--
-- Maintainer  : justin@jle.im
-- Stability   : experimental
-- Portability : non-portable
--
-- This module contains the useful combinators 'Pre' and 'Post', which
-- enhances a functor with a "route" to and from the outside world; even if
-- the functor itself is existentially closed in a functor combinator, the
-- route will provide line to the outside world for extraction or
-- injection.
--
-- See 'Pre' and 'Post' for more information.
--
-- @since 0.3.4.0
module Data.HFunctor.Route (
  -- * Routing Combinators
  -- ** Contravariant
    Pre(..)
  , interpretPre, getPre, retractPre
  , injectPre, mapPre
  , preDivisible, preDivise, preContravariant
  -- ** Covariant
  , Post(..)
  , interpretPost, getPost, retractPost
  , injectPost, mapPost
  , postPlus, postAlt, postFunctor
  -- * Wrapped Invariant
  -- ** Contravariant
  , PreT(..)
  , preDivisibleT, preDiviseT, preContravariantT
  -- ** Covariant
  , PostT(..)
  , postPlusT, postAltT, postFunctorT
  ) where

import           Control.Natural
import           Data.Functor.Bind
import           Data.Functor.Contravariant
import           Data.Functor.Contravariant.Conclude
import           Data.Functor.Contravariant.Decide
import           Data.Functor.Contravariant.Divise
import           Data.Functor.Contravariant.Divisible
import           Data.Functor.Invariant
import           Data.Functor.Plus
import           Data.HFunctor
import           Data.HFunctor.HTraversable
import           Data.HFunctor.Interpret
import           Data.Profunctor
import           Data.Void

-- | A useful helper type to use with a covariant functor combinator that
-- allows you to tag along contravariant access to all @f@s inside the
-- combinator.
--
-- Maybe most usefully, it can be used with 'Ap'.  Remember that @'Ap' f a@
-- is a collection of @f x@s, with each x existentially wrapped.  Now, for
-- a @'Ap' (Pre a f) a@, it will be a collection of @f x@ and @a -> x@s:
-- not only each individual part, but a way to "select" that individual
-- part from the overal @a@.
--
-- So, you can imagine @'Ap' ('Pre' a f) b@ as a collection of @f x@ that
-- consumes @a@ and produces @b@.
--
-- When @a@ and @b@ are the same, @'Ap' ('Pre' a f) a@ is like the free
-- invariant sequencer.  That is, in a sense, @'Ap' ('Pre' a f) a@ contains
-- both contravariant and covariant sequences side-by-side, /consuming/
-- @a@s and also /producing/ @a@s.
--
-- You can build up these values with 'injectPre', and then use whatever
-- typeclasses your @t@ normally supports to build it up, like
-- 'Applicative' (for 'Ap').  You can then interpret it into both its
-- contravariant and covariant contexts:
--
-- @
-- -- interpret the covariant part
-- runCovariant :: 'Applicative' g => (f ~> g) -> Ap (Pre a f) a -> g a
-- runCovariant f = interpret (f . getPre)
--
-- -- interpret the contravariant part
-- runContravariant :: 'Divisible' g => (f ~> g) -> Ap (Pre a f) a -> g a
-- runContravariant = preDivisible
-- @
--
-- The 'PreT' type wraps up @'Ap' ('Pre' a f) a@ into a type @'PreT' 'Ap'
-- f a@, with nice instances/helpers.
--
-- An example of a usage of this in the real world is the /unjson/
-- library's record type constructor, to implement bidrectional
-- serializers for product types.
data Pre  a f b = (a -> b) :>$<: f b
  deriving Functor


-- | A useful helper type to use with a contravariant functor combinator that
-- allows you to tag along covariant access to all @f@s inside the
-- combinator.
--
-- Maybe most usefully, it can be used with 'Dec'.  Remember that @'Dec' f a@
-- is a collection of @f x@s, with each x existentially wrapped.  Now, for
-- a @'Dec' (Post a f) a@, it will be a collection of @f x@ and @x -> a@s:
-- not only each individual part, but a way to "re-embed" that individual
-- part into overal @a@.
--
-- So, you can imagine @'Dec' ('Post' a f) b@ as a collection of @f x@ that
-- consumes @b@ and produces @a@.
--
-- When @a@ and @b@ are the same, @'Dec' ('Post' a f) a@ is like the free
-- invariant sequencer.  That is, in a sense, @'Dec' ('Post' a f) a@ contains
-- both contravariant and covariant sequences side-by-side, /consuming/
-- @a@s and also /producing/ @a@s.
--
-- You can build up these values with 'injectPre', and then use whatever
-- typeclasses your @t@ normally supports to build it up, like
-- 'Conclude' (for 'Div').  You can then interpret it into both its
-- contravariant and covariant contexts:
--
-- @
-- -- interpret the covariant part
-- runCovariant :: 'Plus' g => (f ~> g) -> Div (Post a f) a -> g a
-- runCovariant f = interpret (f . getPost)
--
-- -- interpret the contravariant part
-- runContravariant :: 'Conclude' g => (f ~> g) -> Div (Post a f) a -> g a
-- runContravariant = preDivisible
-- @
--
-- The 'PostT' type wraps up @'Dec' ('Post' a f) a@ into a type @'PostT'
-- 'Dec'
-- f a@, with nice instances/helpers.
--
-- An example of a usage of this in the real world is a possible
-- implementation of the /unjson/ library's sum type constructor, to
-- implement bidrectional serializers for sum types.
data Post a f b = (b -> a) :<$>: f b

instance Contravariant f => Contravariant (Post a f) where
    contramap f (g :<$>: x) = g . f :<$>: contramap f x

infixl 4 :>$<:
infixl 4 :<$>:

-- | Turn the covariant functor combinator @t@ into an 'Invariant'
-- functor combinator; if @t f a@ "produces" @a@s, then @'PreT' t f a@ will
-- both consume and produce @a@s.
--
-- You can run this normally as if it were a @t f a@ by using 'interpret';
-- however, you can also interpret into covariant contexts with
-- 'preDivisibleT', 'preDiviseT', and 'preContravariantT'.
--
-- A useful way to use this type is to use normal methods of the underlying
-- @t@ to assemble a final @t@, then using the 'PreT' constructor to wrap
-- it all up.
--
-- @
-- data MyType = MyType
--      { mtInt    :: Int
--      , mtBool   :: Bool
--      , mtString :: String
--      }
--
-- myThing :: PreT Ap MyFunctor MyType
-- myThing = PreT $ MyType
--     <$> injectPre mtInt    (mfInt    :: MyFunctor Int   )
--     <*> injectPre mtBool   (mfBool   :: MyFunctor Bool  )
--     <*> injectPre mtString (mfString :: MyFunctor STring)
-- @
--
-- See 'Pre' for more information.
newtype PreT t f a = PreT { unPreT :: t (Pre a f) a }

instance (HFunctor t, forall x. Functor (t (Pre x f))) => Invariant (PreT t f) where
    invmap f g = PreT
               . hmap (mapPre g)
               . fmap f
               . unPreT

instance HFunctor t => HFunctor (PreT t) where
    hmap f = PreT . hmap (hmap f) . unPreT

instance Inject t => Inject (PreT t) where
    inject = PreT . inject . (id :>$<:)

instance HTraversable t => HTraversable (PreT t) where
    htraverse f = fmap PreT . htraverse (htraverse f) . unPreT

instance Interpret t f => Interpret (PreT t) f where
    interpret f = interpret f . hmap getPre . unPreT

-- | Turn the contravariant functor combinator @t@ into an 'Invariant'
-- functor combinator; if @t f a@ "consumes" @a@s, then @'PostT' t f a@ will
-- both consume and produce @a@s.
--
-- You can run this normally as if it were a @t f a@ by using 'interpret';
-- however, you can also interpret into covariant contexts with
-- 'postPlusT', 'postAltT', and 'postFunctorT'.
--
-- A useful way to use this type is to use normal methods of the underlying
-- @t@ to assemble a final @t@, then using the 'PreT' constructor to wrap
-- it all up.
--
-- @
-- myThing :: PostT Dec MyFunctor (Either Int Bool)
-- myThing = PostT $ decided $
--     (injectPost Left  (mfInt  :: MyFunctor Int ))
--     (injectPost Right (mfBool :: MyFunctor Bool))
-- @
--
-- See 'Post' for more information.
newtype PostT t f a = PostT { unPostT :: t (Post a f) a }

instance (HFunctor t, forall x. Contravariant (t (Post x f))) => Invariant (PostT t f) where
    invmap f g = PostT
               . hmap (mapPost f)
               . contramap g
               . unPostT

-- | @since 0.3.4.2
instance HFunctor t => HFunctor (PostT t) where
    hmap f = PostT . hmap (hmap f) . unPostT

-- | @since 0.3.4.2
instance Inject t => Inject (PostT t) where
    inject = PostT . inject . (id :<$>:)

instance HTraversable t => HTraversable (PostT t) where
    htraverse f = fmap PostT . htraverse (htraverse f) . unPostT

-- | @since 0.3.4.2
instance Interpret t f => Interpret (PostT t) f where
    interpret f = interpret f . hmap getPost . unPostT

-- | Run a @'PreT' t@ into a contravariant 'Divisible' context.  To run it
-- in @t@s normal covariant context, use 'interpret'.
--
-- This will work for types where there are a possibly-empty collection of
-- @f@s, like:
--
-- @
-- preDivisibleT :: Divisible g => (f ~> g) -> PreT 'Ap'    f ~> g
-- preDivisibleT :: Divisible g => (f ~> g) -> PreT 'ListF' f ~> g
-- @
preDivisibleT
    :: (forall m. Monoid m => Interpret t (AltConst m), Divisible g)
    => (f ~> g)
    -> PreT t f ~> g
preDivisibleT f = preDivisible f . unPreT

-- | Run a @'PreT' t@ into a contravariant 'Divise' context.  To run it in
-- @t@s normal covariant context, use 'interpret'.
--
-- This will work for types where there is a non-empty collection of
-- @f@s, like:
--
-- @
-- preDiviseT :: Divise g => (f ~> g) -> PreT 'Ap1'       f ~> g
-- preDiviseT :: Divise g => (f ~> g) -> PreT 'NonEmptyF' f ~> g
-- @
preDiviseT
    :: (forall m. Semigroup m => Interpret t (AltConst m), Divise g)
    => (f ~> g)
    -> PreT t f ~> g
preDiviseT f = preDivise f . unPreT

-- | Run a @'PreT' t@ into a 'Contravariant'.  To run it in
-- @t@s normal covariant context, use 'interpret'.
--
-- This will work for types where there is exactly one @f@ inside:
--
-- @
-- preContravariantT :: Contravariant g => (f ~> g) -> PreT 'Step'     f ~> g
-- preContravariantT :: Contravariant g => (f ~> g) -> PreT 'Coyoneda' f ~> g
-- @
preContravariantT
    :: (forall m. Interpret t (AltConst m), Contravariant g)
    => (f ~> g)
    -> PreT t f ~> g
preContravariantT f = preContravariant f . unPreT

-- | Run a "pre-routed" @t@ into a contravariant 'Divisible' context.  To
-- run it in @t@s normal covariant context, use 'interpret' with 'getPre'.
--
-- This will work for types where there are a possibly-empty collection of
-- @f@s, like:
--
-- @
-- preDivisible :: Divisible g => (f ~> g) -> 'Ap'    ('Pre' a f) b -> g a
-- preDivisible :: Divisible g => (f ~> g) -> 'ListF' ('Pre' a f) b -> g a
-- @
preDivisible
    :: (forall m. Monoid m => Interpret t (AltConst m), Divisible g)
    => (f ~> g)
    -> t (Pre a f) b
    -> g a
preDivisible f = foldr (divide (\x -> (x,x))) conquer
               . icollect (interpretPre f)

-- | Run a "pre-routed" @t@ into a contravariant 'Divise' context.  To
-- run it in @t@s normal covariant context, use 'interpret' with 'getPre'.
--
-- This will work for types where there are is a non-empty collection of
-- @f@s, like:
--
-- @
-- preDivise :: Divise g => (f ~> g) -> 'Ap1'       ('Pre' a f) b -> g a
-- preDivise :: Divise g => (f ~> g) -> 'NonEmptyF' ('Pre' a f) b -> g a
-- @
preDivise
    :: (forall m. Semigroup m => Interpret t (AltConst m), Divise g)
    => (f ~> g)
    -> t (Pre a f) b
    -> g a
preDivise f = foldr1 (<:>) . icollect1 (interpretPre f)

-- | Run a "pre-routed" @t@ into a 'Contravariant'.  To run it in @t@s
-- normal covariant context, use 'interpret' with 'getPre'.
--
-- This will work for types where there is exactly one @f@ inside:
--
-- @
-- preContravariant :: Contravariant g => (f ~> g) -> 'Step'     ('Pre' a f) b -> g a
-- preContravariant :: Contravariant g => (f ~> g) -> 'Coyoneda' ('Pre' a f) b -> g a
-- @
preContravariant
    :: (forall m. Interpret t (AltConst m), Contravariant g)
    => (f ~> g)
    -> t (Pre a f) b
    -> g a
preContravariant f = iget (interpretPre f)

-- | Run a @'PostT' t@ into a covariant 'Plus' context.  To run it
-- in @t@s normal contravariant context, use 'interpret'.
--
-- This will work for types where there are a possibly-empty collection of
-- @f@s, like:
--
-- @
-- postPlusT :: Plus g => (f ~> g) -> PreT 'Dec' f ~> g
-- postPlusT :: Plus g => (f ~> g) -> PreT 'Div' f ~> g
-- @
postPlusT
    :: (forall m. Monoid m => Interpret t (AltConst m), Plus g)
    => (f ~> g)
    -> PostT t f ~> g
postPlusT f = postPlus f . unPostT

-- | Run a @'PostT' t@ into a covariant 'Alt' context.  To run it
-- in @t@s normal contravariant context, use 'interpret'.
--
-- This will work for types where there is a non-empty collection of
-- @f@s, like:
--
-- @
-- postAltT :: Alt g => (f ~> g) -> PreT 'Dec1' f ~> g
-- postAltT :: Alt g => (f ~> g) -> PreT 'Div1' f ~> g
-- @
postAltT
    :: (forall m. Semigroup m => Interpret t (AltConst m), Alt g)
    => (f ~> g)
    -> PostT t f ~> g
postAltT f = postAlt f . unPostT

-- | Run a @'PostT' t@ into a covariant 'Functor' context.  To run it
-- in @t@s normal contravariant context, use 'interpret'.
--
-- This will work for types where there is exactly one @f@ inside:
--
-- @
-- postFunctorT :: Functor g => (f ~> g) -> PreT 'Step' f ~> g
-- postFunctorT :: Functor g => (f ~> g) -> PreT 'CCY.Coyoneda' f ~> g
-- @
postFunctorT
    :: (forall m. Interpret t (AltConst m), Functor g)
    => (f ~> g)
    -> PostT t f ~> g
postFunctorT f = postFunctor f . unPostT

-- | Run a "post-routed" @t@ into a covariant 'Plus' context.  To run it
-- in @t@s normal contravariant context, use 'interpret'.
--
-- This will work for types where there are a possibly-empty collection of
-- @f@s, like:
--
-- @
-- postPlus :: Plus g => (f ~> g) -> 'Dec' (Post a f) b -> g a
-- postPlus :: Plus g => (f ~> g) -> 'Div' (Post a f) b -> g a
-- @
postPlus
    :: (forall m. Monoid m => Interpret t (AltConst m), Plus g)
    => (f ~> g)
    -> t (Post a f) b
    -> g a
postPlus f = foldr (<!>) zero . icollect (interpretPost f)

-- | Run a "post-routed" @t@ into a covariant 'Alt' context.  To run it
-- in @t@s normal contravariant context, use 'interpret'.
--
-- This will work for types where there are is a non-empty collection of
-- @f@s, like:
--
-- @
-- postAlt :: Alt g => (f ~> g) -> 'Dec1' (Post a f) b -> g a
-- postAlt :: Alt g => (f ~> g) -> 'Div1' (Post a f) b -> g a
-- @
postAlt
    :: (forall m. Semigroup m => Interpret t (AltConst m), Alt g)
    => (f ~> g)
    -> t (Post a f) b
    -> g a
postAlt f = foldr1 (<!>) . icollect1 (interpretPost f)

-- | Run a "post-routed" @t@ into a covariant 'Functor' context.  To run it
-- in @t@s normal contravariant context, use 'interpret'.
--
-- This will work for types where there is exactly one @f@ inside:
--
-- @
-- postFunctor :: Functor g => (f ~> g) -> 'Step'         (Post a f) b -> g a
-- postFunctor :: Functor g => (f ~> g) -> 'CCY.Coyoneda' (Post a f) b -> g a
-- @
postFunctor
    :: (forall m. Interpret t (AltConst m), Functor g)
    => (f ~> g)
    -> t (Post a f) b
    -> g a
postFunctor f = iget (interpretPost f)

-- | Contravariantly retract the @f@ out of a 'Pre', applying the
-- pre-routing function.  Not usually that useful because 'Pre' is meant to
-- be used with covariant 'Functor's.
retractPre :: Contravariant f => Pre a f b -> f a
retractPre (f :>$<: x) = contramap f x

-- | Interpret a 'Pre' into a contravariant context, applying the
-- pre-routing function.
interpretPre :: Contravariant g => (f ~> g) -> Pre a f b -> g a
interpretPre f (g :>$<: x) = contramap g (f x)

-- | Drop the pre-routing function and just give the original wrapped
-- value.
getPre :: Pre a f b -> f b
getPre (_ :>$<: x) = x

-- | Pre-compose on the pre-routing function.
mapPre :: (c -> a) -> Pre a f b -> Pre c f b
mapPre f (g :>$<: x) = g . f :>$<: x

-- | Like 'inject', but allowing you to provide a pre-routing function.
injectPre :: Inject t => (a -> b) -> f b -> t (Pre a f) b
injectPre f x = inject (f :>$<: x)

-- | Covariantly retract the @f@ out of a 'Post', applying the
-- post-routing function.  Not usually that useful because 'Post' is meant to
-- be used with contravariant 'Functor's.
retractPost :: Functor f => Post a f b -> f a
retractPost (f :<$>: x) = fmap f x

-- | Interpret a 'Post' into a covariant context, applying the
-- post-routing function.
interpretPost :: Functor g => (f ~> g) -> Post a f b -> g a
interpretPost f (g :<$>: x) = fmap g (f x)

-- | Drop the post-routing function and just give the original wrapped
-- value.
getPost :: Post a f b -> f b
getPost (_ :<$>: x) = x

-- | Post-compose on the post-routing function.
mapPost :: (a -> c) -> Post a f b -> Post c f b
mapPost f (g :<$>: x) = f  . g :<$>: x

-- | Like 'inject', but allowing you to provide a post-routing function.
injectPost :: Inject t => (b -> a) -> f b -> t (Post a f) b
injectPost f x = inject (f :<$>: x)

instance Functor f => Invariant (Post a f) where
    invmap f g (h :<$>: x) = h . g :<$>: fmap f x

instance Contravariant f => Invariant (Pre a f) where
    invmap f g (h :>$<: x) = f . h :>$<: contramap g x

instance HFunctor (Post a) where
    hmap g (f :<$>: x) = f :<$>: g x

instance HFunctor (Pre a) where
    hmap g (f :>$<: x) = f :>$<: g x

instance HTraversable (Post a) where
    htraverse g (f :<$>: x) = (f :<$>:) <$> g x

instance HTraversable (Pre a) where
    htraverse g (f :>$<: x) = (f :>$<:) <$> g x

instance Monoid a => Inject (Post a) where
    inject x = const mempty :<$>: x

instance Monoid a => HBind (Post a) where
    hjoin (f :<$>: (g :<$>: x)) = (f <> g) :<$>: x

instance Monoid a => Interpret (Post a) f where
    retract (_ :<$>: x) = x

-- | This instance is over-contrained (@a@ only needs to be uninhabited),
-- but there is no commonly used "uninhabited" typeclass
instance (a ~ Void) => Inject (Pre a) where
    inject x = absurd :>$<: x

-- | This instance is over-contrained (@a@ only needs to be uninhabited),
-- but there is no commonly used "uninhabited" typeclass
instance (a ~ Void) => HBind (Pre a) where
    hjoin (_ :>$<: (_ :>$<: x)) = absurd :>$<: x

instance (a ~ Void) => Interpret (Pre a) f where
    retract (_ :>$<: x) = x

-- | If @t@ is a covariant functor combinator, then you applying it to
-- @'Pre' a f@ gives you a profunctor.
newtype ProPre t f a b = ProPre { unProPre :: t (Pre a f) b }

instance (HFunctor t, forall x. Functor (t (Pre x f))) => Profunctor (ProPre t f) where
    dimap f g = ProPre
              . hmap (mapPre f)
              . fmap g
              . unProPre


-- | @since 0.3.4.1
deriving instance Functor (t (Pre a f)) => Functor (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Apply (t (Pre a f)) => Apply (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Applicative (t (Pre a f)) => Applicative (ProPre t f a)
-- | @since 0.3.4.1
instance Bind (t (Pre a f)) => Bind (ProPre t f a) where
    ProPre x >>- f = ProPre $ x >>- (unProPre . f)
-- | @since 0.3.4.1
deriving instance Monad (t (Pre a f)) => Monad (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Contravariant (t (Pre a f)) => Contravariant (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Divisible (t (Pre a f)) => Divisible (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Divise (t (Pre a f)) => Divise (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Decide (t (Pre a f)) => Decide (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Conclude (t (Pre a f)) => Conclude (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Decidable (t (Pre a f)) => Decidable (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Plus (t (Pre a f)) => Plus (ProPre t f a)
-- | @since 0.3.4.1
instance Alt (t (Pre a f)) => Alt (ProPre t f a) where
    ProPre x <!> ProPre y = ProPre (x <!> y)
-- | @since 0.3.4.1
deriving instance Invariant (t (Pre a f)) => Invariant (ProPre t f a)
-- | @since 0.3.4.1
deriving instance Semigroup (t (Pre a f) b) => Semigroup (ProPre t f a b)
-- | @since 0.3.4.1
deriving instance Monoid (t (Pre a f) b) => Monoid (ProPre t f a b)
-- | @since 0.3.4.1
deriving instance Show (t (Pre a f) b) => Show (ProPre t f a b)
-- | @since 0.3.4.1
deriving instance Eq (t (Pre a f) b) => Eq (ProPre t f a b)
-- | @since 0.3.4.1
deriving instance Ord (t (Pre a f) b) => Ord (ProPre t f a b)



-- | If @t@ is a contravariant functor combinator, then you applying it to
-- @'Post' a f@ gives you a profunctor.
newtype ProPost t f a b = ProPost { unProPost :: t (Post b f) a }

instance (HFunctor t, forall x. Contravariant (t (Post x f))) => Profunctor (ProPost t f) where
    dimap f g = ProPost
              . hmap (mapPost g)
              . contramap f
              . unProPost

-- | @since 0.3.4.1
instance (HFunctor t, Contravariant (t (Post a f))) => Functor (ProPost t f a) where
    fmap f = ProPost
           . hmap (mapPost f)
           . unProPost
-- | @since 0.3.4.1
instance (HFunctor t, Contravariant (t (Post a f))) => Invariant (ProPost t f a) where
    invmap f _ = fmap f
