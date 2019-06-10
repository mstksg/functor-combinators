# functor-combinators

Tools for working with *functor combinators*: types that take functors (or
other indexed types) and returns a new functor that "enhances" or "mixes" them
in some way.

The main functionality is exported in *Data.Functor.Combinators*, but more
fine-grained functionality and extra combinators (some of them
re-implementations for compatibility) are available in other modules as well.

The main benefit is to allow you to be able to work with different functor
combinators with a uniform and lawful interface, so the real functionality here
is the wide variety of functor combinators from all around the Haskell
ecosystem.

## What is a functor combinator?

A functor combinator takes functors (or other indexed types) and returns a new
functor, enhances or mixes them together in some way.

That is, they take things of kind `k -> Type` and themselves return a `k ->
Type`.

For example, `ReaderT r` is a famous one that takes a functor `f` and enhances
it with "access to an `r` environment" functionality.

Another famous one is `Free`, which takes a functor `f` and enhances it with
"sequential binding" capabilities: it turns `f` into a `Monad`.

Sometimes, we have binary functor combinators, like `:+:`, which takes two
functors `f` and `g` and returns a functor that is "either" `f` or `g`.  Binary
functor combinators "mix together" the functionality of different functors in
different ways.

### Common Functionality

Most of these functor combinators allow us to "swap out" the underlying
functor, retaining all of the "enhanced" structure:

```haskell
-- | Swap out underlying functor for a single-argument functor combinator
hmap
    :: HFunctor t
    => (forall x. f x -> g x)
    -> t f a
    -> t g a

-- | Swap out underlying functors for a two-argument functor combinator
hbimap
    :: HBifunctor t
    => (forall x. f x -> h x)
    -> (forall x. g x -> j x)
    -> t f g a
    -> t g j a
```

However, for the documentation (and this list), the concept of a "natural
transformation" between `f` and `g` --- a function of type `forall x. f x -> g
x`, is given a type synonym:

```haskell
type f ~> g = forall x. f x -> g x
```

Then the type signatures of `hmap` and `hbimap` become:


```haskell
hmap
    :: HFunctor t
    => (f ~> g)
    -> (t f ~> t g)

hbimap
    :: HBifunctor t
    => (f ~> h)
    -> (g ~> j)
    -> (t f g ~> t g j)
```

You can also always "lift" a functor value into its transformed type:

```haskell
inject
    :: Inject t
    => f ~> t f

inL :: (Monoidal t, CM t g)     -- more on the `CM t` later
    => f ~> t f g

inR :: (Monoidal t, CM t f)     -- more on the `CM t` later
    => g ~> t f g
```

The final goal is to "interpret" the transformed functor into some target
context, provided the target context implements the proper constraints:

```haskell
-- | Interpret unary functor combinator
interpret
    :: (Interpret t, C t g)
    => (f ~> g)             -- ^ interpreting function
    -> (t f ~> g)

-- | Interpret binary functor combinator
binterpret
    :: (Semigroupoidal t, CS t h)
    => (f ~> h)             -- ^ interpreting function on f
    => (g ~> h)             -- ^ interpreting function on g
    -> (t f g ~> h)
```

Each functor combinator defines a constraint (`C` for unary functor
combinators, and `CS` and `CM` for binary functor combinators) that allows you
to "exit", or "run" the functor combinator.

For some concrete examples, for `ReaderT r`:

```haskell
type C (ReaderT r) = MonadReader r

interpret @(MonadReader r)
    :: MonadReader r g
    => (f ~> g)
    -> ReaderT r f a
    -> g a

type C Free = Monad

interpret @Free
    :: Monad g
    => (f ~> g)
    -> Free f a
    -> g a

type CM (:+:) = Unconstrained   -- no constraints on exiting

binterpret @(:+:)
    :: (f ~> h)
    -> (g ~> h)
    -> (f :+: g) a
    -> h a
```

We see that `interpret` lets you "run" a `ReaderT r f` into any `MonadReader r
g` and "run" a `Free` in any monad `g`, and `binterpret` lets you "run" a
function over both branches of an `f :+: g` to produce an `h`.

There are other various utility functions that can be built on `interpret` and
`binterpret` (like `retract`, `biretract`, `getI`, `biget`, etc.), as well, for
convenience in running.

Without further ado, let's run down all of the combinators!
