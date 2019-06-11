functor-combinators
===================

Tools for working with *functor combinators*: types that take functors (or
other indexed types) and returns a new functor that "enhances" or "mixes" them
in some way.

The main functionality is exported in *Data.Functor.Combinators*, but more
fine-grained functionality and extra combinators (some of them
re-implementations for compatibility) are available in other modules as well.

The main benefit of *functor combinators* as a design pattern is that sometimes
it is beneficial to state our program (like a schema, description, or EDSL) as
a functor or indexed type.  Functor combinators allows us to build complex
functors out of simple primitive ones.

The main benefit of this library in specific is to allow you to be able to work
with different functor combinators with a uniform and lawful interface, so the
real functionality here is the wide variety of functor combinators from all
around the Haskell ecosystem.

What is a functor combinator?
-----------------------------

A functor combinator takes functors (or other indexed types) and returns a new
functor, enhances or mixes them together in some way.

That is, they take things of kind `k -> Type` and themselves return a `k ->
Type`.

This lets us build complex functors out of simpler "primitive" ones.

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

Combinator Zoo
==============

Two-Argument
------------

Binary functor combinators "mix together" two functors/indexed types in
different ways.

Each one has two associated constraints:

*   `CS t` is the constraint on where you can *interpret* or *run* values of
    the enhanced type (`binterpret`, `biretract`).
*   `CM t` is the constraint on where you can *create* values of the enhanced
    type (`pureT`, `inL`, `inR`)

Most of these also have an identity, `i`, where applying `t f i` leaves `f`
unchanged (`t f i ~ f`).  This is represented by the associated type `I t`.

All of these also have a "apply to self many times", for situations where you
want to represent the act of applying `t` to the same `f` multiple times,
called the "induced monoidal functor combinator", given by `MF t` (or `SF t`
for the "nonempty" variant).

You can "convert" back and forth by using:

```haskell
toMF   :: t f f ~> MF t
nilMF  :: I t ~> MF t
consMF :: t f (MF t) ~> MF t
```

and other helper functions.

### :+: / Sum

*   **Origin**: *[GHC.Generics][]* (for `:+:`) / *[Data.Functor.Sum][]* (for
    `Sum`)

*   **Mixing Strategy**: "Either-or": provide either case, and user has to
    handle both possibilities.  Basically higher-order `Either`.

    ```haskell
    data (f :+: g) a
        = L1 (f a)
        | R1 (g a)

    data Sum f g a
        = InL (f a)
        | InR (g a)
    ```

    It can be useful for situations where you can validly use one or the other
    in your schema or functor.  For example, if you are describing an HTTP request,
    we could have `data GET a` describing a GET request and `data POST a`
    describing a POST request; `(GET :+: POST) a` would be a functor that
    describes either a GET or POST request.

    The person who creates the `f :+: g` decides which one to give, and the
    person who consumes/interprets/runs the `f :+: g` must provide a way of
    handling *both*

    ```haskell
    binterpret @(:+:)
        :: (f ~> h)
        -> (g ~> h)
        -> (f :+: g) a
        -> h a
    ```

*   **Constraints**

    ```haskell
    type CS (:+:) = Unconstrained
    type CM (:+:) = Unconstrained
    ```

    You don't need any constraint in order to use `inL`

*   **Identity**

    ```haskell
    type I (:+:) = Void
    ```

    `f :+: Void` is equivalent to just `f`, because you can never have a value
    of the right branch.

*   **Induced Monoid**

    ```haskell
    type SF (:+:) = Step
    type MF (:+:) = Step
    ```

    `Step` is the result of an infinite application of `:+:` to the same value:

    ```haskell
    type Step f = f :+: f :+: f :+: f :+: f :+: f :+: ... etc.
    ```

    It's not a particularly useful type, but it can be useful if you want to
    provide an `f a` alongside "which position" it is on the infinite list.
    Repeatedly using `consMF` will push the `f` further and further along the
    list.

[GHC.Generics]: https://hackage.haskell.org/package/base/docs/GHC-Generics.html
[Data.Functor.Sum]: https://hackage.haskell.org/package/base/docs/Data-Functor-Sum.html

### :\*: / Product

*   **Origin**: *[GHC.Generics][]* (for `:*:`) / *[Data.Functor.Product][]* (for
    `Product`)

*   **Mixing Strategy**: "Both, separately": provide values from *both*
    functors, and the user can choose which one they want to use.  Basically a
    higher-order tuple.

    ```haskell
    data (f :*: g) a = f a :*: g a

    data Product f g a = Pair (f a) (g a)
    ```

    It can be useful for situations where your schema/functor must be
    *specified* using *both* functors, but the *interpreter* can choose to use
    only one or the other (or both).

    ```haskell
    prodOutL :: (f :*: g) ~> f
    prodOutR :: (f :*: g) ~> g
    ```

*   **Constraints**

    ```haskell
    type CS (:*:) = Alt
    type CM (:*:) = Plus
    ```

    Fully interpreting out of `:*:` requires [`Alt`][Alt] (to combine both
    branches), but if we use only one branch or ther other, we can use
    `prodOutL` or `prodOutR` and require no constraint.

*   **Identity**

    ```haskell
    type I (:*:) = Proxy
    ```

    `f :+: Proxy` is equivalent to just `f`, because the left hand side doesn't
    add anything extra to the pair.

*   **Induced Monoid**

    ```haskell
    type SF (:*:) = NonEmptyF
    type MF (:*:) = ListF
    ```

    `ListF f a` is a "list of `f a`s".  It represents the posibility of having
    `Proxy` (zero items), `x :: f a` (one item), `x :*: y` (two items), `x :*:
    y :*: z` (three items), etc.

    It's basically an ordered collection of `f a`s `:*:`d with each other.

    It can be useful if your schema provides a "bag" of multiple `f a` options,
    and the interpreter can choose to use any combination of items in the bag
    that they want.

    `NonEmptyF` is the version of `ListF` that has "at least one `f a`".

[GHC.Generics]: https://hackage.haskell.org/package/base/docs/GHC-Generics.html
[Data.Functor.Product]: https://hackage.haskell.org/package/base/docs/Data-Functor-Product.html
[Alt]: https://hackage.haskell.org/package/semigroupoids/docs/Data-Functor-Alt.html

### Day

*   **Origin**: *[Data.Functor.Day][]*

*   **Mixing Strategy**: "Both, together forever": provide values from *both*
    functors, and the user *must* also *use* both.

    It can be useful for situations where your schema/functor must be
    *specified* using *both* functors, and the user must also *use* both.

    ```haskell
    binterpret @Day
        :: Apply h          -- superclass of Applicative
        => (f ~> h)
        -> (g ~> h)
        -> Day f g ~> h
    ```

    Unlike for `:*:`, you always have to interpret *both* functor values in
    order to interpret a `Day`.  It's a "full mixing".

*   **Constraints**

    ```haskell
    type CS Day = Apply
    type CM Day = Applicative
    ```

    We need `Applicative` to interpret out of a `Day`.  Note that all
    `Applicative` instances should have an `Apply` instance, but due to how
    *base* is structured, `Apply` is not a true superclass officially.  You can
    use `upgradeC @Day` to bring an `Apply` instance into scope for any
    `Applicative` instance.

    For example, let's say we had a type `Parser` from an external library that
    is `Applicative` but not `Apply`.  In that case,

    ```haskell
    biretract :: Day Parser Parser a -> Parser a
    ```

    is a type error (because `Parser` has no `Apply` instance), but

    ```haskell
    upgradeC @Day (Proxy @Parser) biretract
        :: Day Parser Parser a -> Parser a
    ```

    will typecheck.

*   **Identity**

    ```haskell
    type I Day = Identity
    ```

    `Day f Identity` is equivalent to just `f`, because `Identity` adds no
    extra effects or structure.

*   **Induced Monoid**

    ```haskell
    type SF Day = Ap1
    type MF Day = Ap
    ```

    `Ap f a` is a bunch of `f x`s `Day`d with each other.  It is either:

    *   `a` (zero `f`s)
    *   `f a` (one `f`)
    *   `Day f f a` (two `f`s)
    *   `Day f (Day f f) a` (three `f`s)
    *   .. etc.

    Like `ListF` this is very useful if you want your schema to provide a "bag"
    of `f a`s and your interpreter *must use all of them*.

    For example, if we have a schema for a command line argument parser, each
    `f` may represent a command line option.  To interpret it, we must look at
    *all* command line options.

    `Ap1` is a version with "at least one" `f a`.

[Data.Functor.Day]: https://hackage.haskell.org/package/kan-extensions/docs/Data-Functor-Day.html

### Comp

*   **Origin**: *[Control.Monad.Freer.Church][]*.  Note that an equivalent type
    is also found in *[GHC.Generics][]* and *[Data.Functor.Compose][]*, but
    they are incompatible with the `HBifunctor` typeclass.

*   **Mixing Strategy**: "Both, together, sequentially ": provide values from
    *both* functors; the user must *use* both, and *in order*.

    ```haskell
    data Comp f g a = Comp (f (g a))
    ```

    It can be useful for situations where your schema/functor must be specified
    using both functors, and the user must *use* both, but also enforcing that
    they must use both in the *given order*: that is, for a `Comp f g`, they
    interpret `f` *before* they interpret `g`.

    ```haskell
    binterpret @Day
        :: Bind h          -- superclass of Monad
        => (f ~> h)
        -> (g ~> h)
        -> Comp f g ~> h
    ```

    Unlike for `:*:`, you always have to interpret *both* functor values.  And,
    unlike for `Day`, you must interpret both functor values *in that order*.

*   **Constraints**

    ```haskell
    type CS Comp = Bind
    type CM Comp = Monad
    ```

    We need `Monad` to interpret out of a `Comp`.  Note that all
    `Monad` instances should have a `Bind` instance, but due to how
    *base* is structured, `Bind` is not a true superclass officially.  See the
    note on `Day` for more information on getting around this with `upgradeC`.

*   **Identity**

    ```haskell
    type I Comp = Identity
    ```

    `Comp f Identity` is equivalent to just `f`, because `Identity` adds no
    extra effects or structure.

*   **Induced Monoid**

    ```haskell
    type SF Day = Free1
    type MF Day = Free
    ```

    `Free f a` is a bunch of `f x`s composed with each other.  It is either:

    *   `a` (zero `f`s)
    *   `f a` (one `f`)
    *   `f (f a)` (two `f`s)
    *   `f (f (f a))` (three `f`s)
    *   .. etc.

    `Free` is very useful because it allows you to specify that your schema can
    have many `f`s, sequenced one after the other, in which the *choice* of
    "the next `f`" is allowed to depend on the *result* of "the previous `f`".

    For example, in an interactive "wizard" sort of schema, where `f`
    represents a wizard dialog box, we can represent our wizard using `Free f
    a` --- an ordered sequence of dialog boxes, where the choice of the next
    box can depend on result of the previous box.

    `Free1` is a version with "at least one" `f a`.

[Control.Monad.Freer.Church]: https://hackage.haskell.org/package/functor-combinators/docs/Control-Monad-Freer-Church.html
[Data.Functor.Compose]: https://hackage.haskell.org/package/base/docs/Data-Functor-Compose.html

### These1

*   **Origin**: *[Data.Functor.These][]*.

*   **Mixing Strategy**: "Either-or, or both": provide either (or both) cases,
    and user has to handle both possibilities.  An "inclusive either"

    ```haskell
    data These1 f g a
        = This1  (f a)
        | That1        (g a)
        | These1 (f a) (g a)
    ```

    This can be useful for situations where your schema/functor can be
    specified using one functor or another, or even both.  See description on
    `:+:` for examples.

    The person who creates the `These1 f g` decides which one to give, and the
    person who consumes/interprets/runs the `f :+: g` must provide a way of
    handling *both* situations.

    ```haskell
    binterpret @These
        :: Alt h
        => (f ~> h)
        -> (g ~> h)
        -> These f g a
        -> h a
    ```

    You can also pattern match on the `These1` directly to be more explicit
    with how you handle each case.

*   **Constraints**

    ```haskell
    type CS These1 = Alt
    type CM These1 = Alt
    ```

    You need at least `Alt` to be able to interpret out of a `These1`, because
    you need to be able to handle the case where you have *both* `f` and `g`,
    and need to combine the result.

*   **Identity**

    ```haskell
    type I These1 = Void
    ```

    `These1 f Void` is equivalent to just `f`, because it means the `That1` and
    `These1` branches will be impossible to construct, and you are left with
    only the `This1` branch.

*   **Induced Monoid**

    ```haskell
    type SF These1 = Steps
    type MF THese1 = Steps
    ```

    `Steps` is the result of an infinite application of `These1 to the same value:

    ```haskell
    type Steps f = f `These1` f `These1` f `These1` f `These1` ... etc.
    ```

    It essentially represents an infinite *sparse* array of `f a`s, where an `f a` might
    exist at many different positions, with gaps here and there.  There is
    always at least *one* `f a`.

    Like `Step`, it's not particularly useful, but it can be used in situations
    where you want a giant infinite sparse array of `f a`s, each at a given
    position, with many gaps between them.

[Data.Functor.These]: https://hackage.haskell.org/package/these/docs/Data-Functor-These.html

Single-Argument
---------------

### Coyoneda

*   **Origin**: *[Data.Functor.Coyoneda][]*

*   **Enhancement**: A `Functor` instance.

    Can be useful if `f` is created using a `GADT` that cannot be given a
    `Functor` instance.

    For example, here is an indexed type that represents
    the type of a "form element", where the type parameter represents the
    output result of the form element.

    ```haskell
    data FormElem :: Type -> Type where
        FInput    :: FormElem String
        FTextbox  :: FormElem Text
        FCheckbox :: FormElem Bool
        FNumber   :: FormElem Int
    ```

    Then `Coyoneda FormElem` has a `Functor` instance.  We can now fmap over
    the result type of the form element; for example, `fmap :: (a -> b) ->
    Coyoneda FormElem a -> Coyoneda FormElem b` takes a form element whose
    result is an `a` and returns a form element whose result is a `b`.

*   **Constraint**

    ```haskell
    type C Coyoneda = Functor
    ```

    Interpreting out of a `Coyoneda f` requires the target context to be
    `Functor`.

[Data.Functor.Coyoneda]: https://hackage.haskell.org/package/kan-extensions/docs/Data-Functor-Coyoneda.html

### Ap

### Ap1

### Alt

### Lift / MaybeApply

### ListF

### NonEmptyF

### MaybeF

### Free

### Free1

### Final

### IdentityT

### ProxyF

### Chain

### Chain1

### Step

### Steps

Combinator Combinators
----------------------

### ComposeT

### HLift

### HFree
