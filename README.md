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
    the enhanced type:

    ```haskell
    binterpret
        :: (Semigroupoidal t, CS t h)
        => (f ~> h)
        => (g ~> h)
        -> (t f g ~> h)

    biretract
        :: (Semigroupoidal t, CS t f)
        => t f f ~> f
    ```

*   `CM t` is the constraint on where you can *create* values of the enhanced
    type (`pureT`, `inL`, `inR`)

    ```haskell
    pureT
        :: (Monoidal t, CM t f)
        => I t ~> f

    inL :: (Monoidal t, CM t g)
        => f ~> t f g

    inR :: (Monoidal t, CM t f)
        => g ~> t f g
    ```

Most of these also have an identity, `I t`, where applying `t f (I t)` leaves `f`
unchanged (`t f (I t) ~ f`).  This is represented by the associated type `I t`.

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

Here we simply list the induced monoid with some small notes; for more details,
see the actual section for that induced monoid later on.

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

    You don't need any constraint in order to use `binterpret`, `inL`, `inR`,
    etc.

    However, note that `pureT @(:+:) :: Void1 ~> h` is effectively impossible to
    call, because no values of type `Void1 a` exist.

*   **Identity**

    ```haskell
    type I (:+:) = Void1
    ```

    `f :+: Void1` is equivalent to just `f`, because you can never have a value
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

    It is useful if you want to define a schema where you can offer *multiple*
    options for the `f a`, and the interpreter/consumer can freely pick any one
    that they want to use.

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
    type MF These1 = Steps
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

### LeftF / RightF / Joker

*   **Origin**: *[Data.HBifunctor][]* (for `LeftF` and `RightF`),
    *[Data.Bifunctor.Joker][]* (for `Joker`, which is equivalent to `LeftF`)

*   **Mixing Strategy**: "Ignore the left" / "ignore the right".

    ```haskell
    data LeftF  f g a = LeftF  { runLeftF  :: f a }
    data Joker  f g a = Joker  { runJoker  :: f a }    -- same

    data RightF f g a = RightF { runRightF :: g a }
    ```

    You can think of `LeftF` as "`:+:` without the Right case,
    `R1`", or `RightF` as "`:+:` without the Left case, `L1`".  `RightF f` is
    also equivalent to `IdentityT` for any `f`.

    This can be useful if you want the second (or first) argument to be
    ignored, and only be used maybe at the type level.

    For example, `RightF IgnoreMe MyFunctor` is equivalent to just `MyFunctor`,
    but you might want to use `IgnoreMe` as a phantom type to help limit what
    values can be used for what functions.

*   **Constraints**

    ```haskell
    type CS LeftF  = Unconstrained
    type CS Joker  = Unconstrained
    type CS RightF = Unconstrained
    ```

    Interpreting out of either of these is unconstrained, and can be done in
    any context.

*   **Identity**

    Unlike the previous functor combinators, these three are only
    `Semigroupoidal`, not `Monoidal`: this is because there is no functor `i` such
    that `LeftF i g` is equal to `g`, for all `g`, and no functor `i` such that
    `RightF f i` is equal to `f`, for all `f`.


*   **Induced Semigroup**

    ```haskell
    type SF LeftF = EnvT Any
    ```

    For `LeftF` and `Joker`, induced semigroup is `EnvT Any`.  This can be
    useful as a type that marks if an `f` is "pure" (`HPure`, `Any False`), or
    "tainted" (`HOther`, `Any True`).  It is an `f a` "tagged" with some
    boolean bit about whether it was made using `inject`, or with `consSF`.
    The *provider* of an `EnvT Any f` can specify "pure or tained", and the
    *interpreter* can make a decision based on that tag.

    ```haskell
    type SF RightF = Step
    ```

    For `RightF`, the induced semigroup is `Step`.  See `Step` and the
    information on `:+:` for more details.  This can be useful for having a
    value of `f a` at "some point", indexed by a `Natural`.

[Data.HBifunctor]: https://hackage.haskell.org/package/functor-combinators/docs/Data-HBifunctor.html
[Data.Bifunctor.Joker]: https://hackage.haskell.org/package/bifunctors/docs/Data-Bifunctor-Joker.html

Single-Argument
---------------

### Coyoneda

*   **Origin**: *[Data.Functor.Coyoneda][]*

-   **Enhancement**: The ability to map over the parameter --- a free `Functor`
    instance.

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

### ListF / NonEmptyF

*   **Origin**: *[Control.Applicative.ListF][]*

*   **Enhancement**: The ability to offer multiple options for the interpreter
    to pick from -- a free `Alt` instance.

    ```haskell
    data ListF     f a = ListF     { runListF     :: [f a]          }
    data NonEmptyF f a = NonEmptyF { runNonEmptyF :: NonEmpty (f a) }
    ```

    Can be useful if you want to provide the ability when you *define* your
    schema to provide multiple `f a`s that the *interpreter*/consumer can
    freely pick from.

    For example, for a form schema, you might have multiple ways to enter
    a name.  If you had a `Name` schema `data Name a`, then you can represent
    "many different name inputs" schema as `ListF Name a`.

    Because this has a `Plus` instance, you can use `(<!>) :: ListF f a ->
    ListF f a -> ListF f a` to combine multiple option sets, and `zero :: ListF
    f a` to provide the "choice that always fails/is unusuable".

    Also provided is `NonEmptyF`, which is a variety of `ListF` where you
    always have "at least one `f a`".  Can be useful if you want to ensure, for
    your interpreter's sake, that you always have at least one `f a` option to
    pick from.  For example, `NonEmptyF Name a` will always have at least *one*
    name schema.

    Note that this is essentially `f` `:*:`d with itself multiple times;
    `ListF` is the monoidal functor combinator induced by `:*:`, and
    `NonEmptyF` is the semigroupoidal functor combinator induced by `:*:`.

*   **Constraint**

    ```haskell
    type C ListF     = Plus
    type C NonEmptyF = Alt
    ```

    Interpreting out of a `ListF f` requires the target context to be
    `Plus`, and interpreting out of a `NonEmptyF f` requires `Alt` (because you
    will never have the empty case).  However, you can directly pattern match
    on the list and pick an item you want directly, which requires no
    constraint.

[Control.Applicative.ListF]: https://hackage.haskell.org/package/functor-combinators/docs/Control-Applicative-ListF.html

### Ap / Ap1

*   **Origin**: *[Control.Applicative.Free][]* / *[Data.Functor.Apply.Free][]*

*   **Enhancement**: The ability to provide multiple `f`s that the interpreter
    *must* consume *all* of --- the free `Applicative`.

    While `ListF` may be considered "multiple options offered", `Ap` can be
    considered "multiple actions all required".  The interpreter must
    consume/interpret *all* of the multiple `f`s in order to interpret an `Ap`.

    For example, for a form schema, you might want to have multiple form
    elements.  If a single form element is `data FormElem a`, then you can
    make a multi-form schema with `Ap FormElem a`.  The consumer of the form
    schema must handle *every* `FormElem` provided.

    Note that ordering is not enforced: while the consumer must handle each `f`
    eventually, they are free to handle it in whatever order they desire.  In
    fact, they could even all be handled in parallel.  See `Free` for a version
    where ordering is enforced.

    Because this has an `Applicative` instance, you can use `(<*>) :: Ap f (a
    -> b) -> Ap f a -> Ap f b` to sequence multiple `Ap f`s together, and `pure
    :: a -> Ap f a` to produce a "no-op" `Ap` without any `f`s.

    `Ap` has some utility over `Free` in that you can pattern match on the
    constructors directly and look at each individual sequenced `f a`, for
    static analysis, before anything is ever run or interpreted.

    Also provided is `Ap1`, which is a variety of `Ap` where you always have to
    have "at least one `f`".  Can be useful if you want to ensure, for example,
    that your form has at least one element.

    Note that this is essentially `f` `Day`d with itself multiple times;
    `Ap` is the monoidal functor combinator induced by `Day` and
    `Ap1` is the semigroupoidal functor combinator induced by `Day`.

*   **Constraint**

    ```haskell
    type C Ap  = Applicative
    type C Ap1 = Apply
    ```

    Interpreting out of an `Ap f` requires the target context to be
    `Applicative`, and interpreting out of a `Ap1 f` requires `Apply` (because
    you will never have the pure case).

[Control.Applicative.Free]: https://hackage.haskell.org/package/free/docs/Control-Applicative-Free.html
[Data.Functor.Apply.Free]: https://hackage.haskell.org/package/functor-combinators/docs/Data-Functor-Apply-Free.html

### Alt

*   **Origin**: *[Control.Alternative.Free][]*

*   **Enhancement**: A combination of both `ListF` and `Ap`: provide a choice
    (`ListF`-style) of sequences (`Ap`-style) of choices of sequences of
    choices .... --- the free `Alternative`.

    ```haskell
    Alt f ~ ListF (Ap (ListF (Ap (ListF (Ap (...))))
          ~ ListF (Ap (Alt f))
    ```

    This type imbues `f` with both sequential "must use both" operations (via
    `<*>`) and choice-like "can use either" operations (via `<|>`).

    It can be useful for implementing parser schemas, which often involve both
    sequential and choice-like combinations.  If `f` is a primitive parsing
    unit, then `Alt f` represents a non-deterministic parser of a bunch of
    `f`s one after the other, with multiple possible results.

*   **Constraint**

    ```haskell
    type C Alt = Alternative
    ```

    Interpreting out of an `Alt f` requires the target context to be
    `Alternative` --- it uses `<*>` for sequencing, and `<|>` for choice.

[Control.Alternative.Free]: https://hackage.haskell.org/package/free/docs/Control-Alternative-Free.html

### Free / Free1

*   **Origin**: *[Control.Monad.Freer.Church][]*, which is a variant of
    *[Control.Monad.Free][]* that is compatible with `HFunctor`.

*   **Enhancement**: The ability to provide multiple `f`s that the interpreter
    must consume *in order*, sequentially --- the free `Monad`.

    Contrast with `Ap`, which also sequences multiple `f`s together, but
    without any enforced order.  It does this by *hiding* the "next `f a`" until
    the previous `f a` has already been interpreted.

    Perhaps more importantly, you can sequence `f`s in a way where the *choice
    of the next `f`* is allowed to depend on the *result of the previous `f`*.

    For example, in an interactive "wizard" sort of schema, where `f`
    represents a wizard dialog box, we can represent our wizard using `Free f
    a` --- an ordered sequence of dialog boxes, where the choice of the next
    box can depend on result of the previous box.  Contrast to `Ap`, where the
    choice of all dialog boxes must be made in advanced, up-front, before
    reading any input from the user.

    In having this, however, we loose the ability to be able to inspect each `f
    a` before interpreting anything.

    Because this has a `Monad` instance, you can use `(<*>) :: Free f (a
    -> b) -> Free f a -> Free f b` and `(>>=) :: Free f a -> (a -> Free f b) ->
    Free f b)` to sequence multiple `Free f`s together,
    and `pure :: a -> Free f a` to produce a "no-op" `Free` without any `f`s.

    Also provided is `Free1`, which is a variety of `Free1` where you always have to
    have "at least one `f`".  Can be useful if you want to ensure, for example,
    that your wizard has at least one dialog box.

    Note that this is essentially `f` `Comp`d with itself multiple times;
    `Free` is the monoidal functor combinator induced by `Comp` and
    `Free1` is the semigroupoidal functor combinator induced by `Comp`.

*   **Constraint**

    ```haskell
    type C Free  = Monad
    type C Free1 = Bind
    ```

    Interpreting out of a `Free f` requires the target context to be
    `Monad`, and interpreting out of a `Free1 f` requires `Bind` (because
    you will never have the pure case).

[Control.Monad.Free]: https://hackage.haskell.org/package/free/docs/Control-Monad-Free.html

### Lift / MaybeApply

*   **Origin**: *[Control.Applicative.Lift][]* / *[Data.Functor.Apply][]* (the
    same type)

*   **Enhancement**: Make `f` "optional" in the schema in a way that the
    interpreter can still work with as if the `f` was still there --- the free
    `Pointed`.

    ```haskell
    data Lift f a = Pure  a
                  | Other (f a)

    newtype MaybeApply f a = MaybeApply { runMaybeApply :: Either a (f a) }
        -- same
    ```

    Can be useful so that an `f a` is *optional* for the schema definition, but
    in a way where the consumer can still continue from it as if they *had* the
    `f`.

    It can be used, for example, to turn an required parameter `Param a` into
    an optional paramter `Lift Param a`.

    Contrast this to `MaybeF`: this allows the interpreter to still "continue
    on" as normal even if the `f` is not there.  However, `MaybeF` forces the
    interpreter to abort if the `f` is not there.

    This can be thought of as `Identity :+: f`.

*   **Constraint**

    ```haskell
    type C Lift = Pointed
    ```

    Interpreting out of a `Lift f` requires the target context to be
    `Pointed` --- it uses `point :: a -> f a` to handle the case where the `f`
    is not there.  Note that every `Applicative` instance should also be a
    `Pointed` instance; use `unsafePointed` to provide an instance for any
    `Applicative` the same way you'd use `upgradeC`.

[Control.Applicative.Lift]: https://hackage.haskell.org/package/transformers/docs/Control-Applicative-Lift.html
[Data.Functor.Apply]: https://hackage.haskell.org/package/semigroupoids/docs/Data-Functor-Apply.html

### MaybeF

*   **Origin**: *[Control.Applicative.ListF][]*

*   **Enhancement**: Make `f` "optional" in the schema in a way that the
    interpreter must fail if the `f` is not present.

    ```haskell
    newtype MaybeF f a = MaybeF { runMaybeF :: Maybe (f a) }
    ```

    Can be useful so that an `f a` is *optional* for the schema definition; if
    the `f` is not present, the consumer must abort the current branch, or find
    some other external way to continue onwards.

    Contrast this to `Lift`, which is an "optional" `f` that the consumer may
    continue on from.

    This can be thought of as `Proxy :+: f`.

*   **Constraint**

    ```haskell
    type C MaybeF = Plus
    ```

    Interpreting out of a `Lift f` requires the target context to be
    `Plus` --- it uses `zero :: f a` to handle the case where the `f`
    is not there.  Note that this is actually "over-constrained": we really
    only need `zero`, and not all of `Plus` (which includes `<!>`).  However,
    there is no common typeclass in Haskell that provides this, so this is the
    most pragmatic choice.

### EnvT

*   **Origin**: *[Control.Comonad.Trans.Env][]*

*   **Enhancement**: Provide extra (monoidal) data alongside `f a` that the
    interpreter can access.  Basically tuples extra `e` alongside the `f a`.

    ```haskell
    newtype EnvT e f a = EnvT e (f a)
    ```

    You can use this as basically tupling some extra data alongside an `f a`.
    It can be useful if you want to provide extra information that isn't inside
    the `f` for the interpreter use for interpretation.

    When using `inject :: f a -> EnvT e f a`, it uses `mempty` as the initial
    `e` value.

    This can be thought of as `Const e :*: f`.

    This type appears specialized --- as `EnvT (Sum Natural)` as `Step`, and
    also as the semigroupoidal functor combinator `EnvT Any` induced by of
    `LeftF`.  For `Step`, the extra information tracks "how deep we are" in
    along a chain of possible branches, and for `EnvT Any` as an induced
    semigroup, the `Any` (a wrapped `Bool`) tracks if we are "pure" or
    "impure".

*   **Constraint**

    ```haskell
    type C (EnvT e) = Unconstrained
    ```

    Interpreting out of `EnvT e` requires no constraints.

[Control.Comonad.Trans.Env]: https://hackage.haskell.org/package/comonad/docs/Control-Comonad-Trans-Env.html

### Step

*   **Origin**: *[Control.Applicative.Step][]*

*   **Enhancement**: Tuples the `f a` with an extra natural number index.

    ```haskell
    data Step f a = Step { stepPos :: Natural, stepVal :: f a }
    ```

    This is essentially a specialized `EnvT`: it's `EnvT (Sum Natural)`.

    This is a useful type because it can be seen as equivalent to `f :+: f :+:
    f :+: f :+: f ...` forever: it's an `f`, but at some index.

    The speicalized functions `stepUp` and `stepDown` allow you to match on the
    "first" `f` in that infinite chain (these are also exposed as `consSF` and
    `matchSF` for `:+:`); it will increment and decrement the index relatively
    to make this work properly.

*   **Constraint**

    ```haskell
    type C Step = Unconstrained
    ```

    Interpreting out of `Step` requires no constraints.

[Control.Applicative.Step]: https://hackage.haskell.org/package/functor-combinators/docs/Control-Applicative-Step.html

### Steps

*   **Origin**: *[Control.Applicative.Step][]*

*   **Enhancement**: The ability to offer multiple *indexed*
    options for the interpreter to pick from.  Like `NonEmptyF`, except with
    each `f a` existing at an indexed position that the consumer/interpreter
    can look up or access.

    ```haskell
    newtype Steps f a = Steps { getSteps :: NEMap Natural (f a) }
    ```

    This is like a mix between `NonEmptyF` and `Step`: multiple `f a` options
    (at least one) for the consumer/interpreter to pick from.  Unlike
    `NonEmptyF`, each `f a` exists at an "index" --- there might be one at 0,
    one at 5, one at 100, etc.

    Another way of looking at this is like an infinite *sparse array* of `f
    a`s: it's an inifinitely large collection where each spot may potentially
    have an `f a`.

    Useful for "provide options that the consumer can pick from, index, or
    access", like `ListF`/`NonEmptyF`.

    This type can be seen as an infinite ``f `These1` f `These1` f `These1` f
    ...``, and along these lines, `stepsDown` and `stepsUp` exist analogous to
    `stepUp` and `stepDown` to treat a `Steps` in this manner.

*   **Constraint**

    ```haskell
    type C Steps = Alt
    ```

    Interpreting out of `Steps` requires an `Alt` to combine different
    possibilities.  It does not require a full `Plus` constraint because we
    never need `zero`: a `Steps f a` always has at least one `f a`.

### Final

*   **Origin**: *[Data.HFunctor.Final][]*

*   **Enhancement**: `Final c` will lift `f` into a free structure of any
    typeclass `c` --- give it all of the actions/API of a typeclass for free.
    `Final c f` is the "free `c`" over `f`.

    ```haskell
    data Final c f a
    ```

    In a way, this is the "ultimate free structure": it can fully replace all
    other free structures of typeclasses of kind `Type -> Type`.  For example:

    ```haskell
    Coyoneda  ~ Final Functor
    ListF     ~ Final Plus
    NonEmptyF ~ Final Alt
    Ap        ~ Final Applicative
    Ap1       ~ Final Apply
    Free      ~ Final Monad
    Free1     ~ Final Bind
    Lift      ~ Final Pointed
    IdentityT ~ Final Unconstrained
    ```

    All of these are connections are witnessed by instances of the typeclass
    `FreeOf`.

    In fact, `Final c` is often more performant than the actual concrete free
    structures.

    The main downside is that you cannot directly pattern match on the
    structure of a `Final c` the same way you can pattern match on, say, `Ap`
    or `ListF`.  Doing so may require a concrete throwaway data type with the
    proper instances.

    You can also think of this as the "ultimate `Interpret`", because with
    `inject` you can push `f` into `Final c f`, and with `interpret` you only
    ever need the `c` constraint to "run"/interpret this.

    So, next time you want to give an `f` the ability to `<*>` and `pure`, you
    can throw it into `Final Applicative`: `f` now gets "sequencing" abilities,
    and is equivalent to `Ap f`.

    If you want the API of a given typeclass `c`, you can inject `f` into
    `Final c`, and you get the API of that typeclass for free on `f`.

*   **Constraint**

    ```haskell
    type C (Final c) = c
    ```

    Interpreting out of a `Final c` requires `c`, since that is the extra
    context that `f` is lifted into.

[Data.HFunctor.Final]: https://hackage.haskell.org/package/functor-combinators/docs/Data-HFunctor-Final.html

### Chain / Chain1

*   **Origin**: *[Data.HFunctor.Chain][]*

*   **Enhancement**: `Chain t` will lift `f` into a linked list of `f`s chained
    by `t`.

    ```haskell
    -- i is intended to be the identity of t
    data Chain t i f a = Done (i a)
                       | More (t f (Chain t i f a))
    ```

    For example, for `:*:`, `Chain (:*:) Proxy f` is equivalent to one of:

    ```haskell
    Proxy                       ~ Done Proxy
    x                           ~ More (x :*: Done Proxy)
    x :*: y                     ~ More (x :*: More (y :*: Done Proxy))
    x :*: y :*: z               ~ More (x :*: More (y :*: More (z :*: Done Proxy)))
    -- etc.
    ```

    This is useful because it provides a nice uniform way to work with all
    "induced Monoidal functors".  That's because:

    ```haskell
    ListF       ~ Chain (:*:)  Proxy
    Ap          ~ Chain Day    Identity
    Free        ~ Chain Comp   Identity
    Step        ~ Chain (:+:)  Void
    Steps       ~ Chain These1 Void
    ```

    This isomorphism is witnessed by `unrollMF` (turn into the `Chain`) and
    `rerollMF` (convert back from the `Chain`).

    We also have a "non-empty" version, `Chain1`, for induced semigroupoids:

    ```haskell
    data Chain1 t f a = Done1 (f a)
                      | More1 (t f (Chain1 t f a))
    ```

    ```haskell
    NonEmptyF   ~ Chain1 (:*:)
    Ap1         ~ Chain1 Day
    Free1       ~ Chain1 Comp
    Step        ~ Chain1 (:+:)
    Steps       ~ Chain1 These1
    EnvT Any    ~ Chain1 LeftF
    Step        ~ Chain1 RightF
    ```

    Using `ListF`, `Ap`, `Free`, `Step`, `Steps`, etc. can feel very different,
    but with `Chain` you get a uniform interface to pattern match on (and
    construct) all of them in the same way.

    Using `NonEmptyF`, `Ap1`, `Free1`, `Step`, `Steps`, `EnvT`, etc. can feel
    very different, but with `Chain1` you get a uniform interface to pattern
    match on (and construct) all of them in the same way.

*   **Constraint**

    ```haskell
    type C (Chain  t (I t)) = CM t
    type C (Chain1 t      ) = CS t
    ```

    Interpreting out of a `Chain` requires the monoidal constraint on `t`,
    since we have to "squish" all of the layers of `t` together with a
    potential empty case.  Interpreting out of a `Chain1` requires the
    semigroupoidal constraint on `t`, since we have to squish all of the layers
    of `t` together, but we don't have to worry about the empty case.

    For example, we have:

    ```haskell
    type C (Chain  (:*:) Proxy) = Plus
    type C (Chain1 (:*:)      ) = Alt

    type C (Chain  Day Identity) = Applicative
    type C (Chain1 Day         ) = Apply

    type C (Chain  Comp Identity) = Monad
    type C (Chain1 Comp         ) = Bind
    ```

[Data.HFunctor.Chain]: https://hackage.haskell.org/package/functor-combinators/docs/Data-HFunctor-Chain.html

### IdentityT

*   **Origin**: *[Data.Functor.Identity][]*

*   **Enhancement**: None whatsoever; it adds no extra structure to `f`, and
    `IdentityT f` is the same as `f`

    ```haskell
    data IdentityT f a = IdentityT { runIdentityT :: f a }
                       | More (t f (Chain t i f a))
    ```

    This isn't too useful on its own, but it can be useful to give to the
    functor combinator combinators as a no-op functor combinator.  It can also
    be used to signify "no structure", or as a placeholder until you figure out
    what sort of structure you want to have.

    In that sense, it can be thought of as a "`ListF` with always one item", a
    "`MaybeF` that's always `Just`"', an "`Ap` with always one sequenced item",
    a "`Free` with always exactly one layer of effects", etc.

*   **Constraint**

    ```haskell
    type C IdentityT = Unconstrained
    ```

    Interpreting out of `IdentityT` requires no constraints --- it basically
    does nothing.

[Data.Functor.Identity]: https://hackage.haskell.org/package/base/docs/Data-Functor-Identity.html

### ProxyF / ConstF

*   **Origin**: *[Data.HFunctor][]*

*   **Enhancement**: "Black holes" --- they completely forget all the structure
    of `f`, and are impossible to `interpret` out of.

    ```haskell
    data ProxyF f a = ProxyF
    data ConstF e f a = ConstF e
    ```

    `ProxyF` is essentially `ConstF ()`.

    These are both valid functor combinators in that you can inject into them,
    and `retract . inject == id` is technically true (the best kind of true).

    You can use them if you want your schema to be impossible to interpret, as
    a placeholder or to signify that one branch is uninterpretable.  In this
    sense, this is like a "`ListF` that is always empty" or a "`MaybeF` that is
    always `Nothing`".

    Because of this, they aren't too useful on their own --- they're more
    useful in the context of swapping out and combining or manipulating with
    other functor combinators or using with functor combinator combinators.

*   **Constraint**

    ```haskell
    type C ProxyF     = Impossible
    type C (ConstF e) = Impossible
    ```

    Interpreting out of these requires an impossible constraint.

[Data.HFunctor]: https://hackage.haskell.org/package/base/docs/Data-HFunctor.html

Combinator Combinators
----------------------

### ComposeT

### HLift

### HFree
