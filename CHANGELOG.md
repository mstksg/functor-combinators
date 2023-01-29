Changelog
=========

Version 0.4.1.1
---------------

*January 29, 2023*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.4.1.1>

*   Fix builds and warnings for GHC 9.2 and base 4.16

Version 0.4.1.0
---------------

*September 29, 2021*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.4.1.0>

*   All of the missing instances to the typeclasses added in 0.4 that I could
    remember.
*   Variations of `concatInply` / `concatInplicative` / `concatInalt` /
    `concatInplus` renamed to `gatheredN` / `swervedN` / `gatheredN1` /
    `swervedN1`.
*   `gatherN`, `gatherN1` added with typeclass-based multi-arity functions.
*   GHC 9.0 compatibility (@ocharles)

Version 0.4.0.0
---------------

*September 3, 2021*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.4.0.0>

*   Finally add *Data.Functor.Invariant.Inplicative* and
    *Data.Functor.Internative*, with the typlecasses `Inply`, `Inplicative`,
    `Inalt`, `Inplus`, and `Internative`, the invariant versions of
    `Apply`/`Divise`, `Applicative`/`Divisible`, `Alt`/`Decide`,
    `Plus`/`Choose`, and `Alternative`/`Decidable`.
*   Move *Data.Functor.Invariant.DivAp* and *Data.Functor.Invariant.DecAlt* to
    *Data.Functor.Invariant.Inplicative.Free* and
    *Data.Functor.Invariant.Internative.Free*, respectively.

    Their specialized `gather`/`knot`/`swerve`/`reject` are now a part of the
    typeclasses.
*   `concatDivAp` family and `concatDecAlt` family of functions generalized to
    work for all *Inplicative* and *Inplus*, respectively, and moved to the
    modules for their respective typeclasses as `concatInplicative`,
    `concatInply`, `concatInplus`, and `concatInalt`.
*   Changed the order of arguments on `gather` and `swerve` to be consistent
    with the arguments of `invmap`, `Day`, and `Night`.
*   Changed the order of arguments in the `Gather`, and `Swerve` patterns to
    be more consistent with the new order of arguments for `gather`/`swerve`.
*   Changed the order of arguments in the `DivAp1` and `DecAlt1` patterns to
    be more consistent with the order of arguments for `Day` and `Night`.
*   Add `runDay` and `runNight` for invariant `Day` and `Night`, using the
    `Inply` and `Inalt` typeclasses, respectively. `runDay` is found in
    *Data.Functor.Invariant.Inplicative*, even though it should belong in
    *Data.Functor.Invariant.Day*, but that's in a different package.
*   Add `dather`, `necide`, and `nerve` to invariant `Day`, contravariant
    `Night`, invariant `Night`, in parallel to `dap` for covariant `Day`. Uses
    the `Inply`, `Divise`, and `Inalt` typeclasses, respectively. `dather` is
    found in *Data.Functor.Invariant.Inplicative*, even though it should
    belong in *Data.Functor.Invariant.Day*, but that's in a different package.
*   Add `hfor` and `hfor1` to *Data.HFunctor.HTraversable*.

Version 0.3.6.0
---------------

*August 27, 2020*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.3.6.0>

*   *Data.HFunctor.HTraversable* added, providing `HTraversable` and
    `HTraversable1`.
*   *Control.Monad.Freer.Church*: Missing `Apply`, `Alt`, and `Plus` instances
    added for `Comp`.
*   *Data.HBifunctor*: `HFunctor` instances for `LeftF`, `RightF`, `Joker`,
    `Void3`, and `Comp` made more kind-polymorphic
*   *Data.HFunctor.Interpret*: `itraverse` added, mimicking `htraverse` for
    proper `Interpret` instances.
*   *Data.HFunctor.Chain*: `foldChainA` and `foldChain1A` added, for effectful
    folding of chains.

Version 0.3.5.0
---------------

*August 15, 2020*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.3.5.0>

*   `DayChain` and `NightChain` renamed to `DivAp` and `DecAlt`, to better
    reflect their abstracted nature ever since *0.3.4.0*.  The modules are
    renamed to *Data.Functor.Invariant.DivAp* and
    *Data.Functor.Invariant.DecAlt*.

*   **v0.3.5.1**: Fixed infinite recursion bug for Tensor instances of
    invariant `Day`/`Night`.

Version 0.3.4.0
---------------

*August 14, 2020*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.3.4.0>

*   *Data.HFunctor.Route*: A new twist on getting invariant functor
    combinators.  Instead of creating new ones, utilize existing functor
    combinators with `Pre`/`Post`.
*   *Data.Functor.Invariant.Day.Chain* and *Data.Functor.Invariant.Night.Chain*
    created, factoring out the `Chain` part of the invariant `Day`/`Night`.
    This was done to fix the fact that *Data.Functor.Invariant.Day* is a module
    that already existed in *kan-extensions*.  Oops!
    *   As a consequence, `DayChain` and `NightChain` are now newtype wrappers
        instead of plain type synonyms.

*   **v0.3.4.1**: Add in missing `Functor` and `Invariant` instances for
    `ProPre` and `ProPost`, as well as a bunch of instances for `ProPre`.
*   **v0.3.4.2**: Add in missing `HFunctor`, `Inject`, `Interpret` instances
    for `PostT`.

Version 0.3.3.0
---------------

*August 11, 2020*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.3.3.0>

*   *Control.Applicative.ListF*: Missing contravariant instances added for
    `MaybeF`.
*   *Data.HFunctor*: Add `injectMap` and `injectContramap`, two small utility
    functions that represent common patterns in injection and mapping.
*   *Data.Functor.Combinator*: Replace `divideN` and related functions with
    `dsum` and `dsum1`, which is an altogether cleaner interface that doesn't
    require heterogenous lists.  A part of a larger project on cleaning up
    `Divisible` tools.
*   *Data.Functor.Contravariant.Divise*: Add useful utility functions `dsum`
    and `<:>`, which makes the type of `divise` closer to that of `<|>` and
    `asum`.
*   *Data.Functor.Contravariant.Divisible.Free*: Implement `Div` in terms of a
    list, instead of the mirrored `Ap`.  Should make it much easier to use,
    although a less-than-ideal `Coyoneda` is required to keep it compatible
    with the contravariant `Day` in *kan-extensions*.  Added patterns to
    recover the original interface.


Version 0.3.2.0
---------------

*August 9, 2020*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.3.2.0>

*   *Data.HFunctor.Interpret*: `icollect`, `icollect1` now are more
    constrained: they only work on things that have `Interpret` instances for
    *all* `Monoid m` or `Semigroup m` in `AltConst m`.  While this doesn't
    affect how it works on any types in this library, it does make the type
    signature a little more clean (hiding the usage of `DList`) and prevents
    one from making an odd `Interpret` instance that does something weird with
    the `DList`.  This also allows us to drop the direct *dlist >= 1.0* dependency.
*   *Data.HFunctor.Interpret*: `biapply`, `bifanout`, `bifanout1` added as
    contravariant consumer versions of `iget`, `icollect`, and `icollect1`.
*   *Data.HBifunctor.Associative*: `bicollect` `bicollect1` removed because
    they really don't make sense for associative tensors, which can only have
    at most one of each tensor.
*   *Data.HBifunctor.Associative*: `biapply` added as the contravariant
    consumer version of `biget`.
*   *Data.Functor.Invariant.Day*: Add conversion functions from chains to the
    covariant/invariant versions, `chainAp`, `chainAp1`, `chainDiv`, and
    `chainDiv1`.
*   *Data.Functor.Invariant.Night*: Add conversion functions from chains to the
    covariant/invariant versions, `chainDec`, `chainDec1`, `chainListF`,
    `chainNonEmptyF`.  Also add "undescored" versions to the covariant
    versions, `toCoNight_`, `chainListF_`, `chainNonEmptyF_`, to more
    accurately represent the actual contravariant either-based day convolution.
    Also changed `Share` to `Swerve`.
*   *Data.Functor.Combinator*: `AltConst` re-exported.


Version 0.3.1.0
---------------

*August 7, 2020*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.3.1.0>

*   *Data.HFunctor.Interpret*: `getI` and `collectI` made more efficient, and
    renamed to `iget` and `icollect`, respectively, to mirror `biget` and
    `bicollect`.  `getI` and `collectI` are left in with a deprecation warning.
    `icollect1` added to ensure a non-empty collection.  `AltConst` added to
    aid in implementation.
*   *Data.HBifunctor.Associative*: `bicollect1` added to ensure a non-empty
    collection.  *biget* and *bicollect* made more efficient.
*   *Data.Functor.Contravariant.Night*, *Data.Functor.Invariant.Night*:
    `refuted` added for a convenient `Not`.  Missing `Invariant` instance for
    `Not` also added.
*   *Data.HFunctor.Chain*: `chainPair` and `chain1Pair` renamed to `toChain`
    and `toChain1`, respectively, to mirror `toListBy` and `toNonEmptyBy`.

Version 0.3.0.0
---------------

*August 5, 2020*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.3.0.0>

*   *Data.HBifunctor.Associative*, *Data.HBifunctor.Tensor*: Support for
    `Contravariant` and `Invariant` functor combinators. Main change to the
    infrastructure: add a `FunctorBy` associated constraint to `Associative` to
    signal what "sort of functor" the tensor supports: it should either be
    `Unconstrained`, `Functor`, `Contravariant`, or `Invariant`.
*   *Data.Functor.Contravariant.Divise*, *Data.Functor.Contravariant.Decide*,
    and *Data.Functor.Contravariant.Conclude*: Temporarily add in the
    semigroupoidal contravariant typeclasses. These should only be needed until
    they get merged into *semigroupoids*.
*   *Data.Functor.Contravariant.Divisible*: Add free structures for
    contravariant typeclass hierarchy.
*   Added in some new day convolutions:

    *   *Data.Functor.Contravariant.Night*: `Night`, a contravariant day
        convolution using `Either`, which is the tensor that generates
        `Conclude` (and `Decidable` kinda).
    *   *Data.Functor.Invariant.Day*: `Day`, an *invariant* day convolution
        using tuples.
    *   *Data.Functor.Invariant.Night*: `Night`, an *invariant* day convolution
        using either.

    For the invariant day convolutions, we *could* write free monoids on them
    (like `Ap`/`Div`/`Dec`).  But instead we just outsource our free structures
    to `Chain`, providing useful pattern synonyms and folding functions to
    pretend like we had an actual free structure.
*   *Data.Functor.Combinator*: Useful functions in for working with divisible
    and decidable contravariant functors: `divideN`, `diviseN`, `concludeN`,
    `decideN`, `divideNRec`, and `diviseNRec`.
*   `Contravariant` and `Invariant` instances for many types.
*   *Data.HFunctor.Final*: `FreeOf` adjusted to allow for contravariant free
    types.
*   *Data.Functor.Combinator.Unsafe*: Add `unsafeDivise` and `unsafeConclude`,
    to mirror the situation with `unsafeApply` and `unsafePlus`.

Version 0.2.0.0
---------------

*November 11, 2019*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.2.0.0>

*   Major restructuring of the hbifunctor-based classes. `Data.HBifunctor.Associative`
    and `Data.HBifunctor.Tensor` are more or less completely rewritten; the
    typeclasses are restructured in order to more properly reflect the math
    that motivates them.  See the updated type classes to see what methods
    ended up where.

    However, much of the external API that is independent of the underlying
    abstraction is effectively unchanged (`biget`, etc.)

    For the most part, the migration would involve:

    *   `SF`, `MF` are now `NonEmptyBy` and `ListBy`, respectively.
    *   `-SF` and `-MF` as suffixes for function names now become `-NE` and
        `-LB`.

*   `upgradeC` no longer exists; use unsafe functions from
    *Data.Functor.Combinator.Unsafe* instead, on a per-tensor basis.

*   Restructuring of `Interpret`: It now takes an extra type parameter, the
    type to interpret into.  This makes it more consistent with the new `MonoidIn`
    and `SemigroupIn`.  Most of the external API should be effectively
    unchanged.

    For the most part, the migration would only affect people who *write*
    instances of `Interpret`.  Instead of

    ```haskell
    instance Interpret MyType where
        type C MyType = Monad
    ```

    you would write:

    ```haskell
    instance Monad f => Interpret MyType f where
    ```


Version 0.1.1.1
---------------

*July 13, 2019*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.1.1.1>

*   Moved to *trivial-constraints-0.6.0.0*

Version 0.1.1.0
---------------

*June 19, 2019*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.1.1.0>

*   `appendChain` and `appendChain1`

Version 0.1.0.1
---------------

*June 19, 2019*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.1.0.1>

*   Small tweaks for haddock generation and dependency bounds.

Version 0.1.0.0
---------------

*June 19, 2019*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.1.0.0>

*   Initial release
