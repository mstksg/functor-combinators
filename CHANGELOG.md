Changelog
=========

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
