Changelog
=========

Version 0.2.0.0
---------------

*November 11, 2019*

<https://github.com/mstksg/functor-combinators/releases/tag/v0.2.0.0>

*   Major restructuring of the hbifunctor-based classes. `Data.HBifunctor.Associative`
    and `Data.HBifunctor.Tensor` are more or less completely rewritten; the
    typeclasses are restructured in order to more properly reflect the math
    that motivates them.

    However, much of the external API that is independent of the underlying
    abstraction is effectively unchanged (`biget`, etc.)

*   Restructuring of `Interpret`: It now takes an extra type parameter, the
    type to interpret into.  This makes it more consistent with the new `MonoidIn`
    and `SemigroupIn`.  Most of the external API should be effectively
    unchanged.

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
