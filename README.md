functor-combinators
===================

*[Introductory Blog Post][combinatorpedia]* / *[Hackage][hackage]*

[combinatorpedia]: https://blog.jle.im/entry/functor-combinatorpedia.html
[hackage]: https://hackage.haskell.org/package/functor-combinators

Tools for working with *functor combinators*: types that take functors (or
other indexed types) and returns a new functor that "enhances" or "mixes" them
in some way.

The main functionality is exported in *Data.Functor.Combinators*, but more
fine-grained functionality and extra combinators (some of them
re-implementations for compatibility) are available in other modules as well.

The goal is to represent schemas, DSL's, and computations (things like parsers,
things to execute, things to consume or produce data) by assembling
"self-evident" basic primitives and subjecting them to many *different*
successive transformations and combiners.  The process of doing so:

1.  Forces you to make explicit decisions about the structure of your
    computation type as an ADT.
2.  Allows you to retain isolation of fundamental parts of your domain as
    separate types
3.  Lets you manipulate the structure of your final computation type through
    *normal Haskell techniques* like pattern matching.  The structure is
    available throughout the entire process, so you can replace individual
    components and values within your structure.
4.  Allows you to fully *reflect* the structure of your final computation
    through pattern matching and folds, so you can inspect the structure and
    produce useful summaries.

The main benefit of this library in specific is to allow you to be able to work
with different functor combinators with a uniform and lawful interface, so the
real functionality here is the wide variety of functor combinators from all
around the Haskell ecosystem.  This library does not provide the functor
combinators, as much as it re-exports them with a unified interface.  However,
it does "fill in the matrix", in a sense, of functor combinators in specific
roles that are missing from the haskell ecosystem.

To jump into using it, import *Data.Functor.Combinator*.  For a full
introduction, check out the *[Functor Combinatorpedia][combinatorpedia]*, which
goes in-depth into the motivation behind functor combinator-driven development,
examples of the functor combinators in this library, and details about how to
use these abstractions!

Comparisons
-----------

On the surface, *functor-combinators* look like it fills a similar space to
effects systems and libraries like *[mtl][]*, *[polysemy][]*,
*[freer-simple][]*, or *[fused-effects][]*.  However, the functor combinator
design pattern actually exists on a different level.

[mtl]: https://hackage.haskell.org/package/mtl
[polysemy]: https://hackage.haskell.org/package/polysemy
[freer-simple]: https://hackage.haskell.org/package/freer-simple
[fused-effects]: https://hackage.haskell.org/package/fused-effects

Functor combinator design patterns can be used to help build the *structure* of
the *data types* and schemas that define your program/DSL.  Once you build
these nice structures, you then *interpret* them into some target context. This
"target context" is the realm that libraries like *mtl* and *polysemy* can
fill; functor combinators serve to help you define a structure for your program
*before* you interpret it into whatever Applicative or Monad or effects system
you end up using.
