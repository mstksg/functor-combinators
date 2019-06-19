functor-combinators
===================

*[Introductory Blog Post][combinatorpedia]*

[combinatorpedia]: https://blog.jle.im/entry/functor-combinatorpedia.html

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
around the Haskell ecosystem.  This library also "fills in the matrix", in a
sense, of functor combinators in specific roles that are missing from the
haskell ecosystem.

To jump into using it, import *Data.Functor.Combinator*.  For a full
introduction, check out the *[Functor Combinatorpedia][]*, which goes in-depth
into the motivation behind functor combinator-driven development, examples of
the functor combinators in this library, and details about how to use these
abstractions!
