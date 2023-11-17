# Verified Parser Combinators

Parser combinators in Dafny, inspired from the model (Meijer&Hutton 1996).

This library offers two styles of functional parser combinators.

- The first parsers style is a synonym for `seq<character> -> ParseResult<Result>` that supports monadic styles, is straightforward to use, but results in lots of closing parentheses.

- The second parsers style is a datatype wrapper around the first style, which enable to define functions as infix or suffixes, which makes parsers sometimes easier to read and helps decreasing nesting.

## Library usage

The tutorial in [`Tutorial.dfy`](examples/Tutorial.dfy) shows how to import the library call the two parsers style API, apply the parser to a string, and also use the PrintFailure to pretty print the failure along with the line/col where it occurred.

To view a full example of how to use the parser combinator library,
especially how to define a recursive parser that is guaranteed to terminate,
please refer to the files [`polynomialParser.dfy`](examples/polynomialParser.dfy) and [`polynomialParserBuilders.dfy`](examples/polynomialParserBuilder.dfy), which both parse polynomial expressions.

As a quick walkthrough, here is a test to parse a Tic-tac-toe grid:

```
method {:test} TestTicTacToe() {
  var x := OrSeq([
    String("O"), String("X"), String(" ")
  ]);
  var v := String("|");
  var row := Concat(x, ConcatR(v, Concat(x, ConcatR(v, x))));
  var sep := String("\n-+-+-\n");
  var grid := 
    Concat(row, ConcatR(sep, Concat(row, ConcatR(sep, row))));
  var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
              // 012345 678901 234567 890123 45678
  var r := grid(input);
  expect r.IsFailure();
  PrintFailure(input, r);
}
```

it displays the following:

```
Error:
5: P| |O
   ^
expected 'O', or
expected 'X', or
expected ' '
```
## What is verified?

Despite combinators enabling to define mutually recursive parsers (`RecursiveMap`, `Recursive`), Dafny will always check termination. When using recursive combinators, termination is checked at run-time so it does not prevent quick prototyping and iterations, and error messages about non-termination are always precise (either the ordering, or the progression).

This library offers a predicate on parsers of the first style `Valid()`, which
indicates that such parsers will never raise a fatal result, and will always return a
string that is suffix of the string they are given as input. Many combinators have
a proof that, if their inputs are Valid(), then their result is Valid().
Checking validity statically could help design parsers that do even less checks at run-time, but it has not been developed in this library.

This library also offers a dual type to parser, named Displayer, which is `(Result, seq<character>) -> seq<character>`. It only defines the dual of the Concat parser combinator and proves the roundtrip to be the identity. Because Dafny does not offer
compilable predicate to check that a datatype constructor is included in another one,
writing combinators for this kind of parser dual is difficult.

## Relationship to JSON parsers

The JSON parser is very specialized and the type of the parsers combinators it is using is actually a subset type.
Subset types are known to be a source of proof brittleness,
so this library design is not using subset types.
That said, it is possible to create an adapter around a JSON parser to make it a parser of this library.

# Caveats

- Recursive parsers will consume stack and, in programming languages that have a finite amount of stack, programs can get out of memory. Prefer `Rep` and `RepSeq` as much as possible as they are tail-recursive.

# Implementation notes

The module hierarchy is as follow:

```
abstract module Parsers {
  type C
}
module StringParsers {
  type C: Char
}

abstract module ParsersBuilders {
  import P: Parsers
}
module StringParsersBuilders {
  import P = StringParsers
}
```


## FAQ: 

### What properties can we use it to prove?

* You get for free that parsers terminate, at worst with a run-time "fatal" parser result "no progress and got back to the same function"
* You can actually prove the absence of fatal errors. I have several lemmas that propagate this property through parsers combinators. I'm working on a lemma for the recursive case (already done in a previous formalism, need to migrate)
* You can prove the equivalence between various combinations of parser combinators (e.g. Bind/Succed == Map)
* You can use these parser combinators as a specification for optimized methods that perform the same task but perhaps with a different representation, e.g. array and position instead of sequences of characters.

### How does it backtrack? Like Parsec (fails if tokens are consumed)?

There are several way parsers can backtrack in the current design.
* A parser not consuming any input when returning a recoverable error can be ignored for combinators with alternatives like `Or`, `Maybe`, `If` or `ZeroOrMore` (respectively `O([...])`, `.?()`, `.If()` and `.ZeroOrMore()` if using builders)
* It's possible to transform a parser to not consume any input when it fails (except fatal errors) via the combinator `?(...)` (`.??()` if using builders). This means the failure will have the same input as previously given, making it possible for surrounding combinators to explore alternatives.
* The combinators `BindResult`, a generalization of the `Bind` combinator when considering parsers as monads, lets the user decides whether to continue on the left parser's remaining input or start from the beginning.