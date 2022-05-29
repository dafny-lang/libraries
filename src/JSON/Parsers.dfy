include "../BoundedInts.dfy"
include "../Wrappers.dfy"
include "Cursors.dfy"

module {:options "/functionSyntax:4"} Parsers {
  import opened BoundedInts
  import opened Wrappers

  import opened Views.Core
  import opened Cursors

  type SplitResult<+T, +R> = CursorResult<Split<T>, R>

  type Parser<+T, +R> = p: Parser_<T, R> | p.Valid?()
    // BUG(https://github.com/dafny-lang/dafny/issues/2103)
    witness ParserWitness<T, R>() // BUG(https://github.com/dafny-lang/dafny/issues/2175)
  datatype Parser_<+T, +R> = Parser(fn: FreshCursor -> SplitResult<T, R>) {
    ghost predicate Valid?() {
      forall ps': FreshCursor :: fn(ps').Success? ==> fn(ps').value.ps.StrictlySplitFrom?(ps')
    }
  }

  function {:opaque} ParserWitness<T, R>(): (p: Parser_<T, R>)
    ensures p.Valid?()
  {
    Parser(_ => Failure(EOF))
  }

  // BUG(): It would be much nicer if `SubParser` was a special case of
  // `Parser`, but that would require making `fn` in parser a partial
  // function `-->`.  The problem with that is that we would then have to
  // restrict the `Valid?` clause of `Parser` on `fn.requires()`, thus
  // making it unprovable in the `SubParser` case (`fn` for subparsers is
  // typically a lambda, and the `requires` of lambdas are essentially
  // uninformative/opaque).
  datatype SubParser_<+T, +R> = SubParser(
    ghost ps: Cursor,
    ghost pre: FreshCursor -> bool,
    fn: FreshCursor --> SplitResult<T, R>)
  {
    ghost predicate Valid?() {
      && (forall ps': FreshCursor | pre(ps') :: fn.requires(ps'))
      && (forall ps': FreshCursor | ps'.StrictlySplitFrom?(ps) :: pre(ps'))
      && (forall ps': FreshCursor | pre(ps') :: fn(ps').Success? ==> fn(ps').value.ps.StrictlySplitFrom?(ps'))
    }
  }
  type SubParser<+T, +R> = p: SubParser_<T, R> | p.Valid?()
    witness SubParserWitness<T, R>() // BUG(https://github.com/dafny-lang/dafny/issues/2175)

  function {:opaque} SubParserWitness<T, R>(): (subp: SubParser_<T, R>)
    ensures subp.Valid?()
  {
    SubParser(Cursor([], 0, 0, 0),
              (ps: FreshCursor) => false,
              (ps: FreshCursor) => Failure(EOF))
  }
}
