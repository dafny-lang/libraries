include "../Wrappers.dfy"
include "library.dfy"

// Functional parsers are consuming the string from the left to the right.
abstract module Parsers {
  import Wrappers
  import Printer
  type Option<T> = Wrappers.Option<T>

  type C(!new, ==) // The character of the sequence being parsed

  datatype Either<+L, +R> =
    // Type to return when using the Or parser
    Left(l: L) | Right(r: R)
    

  datatype FailureLevel =
    // PFailure level for parse results. An Error will be propagated to the top
    // while a Recoverable can be caught by a disjunctive pattern.
    // For example, if the parser Const?() fails, then it returns a Recoverable,
    // but the parser Const() will return an error.
    Error | Recoverable

  datatype ParseResult<+R> =
      // ParseResult is a failure-compatible type
    | PFailure(level: FailureLevel, message: string, remaining: seq<C>)
      // Returned if a parser failed
    | PSuccess(result: R, remaining: seq<C>)
      // Returned if a parser succeeds, with the increment in the position
  {
    predicate IsFailure() {
      PFailure?
    }

    function PropagateFailure<U>(): ParseResult<U>
      requires IsFailure()
    {
      PFailure(level, message, remaining)
    }

    function Extract(): (R, seq<C>)
      requires !IsFailure()
    {
      (result, remaining)
    }

    function MapResult<R'>(f: R -> R'): ParseResult<R'> {
      match this
      case PSuccess(result, remaining) =>
        PSuccess(f(result), remaining)
      case PFailure(level, message, remaining) =>
        PFailure(level, message, remaining)
    }
  }
  type Parser<+R> = seq<C> -> ParseResult<R>
  // A parser is a total function from a position to a parse result
  // Because it returns a delta pos, it cannot return a position negative from the origing
  // If the parsing is out of context, it will return a failure.

  type ParserSelector<!R> = string -> Option<Parser<R>>
  // A parser selector is a function that, given a name that exists,
  // returns a parser associated to this name

  predicate IsRemaining(input: seq<C>, remaining: seq<C>)
    // Remaining is a suffix of the input
  {
    && |remaining| <= |input|
    && input[|input|-|remaining|..] == remaining
  }

  opaque ghost predicate NonCrashing<R>(underlying: Parser<R>)
    // A parser is valid for an input if it never returns a fatal error
    // and always returns a suffix of its input
  {
    forall input: seq<C> ::
      && (underlying(input).PFailure? ==> underlying(input).level == Recoverable)
      && IsRemaining(input, underlying(input).remaining)
  }

  // Parser combinators.
  // The following functions make it possible to create and compose parsers
  // All these combinators provide non-crashing parsers if their inputs are noncrashing

  opaque function Succeed_<R>(result: R): (p: Parser<R>)
    // A parser that does not consume any input and returns the given value
    // This is a generic function, it's better to use the Succeed function on strings.
  {
    (input: seq<C>) => PSuccess(result, input)
  }

  lemma Succeed_NonCrashing<R>(result: R)
    ensures NonCrashing(Succeed_(result))
  { reveal NonCrashing(), Succeed_(); }

  lemma Succeed_NonCrashingAuto<R>()
    ensures forall result: R :: NonCrashing(Succeed_(result))
  { reveal NonCrashing(), Succeed_();  }

  opaque function Epsilon_(): (p: Parser<()>)
  {
    Succeed_(())
  }

  lemma Epsilon_NonCrashing()
    ensures NonCrashing(Epsilon_())
  { reveal NonCrashing(), Epsilon_(); Succeed_NonCrashing(()); }

  lemma AboutEpsilon_(input: seq<C>)
    ensures
      var p := Epsilon_();
      && p(input).PSuccess?
      && p(input).remaining == input
  {
    reveal Epsilon_();
    reveal Succeed_();
  }

  opaque function Fail_<R>(message: string, level: FailureLevel := Recoverable): Parser<R>
    // A parser that does not consume any input and returns the given failure
  {
    (input: seq<C>) => PFailure(level, message, input)
  }

  lemma Fail_NonCrashing<R>(message: string)
    ensures NonCrashing<R>(Fail_(message, Recoverable))
  { reveal Fail_(); reveal NonCrashing(); }

  lemma Fail_NonCrashingAuto<R>()
    ensures forall message :: NonCrashing<R>(Fail_(message, Recoverable))
  { reveal Fail_(); reveal NonCrashing(); }

  opaque function Bind_<L, R>(
    left: Parser<L>,
    right: L -> Parser<R>
  ) : (p: Parser<R>)
  {
    (input: seq<C>)
    =>
      var (leftResult, remaining) :- left(input);
      right(leftResult)(remaining)
  }

  opaque function Bind__<L, R>(
    left: Parser<L>,
    right: (L, seq<C>) -> Parser<R>
  ) : (p: Parser<R>)
    // Useful for recursive binds
  {
    (input: seq<C>)
    =>
      var (leftResult, remaining) :- left(input);
      right(leftResult, remaining)(remaining)
  }

  ghost predicate BindRightNonCrashing<L(!new), R>(right: (L, seq<C>) -> Parser<R>) {
    forall l: L, input: seq<C> :: NonCrashing(right(l, input))
  }

  lemma Bind_NonCrashing<L, R>(
    left: Parser<L>,
    right: (L, seq<C>) -> Parser<R>
  ) 
    requires NonCrashing(left)
    requires BindRightNonCrashing(right)
    ensures NonCrashing(Bind__(left, right))
  {
    reveal Bind__(), NonCrashing();
    var p := Bind__(left, right);
    forall input: seq<C> ensures
      && (p(input).PFailure? ==> p(input).level == Recoverable)
      && IsRemaining(input, p(input).remaining)
    {

    }
  }

  ghost predicate Bind_NonCrashingRight<L(!new), R(!new)>(left: Parser<L>)
    requires NonCrashing(left)
  {
    forall right: (L, seq<C>) -> Parser<R> | BindRightNonCrashing(right) ::
      NonCrashing(Bind__(left, right))
  }

  lemma Bind_NonCrashingAuto<L(!new), R(!new)>() 
  ensures forall left: Parser<L> | NonCrashing(left) ::
    Bind_NonCrashingRight<L, R>(left)
  {
    forall left: Parser<L> | NonCrashing(left),
           right: (L, seq<C>) -> Parser<R> | BindRightNonCrashing(right)
    ensures
      NonCrashing(Bind__(left, right))
    {
      Bind_NonCrashing(left, right);
    }
  }

  opaque function Map_<R, U>(underlying: Parser<R>, mappingFunc: R -> U)
    : (p: Parser<U>)
    // A parser combinator that makes it possible to transform the result of a parser in another one
    // The mapping function can be partial
    // ensures forall pos | MapSpec(size, underlying, mappingFunc, pos) ::
    //          p.requires(pos)
  {
    (input: seq<C>) =>
      var (result, remaining) :- underlying(input);
      var u := mappingFunc(result);
      PSuccess(u, remaining)
  }

  opaque function Concat_<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<(L, R)>)
    // Makes it possible to concatenate two consecutive parsers and return the pair of the results
  {
    (input: seq<C>)
    =>
      var (l, remaining) :- left(input);
      var (r, remaining2) :- right(remaining);
      PSuccess((l, r), remaining2)
  }

  opaque function ConcatR_<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<R>)
    // Return only the result of the right parser if the two parsers match
  {
    (input: seq<C>)
    =>
      var (l, remaining) :- left(input);
      var (r, remaining2) :- right(remaining);
      PSuccess(r, remaining2)
  }

  opaque function ConcatL_<L, R>(
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<L>)
    // Return only the result of the right parser if the two parsers match
  {
    (input: seq<C>)
    =>
      var (l, remaining) :- left(input);
      var (r, remaining2) :- right(remaining);
      PSuccess(l, remaining2)
  }

  opaque function Repeat<R>(
    underlying: Parser<R>
  ): Parser<seq<R>> {
    (input: seq<C>) => Repeat_(underlying, [], input)
  }

  opaque function {:tailrecursion true} Repeat_<R>(
    underlying: Parser<R>,
    acc: seq<R>,
    input: seq<C>
  ): (p: ParseResult<seq<R>>)
    decreases |input|
  // Repeat the underlying parser over the input until a recoverable failure happens
  // and returns the accumulated results
  {
    match underlying(input)
    case PSuccess(result, remaining) =>
      if |remaining| >= |input| then PSuccess(acc + [result], input) else
      Repeat_(underlying, acc + [result], remaining)
    case PFailure(Error, message, remaining) =>
      PFailure(Error, message, remaining)
    case PFailure(Recoverable, message, remaining) =>
      PSuccess(acc, input)
  }

  opaque function Fixpoint<R(!new)>(
    underlying: Parser<R> -> Parser<R>
  ): (p: Parser<R>)
    // Given a function that requires a parser and a position to return a parse result,
    // provide this function the Fixpoint() parser itself
    // so that it makes it possible to iteratively parse the result
  {
    (input: seq<C>) => Fixpoint_(underlying, input)
  }

  opaque function Fixpoint_<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: seq<C>
  ): (p: ParseResult<R>)
    // Given a function that combines a (recursive) parser and a position to obtain a parse result,
    // returns the parse result associated to recursively applying the function.
    // If partially applied on "underlying" and "size", it would returns the solution to the equation:
    // f = pos => underlying(f, pos)
    decreases |input|
  {
    var callback: Parser<R> :=
      (remaining: seq<C>) =>
        if |remaining| < |input| then
          Fixpoint_(underlying, remaining)
        else if |remaining| == |input| then
          PFailure(Recoverable, "No progress", remaining)
        else
          PFailure(Error, "Fixpoint called with an increasing remaining sequence", remaining);
    underlying(callback)(input)
  }
  /*opaque function FixpointMap<R(!new)>(
    maxPos: nat,
    underlying: map<string, (string -> Option<Parser<R>>, nat) -> ParseResult<R>>,
    fun: string): Parser<R>
  {
    (pos: nat) => FixpointMap_(maxPos, underlying, fun, pos)
  }*/
  datatype RecursiveDef<!R> = RecursiveDef(
    order: nat, 
    definition: (string -> Option<Parser<R>>) -> Parser<R>
  )
  opaque function FixpointMap_<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string,
    input: seq<C>
  ): (p: ParseResult<R>)
    // Given a function that combines a (recursive) parser selector and a position to obtain a parse result,
    // returns the parse result associated to recursively applying the function.
    // If partially applied on "underlying" and "fun", it would return the solution f<"fun"> to the equations:
    // f<name> = pos => underlying[fun](f, pos)
    decreases |input|, if fun in underlying then underlying[fun].order else 0
  {
    if fun !in underlying then PFailure(Error, "Parser '"+fun+"' not found", input) else
    var RecursiveDef(orderFun, definitionFun) := underlying[fun];
    var callback: string -> Option<Parser<R>>
      :=
      (fun': string) =>
        if fun' !in underlying.Keys then
          Option.None
        else
          var RecursiveDef(orderFun', definitionFun') := underlying[fun'];
          Option.Some(
           (remaining: seq<C>) =>
             if |remaining| < |input| || (|remaining| == |input| && orderFun' < orderFun) then
               FixpointMap_(underlying, fun', remaining)
             else if |remaining| == |input| then
               PFailure(Recoverable, "Non progressing recursive call requires that order of '"
                 +fun'+"' ("+Printer.natToString(orderFun')+") is lower than the order of '"+fun+"' ("+Printer.natToString(orderFun)+")", remaining)
            else
               PFailure(Error, "Parser did not return a suffix of the input", remaining)
          );
      definitionFun(callback)(input)
  }

  /*  
  ghost predicate FixMapSpecInnerInner<R(!new)>(
    fun: string, fun': string, functions: set<string>, maxPos: nat, callback: string -> Option<Parser<R>>, u: nat)
  {
    forall u': nat | u <  u' <= maxPos || (u == u' && |fun'| < |fun|) ::
      && callback(fun').Some?
      && var x := callback(fun').value(u');
      && (x.PSuccess? ==> u' + x.deltaPos <= maxPos)
  }
  
  ghost predicate FixMapSpecInner<R(!new)>(fun: string, functions: set<string>, maxPos: nat, callback: string -> Option<Parser<R>>, u: nat)
    // Specification for FixpointMap.
    // Ensures that, for any other function, if this function is in the set of admissible `functions`,
    // then callback should not only accept it, but then accept any position at a second argument if
    // 1) This position is strictly greater than the current position u
    // 2) Or this position is the same but the function name is smaller.
  {
    && u <= maxPos
    && forall fun': string <- functions ::
         FixMapSpecInnerInner(fun, fun', functions, maxPos, callback, u)
  }

  ghost predicate FixpointMapSpecOnce<R(!new)>(fun': string, impl: ParserMapper<R>, otherFuns: set<string>, maxPos: nat)
  {
    forall callback: ParserSelector<R>, u: nat |
      && FixMapSpecInner(fun', otherFuns, maxPos, callback, u)
      :: var x := impl(callback, u);
         && (x.PSuccess? ==> u + x.deltaPos <= maxPos)
  }

  lemma AboutFixpointMap_<R(!new)>(
    maxPos: nat,
    underlying: map<string, (string -> Option<Parser<R>>, nat) -> ParseResult<R>>,
    fun: string,
    pos: nat
  )
    requires pos <= maxPos
    requires 
      forall fun' <- underlying.Keys ::
        FixpointMapSpecOnce(fun', underlying[fun'], underlying.Keys, maxPos)
    ensures
      AboutFixpointMap_Ensures(maxPos, underlying, fun, pos) 
  {
    reveal FixpointMap_();
    var p := FixpointMap_(maxPos, underlying, fun, pos);

    var callback: string -> Option<Parser<R>>
      :=
      (fun': string) =>
        if fun' !in underlying.Keys then
          None
        else
          Some(
           (pos': nat) =>
             if pos < pos' <= maxPos || (pos' == pos && |fun'| < |fun|) then
               FixpointMap_(maxPos, underlying, fun', pos')
             else if pos' == pos then
               PFailure(Recoverable, "Non progressing recursive call requires that '"+fun'+"' be shorter than '"+fun+"'", pos', 0)
            else
               PFailure(Error, "Parser did something unexpected, jump to position " + Printer.natToString(pos'), pos', 0)
          );
    if fun in underlying {
      assert {:only} FixMapSpecInner(fun, underlying.Keys, maxPos, callback, pos) by {
        assume && pos <= maxPos
                && forall fun': string <- underlying.Keys ::
                     FixMapSpecInnerInner(fun, fun', underlying.Keys, maxPos, callback, pos);
        assume false;
      }
      assert p == underlying[fun](callback, pos);
      assert FixpointMapSpecOnce(fun, underlying[fun], underlying.Keys, maxPos);
      var impl := underlying[fun];
      assert forall callback: ParserSelector<R>, u: nat |
      && FixMapSpecInner(fun, underlying.Keys, maxPos, callback, u)
      :: var x := impl(callback, u);
         && (x.PSuccess? ==> u + x.deltaPos <= maxPos);
      assert p.PSuccess? ==> pos + p.deltaPos <= maxPos;
    } else {
    }
  }

  ghost predicate OrSpec<R>(
    size: nat,
    left: Parser<R>,
    right: Parser<R>,
    pos: nat)
    // Verifies that the two parsers can both be applied at the given position
  {
    && left.requires(pos)
    && (left(pos).PSuccess? ==> pos <= left(pos).pos <= size)
    && right.requires(pos)
    && (right(pos).PSuccess? ==> pos <= right(pos).pos <= size)
    // Since requires are only used for progression, I don'result have a use case in which the following is useful
    /*&& var l := left(pos);
    && (l.PFailure? && l.level == Recoverable ==> right.requires(pos))*/
  }

  opaque function Or_<R>(
    ghost size: nat,
    left: Parser<R>,
    right: Parser<R>
  ) : (p: Parser<R>)
    // Builds a parser from left and right such that, if left fails and is recoverable, then right is used instead.
    ensures forall pos: nat | OrSpec(size, left, right, pos)
            :: p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
  {
    (pos: nat) requires OrSpec(size, left, right, pos)
    =>
      match left(pos)
      case PFailure(Recoverable, message, pos') => right(pos)
      case PFailure(Error, message, pos') => PFailure(Error, message, pos')
      case PSuccess(pos, l) => PSuccess(pos, l)
  }

  ghost predicate EitherPSpec<L, R>(size: nat, left: Parser<L>, right: Parser<R>, pos: nat) {
    && left.requires(pos)
    && (left(pos).PSuccess? ==> pos <= left(pos).pos <= size)
    && (left(pos).PFailure? && left(pos).level == Recoverable ==>
          right.requires(pos)
          && (right(pos).PSuccess? ==> pos <= right(pos).pos <= size))
  }

  opaque function EitherP_<L, R>(
    ghost size: nat,
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<Either<L, R>>)
    // Same as 'Or' but supports returning two heterogeneous values
    ensures forall pos: nat |
              EitherPSpec(size, left, right, pos)
            :: p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
  {
    (pos: nat)
     requires EitherPSpec(size, left, right, pos)
    =>
      match left(pos)
      case PFailure(Recoverable, message, pos') => right(pos).MapResult(r => Right(r))
      case PFailure(Error, message, pos') => PFailure(Error, message, pos')
      case PSuccess(pos, l) => PSuccess(pos, Left(l))
  }
}

module {:options "-functionSyntax:4", "-quantifierSyntax:4"} ParserTheorems {
  import opened Parsers
  // The remaining are interesting proofs about some equivalence but are not useful

  opaque function Map__<R, U>(ghost size: nat, underlying: Parser<R>, mappingFunc: R --> U)
    : (p: Parser<U>)
    // Map is equivalent to a bind method:
    ensures forall pos: nat | MapSpec(size, underlying, mappingFunc, pos)
            :: p.requires(pos)
  {
    var p := Bind__(size, underlying, (result: R, pos': nat) requires mappingFunc.requires(result) => Succeed_(size, mappingFunc(result)));
    assert forall pos: nat | MapSpec(size, underlying, mappingFunc, pos) ::
        p.requires(pos) by {
      forall pos: nat | MapSpec(size, underlying, mappingFunc, pos)
        ensures p.requires(pos)
      {
        AboutMap_(size, underlying, mappingFunc, pos);
        var left := underlying;
        var right := (result: R, pos': nat) requires mappingFunc.requires(result) => Succeed_(size, mappingFunc(result));
        assert BindSpec(size, left, right, pos);
      }
    }
    p
  }

  lemma Map_Map2<R, U>(size: nat, underlying: Parser<R>, mappingFunc: R --> U, pos: nat)
    requires MapSpec(size, underlying, mappingFunc, pos)
    ensures
      && Map__<R, U>(size, underlying, mappingFunc)(pos) == Map_<R, U>(size, underlying, mappingFunc)(pos)
  {
    reveal Map_();
    reveal Map__();
    reveal Bind__();
    reveal Succeed_();
  }

  opaque function Concat__<R, U>(ghost size: nat, left: Parser<R>, right: Parser<U>)
    : (p: Parser<(R, U)>)
    // Concat is equivalent to two binds methods
    ensures forall pos: nat | ConcatSpec_(size, left, right, pos)
            :: p.requires(pos)
  {
    Bind__(size, left, (result: R, pos': nat) requires right.requires(pos') =>
           Bind__(size, right, (u: U, pos'': nat) => Succeed_(size, (result, u))))
  }

  lemma Concat_Concat2<R, U>(size: nat, left: Parser<R>, right: Parser<U>, pos: nat)
    requires ConcatSpec_(size, left, right, pos)
    ensures BindSpec(size, left, (result: R, pos': nat) requires right.requires(pos') =>
                       Bind__(size, right, (u: U, pos'': nat) => Succeed_(size, (result, u))), pos)
    // TODO: Bug to report. Concat_() should not be needed
    ensures Concat_(size, left, right)(pos) == Concat__(size, left, right)(pos)
  {
    reveal Bind__();
    reveal Concat_();
    reveal Concat__();
    reveal Succeed_();
  }
}

// Nice DSL to build parsers
// B(p)       returns a parser builder from a normal parser.
// B1.o_I(B2) will parse both but return the result of B2
// B1.I_o(B2) will parse both but return the result of B1
// B.M(f)     will map the result of the parser builder by f if succeeded
// B1.O(B2)   will either parse B1, or B2 if B1 fails with Recoverable
// FirstOf([B1, B2, B3])
//            will parse with B1, but if B1 fails with Recoverable,
//            it will parse with B2, but if B2 fails with Recoverable,
//            it will parse with B3
// R(v)       returns a parser builder that returns immediately v
// 
// There are more parser builders in the trait Engine, when their spec depends on
// a predetermined input, e.g. to tests for constant strings

module {:options "-functionSyntax:4", "-quantifierSyntax:4"}  ParserBuilders {
  import opened Parsers
  //import opened ParserEngine

  // Wrap the constructor in a class where the size is constant so that users
  // don'result need to provide it.
  datatype ParserBuilder<R> = B_(ghost size: nat, apply: Parser<R>)
  {
    opaque function o_I<U>(other: ParserBuilder<U>): (p: ParserBuilder<U>)
      requires size == other.size
      ensures p.size == size
      ensures forall pos: nat |
                ConcatSpec_(size, apply, other.apply, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, ConcatR_(size, apply, other.apply))
    }
    opaque function I_o<U>(other: ParserBuilder<U>): (p: ParserBuilder<R>)
      requires size == other.size
      ensures p.size == size
      ensures forall pos: nat |
                ConcatSpec_(size, apply, other.apply, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, ConcatL_(size, apply, other.apply))
    }
    opaque function M<U>(mappingFunc: R --> U): (p: ParserBuilder<U>)
      ensures p.size == size
      ensures forall pos: nat |
                MapSpec(size, apply, mappingFunc, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, Map_(size, apply, mappingFunc))
    }
    opaque function O(other: ParserBuilder<R>): (p: ParserBuilder<R>)
      requires size == other.size
      ensures size == p.size
      ensures forall pos: nat |
                OrSpec(size, apply, other.apply, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, Or_(size, apply, other.apply))
    }

    opaque function Then<V>(other: (R, nat) --> ParserBuilder<V>): (p: ParserBuilder<V>)
      ensures size == p.size
      ensures forall pos: nat |
                       BindSpec(size, apply, (result: R, pos': nat) requires other.requires(result, pos') => other(result, pos').apply, pos)
                    :: p.apply.requires(pos)
                       && (
                        p.apply(pos).PSuccess? ==>
                          && apply(pos).PSuccess?
                          && apply(pos).pos <= p.apply(pos).pos <= size)
    {
      B_(size, Bind__(size, apply, (result: R, pos': nat) requires other.requires(result, pos') => other(result, pos').apply))
    }

    opaque function Repeat(init: R, combine: (R, R) -> R): (p: ParserBuilder<R>)
      ensures size == p.size
      ensures forall pos: nat | pos <= size && RepeatSpec(apply, pos, size-pos, size) ::
                p.apply.requires(pos)
                && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)

    {
      B_(size,
        (pos: nat)
          requires pos <= size
          requires RepeatSpec(apply, pos, size-pos, size)
          => RepeatAcc_(apply, pos, init, combine, size))
    }
  }
  opaque function FirstOf_<R>(ghost size: nat, others: seq<ParserBuilder<R>>): (p: ParserBuilder<R>)
    requires |others| > 0
    requires forall other <- others :: other.size == size
    ensures p.size == size
    ensures
      forall pos: nat |
        forall pp | pp in others :: pp.apply.requires(pos) && (pp.apply(pos).PSuccess? ==> pos <= pp.apply(pos).pos <= size)
      ::
        p.apply.requires(pos) && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
  {
    if |others| == 1 then others[0]
    else
      var p := others[0].O(FirstOf_(size, others[1..]));
      assert forall pos: nat |
              forall pp | pp in others :: pp.apply.requires(pos) && (pp.apply(pos).PSuccess? ==> pos <= pp.apply(pos).pos <= size)
             ::
               p.apply.requires(pos) && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size) by {
      }
      p
  }
  function R_<R>(ghost size: nat, result: R): (p: ParserBuilder<R>)
  {
    B_(size, Succeed_(size, result))
  }
  datatype FixMapParserBuilder<!R(!new)> = FixMapParserBuilder(ghost size: nat, ghost functions: set<string>, underlying: map<string, ParserMapper<R>> := map[])
  {
    static function Empty(ghost size: nat, ghost functions: set<string>): (b: FixMapParserBuilder<R>) ensures b.NonCrashing() {
      FixMapParserBuilder(size, functions, map[])
    }
    ghost predicate NonCrashing() {
      forall fun <- underlying :: FixpointMapSpecOnce(fun, underlying[fun], functions, size)
    }
    opaque function Add(name: string, mapper: ParserMapper<R>): (f: FixMapParserBuilder<R>)
      requires NonCrashing()
      requires name !in underlying
      requires FixpointMapSpecOnce(name, mapper, functions, size)
      ensures f.NonCrashing()
      ensures f.functions == functions
      ensures f.size == size
      ensures name in f.underlying
      ensures this.underlying.Keys + {name} == f.underlying.Keys
    {
      this.(underlying := underlying[name := mapper])
    }
  }
}

// Defines an "Engine" trait to be extended, which gives access to more
// parser combinators and parser builders that require access to an input string
module {:options "-functionSyntax:4", "-quantifierSyntax:4"}  ParserEngine {
  import opened ParserBuilders
  import opened Parsers
  import opened Wrappers
  import opened Printer

  // Engine defines the following parsers:
  // Succeed(v)       Always succeeds with the given value
  // Bind(l, r)       If l succeeds, returns the result of running r on the result
  // Epsilon          Always succeeds and returns ()
  // Map(p, f)        If p succeeds, maps its result with f
  // Concat(l, r)     if l and r succeed consecutively, pair their results
  // ConcatL(l, r)    if l and r succeed consecutively, returns the value of l
  // ConcatR(l, r)    if l and r succeed consecutively, returns the value of r
  // Or(l, r)         Returns the first of l or r which succeeds
  // EitherP(l, r)    Returns the first of l or r which succeeds, wrapped in Either type
  // Char('c')        fails with Error if 'c' is not at the given position.
  // Char?('c')       fails with Recoverable if 'c' is not at the given position.
  // Const("string")  fails with Error if "string" is not at the given position.
  // Const?("string") fails with Recoverable if "string" is not at the given position.
  // Rep(parser)      repeats the parser as much as possible and returns the sequence of results
  // Fix((result, pos) => parseResult)      returns a parser that recursively applies the provided function when needed
  // FixMap((result, pos) => parseResult)   Same as fix but can provide a mapping from string to functions instead of a single function
  // EOS              Succeeds if we reached the end of the string, fails with Error otherwise
  // FirstOf([p*])    returns the first parser which succeeds
  // Maybe(p)         If p succeeds, returns Some(p.result), otherwise returns None if p fails with Recoverable
  // DebugParser(msg, p) Prints the given message and pass through p
  //
  // Engine defines the following parser builders (please avoid them because they are not performant!)
  // C("string")  fails with Error if "string" is not at the given position.
  // C?("string") fails with Recoverable if "string" is not at the given position.
  // B(p)         wraps a regular parser
  // R(v)         A parser builder that returns the given value
  trait {:termination false} Engine {
    const input: string

    opaque function Succeed<R>(result: R): (p: Parser<R>)
      ensures forall pos: nat | pos <= |input| :: p.requires(pos) && p(pos).PSuccess? && pos == p(pos).pos <= |input|
      // A parser that does not consume any input and returns the given value
    {
      (pos: nat) requires pos <= |input| => PSuccess(pos, result)
    }

    opaque function Bind<L, R>(
      left: Parser<L>,
      right: (L, nat) --> Parser<R>
    ) : (p: Parser<R>)
      // A parser such that, if the left parser succeeds, then the right parser is obtained by using the result of the left parser
      ensures forall pos: nat | BindSpec(|input|, left, right, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==>
                      && left(pos).PSuccess?
                      && left(pos).pos <= p(pos).pos <= |input|
                      && p(pos) == right(left(pos).result, left(pos).pos)(left(pos).pos))
    {
      Bind__(|input|, left, right)
    }

    opaque function Epsilon(pos: nat): (pr: ParseResult<()>)
      requires pos <= |input|
      ensures pr.PSuccess? && pr.pos == pos
    {
      Epsilon_(|input|)(pos)
    }

    opaque function Map<R, U>(underlying: Parser<R>, mappingFunc: R --> U)
    : (p: Parser<U>)
    // A parser combinator that makes it possible to transform the result of a parser in another one
    // The mapping function can be partial
    ensures forall pos: nat | MapSpec(|input|, underlying, mappingFunc, pos)
            :: && p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      Map_(|input|, underlying, mappingFunc)
    }

    ghost predicate MapFailureSpec<R>(pos: nat, underlying: Parser<R>) {
      pos <= |input| && underlying.requires(pos) 
    }

    opaque function MapFailure<R(!new)>(underlying: Parser<R>, mappingFunc: ParseResult --> ParseResult)
    : (p: Parser<R>)
    requires forall p: ParseResult | p.PFailure? :: mappingFunc.requires(p) && mappingFunc(p).PFailure?
    requires forall pos: nat | pos <= |input| ::
        && underlying.requires(pos)
        && (underlying(pos).PSuccess? ==> pos <= underlying(pos).pos <= |input|)
    ensures forall pos: nat | MapFailureSpec(pos, underlying) ::
        && p.requires(pos)
        //&& (p(pos).PSuccess? <==> underlying(pos).PSuccess?)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat) requires pos <= |input| =>
        var r := underlying(pos);
        if r.PSuccess? then r else
        mappingFunc(r)
    }

    ghost predicate ConcatSpec<L, R>(left: Parser<L>, right: Parser<R>, pos: nat) {
      ConcatSpec_(|input|, left, right, pos)
    }

    opaque function Concat<L, R>(
      left: Parser<L>,
      right: Parser<R>
    ) : (p: Parser<(L, R)>)
      // Makes it possible to concatenate two consecutive parsers and return the pair of the results
      ensures forall pos: nat |
                ConcatSpec_(|input|, left, right, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      Concat_(|input|, left, right)
    }

    opaque function ConcatR<L, R>(
      left: Parser<L>,
      right: Parser<R>
    ) : (p: Parser<R>)
      // Makes it possible to concatenate two consecutive parsers and return the pair of the results
      ensures forall pos: nat |
                ConcatSpec_(|input|, left, right, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      ConcatR_(|input|, left, right)
    }

    opaque function ConcatL<L, R>(
      left: Parser<L>,
      right: Parser<R>
    ) : (p: Parser<L>)
      // Makes it possible to concatenate two consecutive parsers and return the pair of the results
      ensures forall pos: nat |
                ConcatSpec_(|input|, left, right, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      ConcatL_(|input|, left, right)
    }

    opaque function Or<R>(
      left: Parser<R>,
      right: Parser<R>
    ) : (p: Parser<R>)
      // Builds a parser from left and right such that, if left fails and is recoverable, then right is used instead.
      ensures forall pos: nat |
                OrSpec(|input|, left, right, pos)
                :: p.requires(pos)
                   && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      Or_(|input|, left, right)
    }

    opaque function EitherP<L, R>(
      left: Parser<L>,
      right: Parser<R>
    ) : (p: Parser<Either<L, R>>)
      // Same as 'Or' but supports returning two heterogeneous values
      ensures forall pos: nat |
                EitherPSpec(|input|, left, right, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      EitherP_(|input|, left, right)
    }

    opaque function Char(c: char): (p: Parser<char>)
      ensures forall pos: nat :: p.requires(pos)
      ensures forall pos: nat :: p(pos).PSuccess? ==>
                                   pos < |input| && p(pos).pos == pos + 1
    {
      (pos: nat) =>
        if pos < |input| && input[pos] == c then PSuccess(pos + 1, c)
        else PFailure(Error, "Expected '"+[c]+"'", pos)
    }

    opaque function Char?(c: char): (p: Parser<char>)
      ensures forall pos: nat :: p.requires(pos)
      ensures forall pos: nat :: p(pos).PSuccess? ==>
                                   pos < |input| && p(pos).pos == pos + 1
    {
      (pos: nat) =>
        if pos < |input| && input[pos] == c then PSuccess(pos + 1, c)
        else PFailure(Recoverable, "Expected a different char but that's ok", pos)
    }

    // Returns a function that tests if, at the given position, we can find the string toTest
    opaque function TestString(toTest: string): (test: nat --> bool)
      ensures forall pos: nat | pos <= |input| :: test.requires(pos)
    {
      (pos: nat) requires pos <= |input| => 
        pos + |toTest| <= |input| && input[pos..pos+|toTest|] == toTest
    }

    // Returns a function that tests if, at the given position, we can find the string toTest
    opaque function TestNotString(toTest: string): (test: nat --> bool)
      ensures forall pos: nat | pos <= |input| :: test.requires(pos)
    {
      (pos: nat) requires pos <= |input| => 
        !(pos + |toTest| <= |input| && input[pos..pos+|toTest|] == toTest)
    }

    opaque function CharTest?(test: nat --> bool): (p: Parser<char>)
      requires forall pos: nat | pos < |input| :: test.requires(pos)
      ensures forall pos: nat | pos <= |input| ::
        p.requires(pos) &&
        (p(pos).PSuccess? ==> pos < |input| && pos + 1 == p(pos).pos)
    {
      (pos: nat) requires pos <= |input| =>
        if pos < |input| && test(pos) then PSuccess(pos + 1, input[pos])
        else PFailure(Recoverable, "Expected a different char but that's ok", pos)
    }

    ghost predicate ConstSpec(expected: string, p: Parser<string>) {
      forall pos: nat ::
        && p.requires(pos)
        && (p(pos).PSuccess? ==>
              pos + |expected| <= |input| && p(pos).pos == pos + |expected|)
    }

    opaque function C(expected: string): (p: ParserBuilder<string>)
      ensures p.size == |input|
      ensures ConstSpec(expected, p.apply)
    {
      B_(|input|, Const(expected))
    }
    opaque function C?(expected: string): (p: ParserBuilder<string>)
      ensures p.size == |input|
      ensures ConstSpec(expected, p.apply)
    {
      B_(|input|, Const?(expected))
    }
    function B<R>(underlying: Parser<R>): (p: ParserBuilder<R>)
      ensures p.size == |input|
    {
      B_(|input|, underlying)
    }

    opaque function Const(expected: string): (p: Parser<string>)
      ensures ConstSpec(expected, p)
    {
      (pos: nat) =>
        if pos + |expected| <= |input| && input[pos..pos + |expected|] == expected then PSuccess(pos + |expected|, expected)
        else PFailure(Error, "Expected '"+expected+"'", pos)
    }

    opaque function Const?(expected: string): (p: Parser<string>)
      ensures ConstSpec(expected, p)
    {
      (pos: nat) =>
        if pos + |expected| <= |input| && input[pos..pos + |expected|] == expected then PSuccess(pos + |expected|, expected)
        else PFailure(Recoverable, "Possibly expecting something else but that's ok", pos)
    }

    opaque function Maybe<R>(underlying: Parser<R>): (p: Parser<Option<R>>)
      requires IsRegular(underlying)
      ensures IsRegular(p)
    {
      Or(Map(underlying, (result: R) => Some(result)), Succeed(None))
    }

    opaque function Newline(): (p: Parser<string>)
      ensures IsRegular(p)
    {
      Or(Const?("\r\n"), Or(Const?("\r"), Const("\n")))
    }

    opaque function Test?(test: (string, nat) --> bool): (p: Parser<()>)
      requires forall pos: nat | pos <= |input| :: test.requires(input, pos)
      ensures forall pos: nat | pos <= |input| ::
        p.requires(pos) &&
        (p(pos).PSuccess? ==> pos <= p(pos).pos)
    {
      (pos: nat) requires pos <= |input| =>
        if test(input, pos) then PSuccess(pos, ()) else PFailure(Recoverable, "Test failed", pos)
    }

    // Given a test on a position, returns a parser that succeeds with the longest string
    // starting at a given position which succeeds the test on every character
    // If the test succeeds immediately, returns a recoverable failure instead
    opaque function While?(test: nat --> bool): (p: Parser<string>)
      requires forall pos: nat | pos <= |input| :: test.requires(pos)
      ensures forall pos: nat | pos <= |input| :: p.requires(pos)
                  && (p(pos).PSuccess? ==> pos < p(pos).pos <= |input|)
    {
      var p := Bind(Rep(CharTest?(test)),
          (result: string, pos': nat) =>
            if result == "" then Fail_("Did not find an non-empty string satisfying test", Recoverable)
            else Succeed(result));
      assert forall pos: nat | pos <= |input| :: p.requires(pos)
                  && (p(pos).PSuccess? ==> pos < p(pos).pos <= |input|) by {
        forall pos : nat | pos <= |input| ensures  p.requires(pos)
                  && (p(pos).PSuccess? ==> pos < p(pos).pos <= |input|){
          assert  p.requires(pos);
          if(p(pos).PSuccess?) {
            RepDoesIncreasePosSometimes(CharTest?(test), pos);
          }
        }
      }
      p
    }

    opaque function EverythingUntilAndDrop(str: string): (p: Parser<string>)
      ensures forall pos: nat | pos <= |input| ::
        p.requires(pos)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      ConcatL(While?(TestNotString(str)), Const(str))
    }


    ghost predicate RepSpec<R>(underlying: Parser<R>, pos: nat) {
      && pos <= |input|
      && (forall pos' | pos <= pos' <= |input| ::
            && underlying.requires(pos')
            && (underlying(pos').PSuccess? ==> pos' <= underlying(pos').pos <= |input|))
    }

    opaque function Rep<R>(underlying: Parser<R>): (p: Parser<seq<R>>)
      ensures forall pos: nat | RepSpec(underlying, pos) ::
        p.requires(pos)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat)
       requires RepSpec(underlying, pos)
      =>
        Repeat0(underlying, pos, [], |input|)
    }

    lemma RepDoesIncreasePosSometimes<R>(underlying: Parser<R>, pos: nat)
      requires pos <= |input| && RepeatSpec(underlying, pos, |input|-pos, |input|)
      requires underlying.requires(pos) && underlying(pos).PSuccess? ==>
        pos < underlying(pos).pos
      ensures
        var p := Rep(underlying);
        (p(pos).PSuccess? && |p(pos).result| > 0 ==> pos < p(pos).pos)
    {
      reveal Rep();
      reveal Repeat0();
    }

    opaque function RepAcc<I, R>(
      underlying: Parser<R>,
      init: I,
      combine: (I, R) -> I
    ): (p: Parser<I>)
      ensures forall pos: nat | RepSpec(underlying, pos) ::
        && p.requires(pos)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat) requires RepSpec(underlying, pos) =>
        RepeatAcc_(underlying, pos, init, combine, |input|)
    }

    ghost predicate FixSpec<R(!new)>(size: nat, underlying: (Parser<R>, nat) --> ParseResult<R>, pos: nat) {
      && pos <= size
      && forall callback: Parser<R>, u: nat |
        FixSpecInner(size, callback, u) ::
        underlying.requires(callback, u)
        && (underlying(callback, u).PSuccess? ==> u <= underlying(callback, u).pos <= size)
    }
    function GetFixBase<R>(): map<string, ParserMapper<R>> { map[] }

    opaque function Fix<R(!new)>(underlying: (Parser<R>, nat) --> ParseResult<R>): (p: Parser<R>)
      ensures forall pos: nat| FixSpec(|input|, underlying, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat)
       requires FixSpec(|input|, underlying, pos)
      =>
        Fixpoint_<R>(
          |input|,
          underlying,
          pos
        )
    }
    // TODO: Dafny clinic. Cannot make it opaque, otherwise
    // even with reveal cannot verify other functions
    ghost predicate FixMapInnerOnce<R(!new)>(fun: string, impl: ParserMapper<R>, otherFuns: set<string>, size: nat)
    {
      FixpointMapSpecOnce(fun, impl, otherFuns, |input|)
    }

    ghost predicate FixMapInner<R(!new)>(size: nat, underlying: map<string, ParserMapper<R>>) {
      forall fun: string <- underlying.Keys ::
        FixMapInnerOnce(fun, underlying[fun], underlying.Keys, size)
    }

    opaque function FixMap<R(!new)>(
      underlying: map<string, ParserMapper<R>>,
      fun: string
    ): (p: Parser<R>)
      requires {:error "Second argument of FixMap might not be a key of the first"} fun in underlying.Keys
      requires {:error "First argument might not satisfy FixMapInner(|input|, arg). Said otherwise, key/value pairs of the first argument might not all satisfy FixMapInnerOnce(key, value, keys, |input|)"} FixMapInner(|input|, underlying)
      ensures forall pos: nat | pos <= |input| ::
                && p.requires(pos)
                && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat) requires pos <= |input| =>
        //reveal FixMapInnerOnce();
        FixpointMap_<R>(
          |input|,
          underlying,
          fun,
          pos
        )
    }
    opaque function FixMapBuilder<R(!new)>(ghost functions: set<string>): (r: FixMapParserBuilder<R>)
      ensures r.NonCrashing()
      ensures |r.underlying.Keys| == 0
      ensures r.functions == functions
      ensures r.size == |input|
    {
      var underlying: map<string, ParserMapper<R>> := map[];
      FixMapParserBuilder(|input|, functions, underlying)
    }

    const EOS: Parser<()> :=
      (pos: nat) => if pos >= |input| then PSuccess(pos, ()) else PFailure(Error, "Expected end of string", pos)
    
    opaque function FirstOf<R>(others: seq<ParserBuilder<R>>): (p: ParserBuilder<R>)
      requires |others| > 0
      requires forall other <- others :: other.size == |input|
      ensures
        forall pos: nat |
          forall pp <- others ::
            pp.apply.requires(pos) && (pp.apply(pos).PSuccess? ==> pos <= pp.apply(pos).pos <= |input|)
        ::
          p.apply.requires(pos) && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= |input|)
    {
      FirstOf_(|input|, others)
    }

    function R<R>(result: R): (p: ParserBuilder<R>)
    {
      B(Succeed(result))
    }

    const natToDigit: seq<char> := "0123456789"
    const digitToNat: map<char, DigitNat> := map i | 0 <= i < |natToDigit| :: natToDigit[i] := i

    opaque function Digit(test: bool := true): (p: Parser<nat>)
      ensures forall pos:nat | pos <= |input| ::
                && p.requires(pos)
                && (p(pos).PSuccess? ==>
                        && pos < |input|
                        && input[pos] in digitToNat
                        && digitToNat[input[pos]] == p(pos).result
                        && 0 <= p(pos).result <= 9
                        && p(pos).pos == pos + 1)
    {
      (pos: nat) requires pos <= |input| =>
        if pos == |input| then PFailure(if test then Recoverable else Error, "Expected a digit", pos) else
        if input[pos] in digitToNat then
          PSuccess(pos + 1, digitToNat[input[pos]])
        else PFailure(if test then Recoverable else Error, "Expected a digit", pos)
    }

    ghost predicate RecSpec<R(!new)>(fun: string, otherFuns: set<string>, rec: string --> Parser<R>, pos: nat)
    {
      FixMapSpecInner(fun, otherFuns, |input|, rec, pos)
    }

    ghost predicate RecSpecOnce<R(!new)>(fun: string, otherFuns: set<string>, mapper: ParserMapper<R>) {
      FixMapInnerOnce(fun, mapper, otherFuns, |input|)
    }

    // TODO: We have the ability to define another parser given the result of the first one,
    // but I'm missing the ability to call another parser builder with the result of the first one
    // to avoid callbacks.

    opaque function {:vcs_split_on_every_assert} Nat(test: bool := true): (p: Parser<nat>)
      ensures forall pos: nat | pos <= |input| ::
                && p.requires(pos)
                && (p(pos).PSuccess? ==> pos < p(pos).pos <= |input|)
    {
      var d? := Digit();
      Bind(d?, (firstdigit: DigitNat, pos: nat) =>
        RepAcc(d?, firstdigit,
          (previous, next) => previous*10 + next)
      )
    }

    opaque function {:vcs_split_on_every_assert} N(test: bool := true): (p: ParserBuilder<nat>)
      ensures p.size == |input| &&
              forall pos: nat | pos <= |input| ::
                && p.apply.requires(pos)
                && (p.apply(pos).PSuccess? ==> pos < p.apply(pos).pos <= |input|)
    {
      B(Nat(test))
    }

    opaque function Spaces?(): (r: Parser<string>)
      ensures forall pos: nat | pos <= |input| ::
        r.requires(pos)
        && (r(pos).PSuccess? ==> pos <= r(pos).pos <= |input|)
    {
      (pos: nat) requires pos <= |input| =>
        if pos < |input| && input[pos] in " \n\r\result" then
          PSuccess(pos+1, input[pos..pos+1])
        else
          PFailure(Recoverable, "Spaces", pos)
    }

    opaque function SkipSpaces<R>(p: Parser<R>): (r: Parser<R>)
      requires forall pos: nat | pos <= |input| ::
        p.requires(pos)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
      ensures forall pos: nat | pos <= |input| ::
        r.requires(pos)
        && (r(pos).PSuccess? ==> pos <= r(pos).pos <= |input|)
    {
      ConcatR(Spaces?(), p)
    }
    function LineContainingPos(pos: nat, p: nat := 0, lineNumber: nat := 0, charNumber: nat := 0, startLinePos: nat := 0): (result: (string, nat, nat))
      decreases |input| - p
      ensures 0 <= result.2 <= |input|
      requires 0 <= charNumber <= p
      requires startLinePos <= p <= |input|
    {
      if p >= |input| then
        assert charNumber <= |input|;
        (input[startLinePos..p], lineNumber, charNumber)
      else
      if input[p] == '\n' || p == |input| then
        if pos <= p then
          (input[startLinePos..p], lineNumber, charNumber)
        else
          LineContainingPos(pos, p + 1, lineNumber + 1, 0, p + 1)
      else
        LineContainingPos(pos, p + 1, lineNumber, if p <= pos then charNumber + 1 else charNumber, startLinePos)
    }

    ghost predicate IsRegular<R>(p: Parser<R>) {
      IsRegular_(p, |input|)
    }

    /*opaque function Regex(s: string): (r: Parser<string>)
      ensures forall pos: nat | pos <= |input| ::
        r.requires(pos)
        && (r(pos).PSuccess? ==> pos <= r(pos).pos <= |input|)
    {
      if s == "" then Epsilon
      else 
    } by method {

    }*/
    
    function FeedbackToString<R>(result: ParseResult<R>): string
      requires result.PFailure?
    {
      var (line, lineNumber, charNumber) := LineContainingPos(result.pos);
      result.message + " at position "+Printer.natToString(result.pos)+" line "+Printer.natToString(lineNumber)+", column "+Printer.natToString(charNumber)+":\n>"+
        line+"\n"+seq(charNumber, i => ' ')+"^\n"
    }
    method ReportError<R>(p: ParseResult<R>)
      requires p.PFailure?
    {
      var (line, lineNumber, charNumber) := LineContainingPos(p.pos);
      print "Parse error at position ",p.pos," line ",lineNumber,", column ",charNumber,":\n>",
        line, "\n", seq(charNumber, i => ' '), "^\n",
        p.message, "\n";
      return;
    }
    function Debug<R>(message: string, x: R): R {
      x
    } by method {
      print message, ":", x, "\n";
      return x;
    }
    
    function DebugParserFail<R>(msg: string): Parser<R> {
      (p: nat) => ParseResult.PFailure(Recoverable, "", Debug( 
        if p < |input| then msg + "'"+(
           if input[p] == '\r' then "\\r" else if input[p] == '\n' then "\\n" else input[p..p+1])
           + "' " + FeedbackToString<R>(PFailure(Recoverable, "", p)) + "\n" else
      msg, p))
    }

    opaque function DebugParser<R>(msg: string, other: Parser<R>): (p: Parser<R>)
      ensures IsRegular(other) ==> IsRegular(p)
    {
      var debugParser := DebugParserFail(msg+" (before)");
      var otherParserDebugged := (p: nat) requires other.requires(p) => Debug(msg+" (after)", other(p));
      Or(debugParser, otherParserDebugged)
    }
  }
  class EngineTest extends Engine {
    constructor() {
      this.input := "";
    }
  }
  type DigitNat = d: nat | 0 <= d <= 9
  */
}

abstract module ParserTests refines Parsers {
  lemma AboutSucceed_<R>(result: R, input: seq<C>)
    ensures
      var p := Succeed_(result);
      && p(input).PSuccess?
      && p(input).remaining == input
  { reveal Succeed_(); }

  lemma AboutFail_<R>(message: string, level: FailureLevel, input: seq<C>)
    ensures
      var p := Fail_<R>(message, level)(input);
      && p.PFailure?
      && p.message == message
      && p.level == level
      && p.remaining == input
  {
    reveal Fail_();
  }

  lemma AboutFail_2<R>(message: string, input: seq<C>)
    ensures
      var p := Fail_<R>(message)(input);
      && p.PFailure?
      && p.message == message
      && p.level == Recoverable
      && p.remaining == input
  {
    reveal Fail_();
  }

  lemma AboutBind_<L, R>(
    left: Parser<L>,
    right: (L, seq<C>) -> Parser<R>,
    input: seq<C>
  )
    ensures
      var p := Bind__(left, right)(input);
      && var leftResult := left(input);
      && !leftResult.IsFailure()
      ==> var leftValues := left(input).Extract();
      && var rightResult := right(leftValues.0, leftValues.1)(leftValues.1);
      && !rightResult.IsFailure()
      ==> && !p.IsFailure()
          && p.remaining == rightResult.remaining
          && p.result == rightResult.result 
  {
    reveal Bind__();
  }

  lemma AboutMap_<R, U>(underlying: Parser<R>, mappingFunc: R -> U, input: seq<C>)
    ensures var p := Map_(underlying, mappingFunc);
      && (underlying(input).PSuccess? <==> p(input).PSuccess?)
      && (p(input).PSuccess? ==>
            && p(input).remaining == underlying(input).remaining
            && p(input).result == mappingFunc(underlying(input).result))
  {
    reveal Map_();
    reveal Bind__();
    reveal Succeed_();
  }

  function BindMapCallback<R, U>(mappingFunc: R -> U):
     (R, seq<C>) -> Parser<U>
   {
    (result: R, remaining: seq<C>) => Succeed_(mappingFunc(result))
  }

  lemma AboutMap_Bind_<R, U>(underlying: Parser<R>, mappingFunc: R -> U, input: seq<C>)
    ensures Map_(underlying, mappingFunc)(input) 
        == Bind__<R, U>(underlying, BindMapCallback(mappingFunc))(input)
  {
    reveal Map_();
    reveal Bind__();
    reveal Succeed_();
  }

  lemma AboutConcat_<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures var p := Concat_(left, right);
            && (p(input).PSuccess? ==>
                && left(input).PSuccess?
                && p(input).result.0 == left(input).result
                && var input2 := left(input).remaining;
                && right(input2).PSuccess?
                && p(input).result.1 == right(input2).result
                && p(input).remaining == right(input2).remaining)
  {
    reveal Concat_();
  }

  function BindConcatCallback<L, R>(right: Parser<R>): (L, seq<C>) -> Parser<(L, R)>
  {
    (l: L, remaining: seq<C>) =>
      Map_(right, (r: R) => (l, r))
  }
  
  lemma AboutConcat_Bind_<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures Concat_(left, right)(input) == Bind__(left, BindConcatCallback(right))(input)
  {
    reveal Concat_();
    reveal Bind__();
    reveal Succeed_();
    reveal Map_();
  }

  lemma AboutConcatR_<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures var p := ConcatR_(left, right);
            && (p(input).PSuccess? ==>
                && left(input).PSuccess?
                && var input2 := left(input).remaining;
                && right(input2).PSuccess?
                && p(input).result == right(input2).result
                && p(input).remaining == right(input2).remaining)
  {
    reveal ConcatR_();
  }

  function first<L, R>(): ((L, R)) -> L {
    (lr: (L, R)) => lr.0
  }
  function second<L, R>(): ((L, R)) -> R {
    (lr: (L, R)) => lr.1
  }
  lemma AboutConcat_ConcatR_<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures Map_(Concat_(left, right), second())(input) == ConcatR_(left, right)(input)
  {
    reveal Concat_();
    reveal Succeed_();
    reveal ConcatR_();
    reveal Map_();
  }


  lemma AboutConcatL_<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures var p := ConcatL_(left, right);
            && (p(input).PSuccess? ==>
                && left(input).PSuccess?
                && var input2 := left(input).remaining;
                && right(input2).PSuccess?
                && p(input).result == left(input).result
                && p(input).remaining == right(input2).remaining)
  {
    reveal ConcatL_();
  }
  lemma AboutConcat_ConcatL_<L, R>(
    left: Parser<L>,
    right: Parser<R>,
    input: seq<C>)
    ensures Map_(Concat_(left, right), first())(input) == ConcatL_(left, right)(input)
  {
    reveal Concat_();
    reveal Succeed_();
    reveal ConcatL_();
    reveal Map_();
  }

  lemma AboutRepeat_<R>(
    underlying: Parser<R>,
    acc: seq<R>,
    input: seq<C>
  )
  // If underlying never throws a fatal error,
  // returns a remaining that is a suffix of the input,
  // then Repeat with always return a success
    decreases |input|
    requires NonCrashing(underlying)
    ensures Repeat_(underlying, acc, input).PSuccess?
  {
    reveal Repeat_(), NonCrashing();
    assert IsRemaining(input, input[0..]);
  }

  predicate AboutRepeatIncreasesPosIfUnderlyingSucceedsAtLeastOnceEnsures<R>(
    underlying: Parser<R>,
    acc: seq<R>,
    input: seq<C>
  )
  {
    var result := Repeat_(underlying, acc, input);
    && result.PSuccess?
    && |acc| <= |result.result|
    && (underlying(input).PSuccess? && |underlying(input).remaining| < |input|
    ==> 
    (|acc| < |result.result| && |result.remaining| < |input|))
  }

  lemma AboutRepeatIncreasesPosIfUnderlyingSucceedsAtLeastOnce<R>(
    underlying: Parser<R>,
    acc: seq<R>,
    input: seq<C>
  ) 
    decreases |input|
    requires NonCrashing(underlying)
    ensures 
      AboutRepeatIncreasesPosIfUnderlyingSucceedsAtLeastOnceEnsures
        (underlying, acc, input)
  {
    reveal Repeat_(), NonCrashing();
    var _ := input[0..];
    match underlying(input)
    case PSuccess(result, remaining) =>
      if |remaining| < |input| {
        AboutRepeatIncreasesPosIfUnderlyingSucceedsAtLeastOnce(underlying, acc + [result], remaining);
      }
    case _ =>
  }

  predicate AboutFixpoint_Ensures<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: seq<C>)
  {
    var p := Fixpoint_(underlying, input);
    p.PSuccess? ==> IsRemaining(input, p.remaining)
  }

  lemma AboutFixpoint_<R(!new)>(
    underlying: Parser<R> -> Parser<R>,
    input: seq<C>)
    requires
      forall callback: Parser<R>, u: seq<C>
        | underlying(callback)(u).PSuccess?
        :: IsRemaining(input, underlying(callback)(input).remaining)
    ensures AboutFixpoint_Ensures(underlying, input)
  {
    reveal Fixpoint_();
  }


  predicate AboutFixpointMap_Ensures<R(!new)>(
    underlying: map<string, RecursiveDef<R>>,
    fun: string,
    input: seq<C>
  ) {
    var p := FixpointMap_(underlying, fun, input);
    && (p.PSuccess? ==> IsRemaining(input, p.remaining))
  }

}