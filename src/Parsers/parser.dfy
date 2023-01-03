include "library.dfy"

module {:options "-functionSyntax:4", "-quantifierSyntax:4"} Parsers {
  datatype Either<+L, +R> = Left(l: L) | Right(r: R)
  // Type to return when using the Or parser

  datatype FailureLevel = Error | Recoverable
  // PFailure level for parse results. An Error will be propagated to the top
  // while a Recoverable can be caught by a disjunctive pattern.
  // For example, if the parser Const?() fails, then it returns a Recoverable,
  // but the parser Const() will return an error.

  datatype ParseResult<+T> =
    // ParseResult is a failure-compatible type
    | PFailure(level: FailureLevel, message: string, pos: nat)
      // Returned in a parser failed
    | PSuccess(pos: nat, t: T)
      // Returns if a parser succeeds
  {
    predicate IsFailure() { PFailure? }
    function PropagateFailure<U>(): ParseResult<U> requires IsFailure() {
      match this
      case PFailure(level, message, position) => PFailure(level, message, position)
    }
    function Extract(): (nat, T) requires PSuccess? { (pos, t) }
    function MapResult<T'>(f: T -> T'): ParseResult<T'> {
      match this
      case PSuccess(n, t) => PSuccess(n, f(t))
      case PFailure(level, message, position) => PFailure(level, message, position)
    }
  }


  type Parser<+T> = nat --> ParseResult<T>
  // A parser is a function from a position to a parse result.
  // It might have preconditions

  // I wanted to use the following to make Parser a subset type
  // but this causes issues in verification, so I'm inlining this
  // condition wherever needed
  ghost predicate IsRegular_<T>(p: Parser<T>, size: nat) {
    forall pos: nat | pos <= size ::
      && p.requires(pos)
      && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
  }

  type ParserSelector<+T> = string --> Parser<T>
  // A parser selector is a function that, given a name that exists,
  // returns a parser associated to this name

  type ParserMapper<!T> = (ParserSelector<T>, nat) --> ParseResult<T>
  // A parser mapper is the building block of recursive parser. Given a parser selector and a position,
  // it returns a parsing result. So it's like a parser, but it can also invoke other parsers.

  // Parser combinators. The following functions make it possible to create and compose parsers

  function {:opaque} Succeed_<T>(ghost size: nat, t: T): (p: Parser<T>)
    ensures forall pos: nat | pos <= size :: p.requires(pos) && p(pos).PSuccess? && pos == p(pos).pos <= size
    // A parser that does not consume any input and returns the given value
  {
    (pos: nat) requires pos <= size => PSuccess(pos, t)
  }

  function {:opaque} Epsilon_(ghost size: nat): (p: Parser<()>)
    ensures forall pos: nat | pos <= size :: p.requires(pos) && p(pos).PSuccess? && pos == p(pos).pos
  { Succeed_(size, ()) }

  function Fail<T>(message: string, level: FailureLevel := Recoverable): Parser<T>
    // A parser that does not consume any input and returns the given failure
  {
    (pos: nat) => PFailure(level, message, pos)
  }

  ghost predicate BindSpec<L, R>(size: nat, left: Parser<L>, right: (L, nat) --> Parser<R>, pos: nat)
    // Encodes the fact that, at position "pos", left and right can be correctly concatenated
  {
    && left.requires(pos)
    && (left(pos).PSuccess? ==> pos <= left(pos).pos <= size)
    && (left(pos).PSuccess? ==>
          && right.requires(left(pos).t, left(pos).pos)
          && var right' := right(left(pos).t, left(pos).pos);
          && right'.requires(left(pos).pos)
          && (right'(left(pos).pos).PSuccess? ==> left(pos).pos <= right'(left(pos).pos).pos <= size)
          )
  }

  function {:opaque} Bind_<L, R>(
    ghost size: nat,
    left: Parser<L>,
    right: (L, nat) --> Parser<R>
  ) : (p: Parser<R>)
    // A parser such that, if the left parser succeeds, then the right parser is obtained by using the result of the left parser
    ensures forall pos: nat | BindSpec(size, left, right, pos)
            :: p.requires(pos)
               && (p(pos).PSuccess? ==>
                    && left(pos).PSuccess?
                    && left(pos).pos <= p(pos).pos <= size
                    && p(pos) == right(left(pos).t, left(pos).pos)(left(pos).pos))
  {
    (pos: nat)
     requires BindSpec(size, left, right, pos)
    =>
      var (pos, l) :- left(pos);
      var (pos, r) :- right(l, pos)(pos);
      PSuccess(pos, r)
  }

  ghost predicate MapSpec<T, U>(size: nat, underlying: Parser<T>, mappingFunc: T --> U, pos: nat)
    // Encodes the proposition that, if the underlying function successfully parses at position 'pos',
    // then the mapping function should succeed on the result of the parsing
  {
    && underlying.requires(pos)
    && (underlying(pos).PSuccess? ==> pos <= underlying(pos).pos <= size
                                            && mappingFunc.requires(underlying(pos).t))
  }

  function {:opaque} Map_<T, U>(ghost size: nat, underlying: Parser<T>, mappingFunc: T --> U)
    : (p: Parser<U>)
    // A parser combinator that makes it possible to transform the result of a parser in another one
    // The mapping function can be partial
    ensures forall pos: nat | MapSpec(size, underlying, mappingFunc, pos)
            :: && p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
  {
    (pos: nat) requires MapSpec(size, underlying, mappingFunc, pos)
    =>
      var (pos, t) :- underlying(pos);
      var u := mappingFunc(t);
      PSuccess(pos, u)
  }

  ghost predicate ConcatSpec_<L, R>(
    size: nat,
    left: Parser<L>,
    right: Parser<R>,
    pos: nat)
    // Encodes the proposition that, if the left parser succeeds on pos, then it should be possible to apply the
    // right parser after the left one.
  {
    && pos <= size
    && left.requires(pos)
    && (left(pos).PSuccess? ==>
          && pos <= left(pos).pos <= size
          && right.requires(left(pos).pos)
          && (right(left(pos).pos).PSuccess? ==>
              left(pos).pos <= right(left(pos).pos).pos <= size)
          )
  }

  function {:opaque} Concat_<L, R>(ghost size: nat,
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<(L, R)>)
    // Makes it possible to concatenate two consecutive parsers and return the pair of the results
    ensures forall pos: nat |
              ConcatSpec_(size, left, right, pos)
            :: p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
  {
    (pos: nat) requires ConcatSpec_(size, left, right, pos)
    =>
      var (pos, l) :- left(pos);
      var (pos, r) :- right(pos);
      PSuccess(pos, (l, r))
  }

  function {:opaque} ConcatR_<L, R>(
    ghost size: nat,
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<R>)
    // Same as Concat but only returns the second result
    ensures forall pos: nat |
              ConcatSpec_(size, left, right, pos)
            :: p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
  {
    (pos: nat)
     requires left.requires(pos)
     requires left(pos).PSuccess? ==> right.requires(left(pos).pos)
    =>
      var (pos, l) :- left(pos);
      var (pos, r) :- right(pos);
      PSuccess(pos, r)
  }

  function {:opaque} ConcatL_<L, R>(
    ghost size: nat,
    left: Parser<L>,
    right: Parser<R>
  ) : (p: Parser<L>)
    // Same as Concat but only returns the first result
    ensures forall pos: nat |
              ConcatSpec_(size, left, right, pos)
            :: p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
  {
    (pos: nat)
     requires left.requires(pos)
     requires left(pos).PSuccess? ==> right.requires(left(pos).pos)
    =>
      var (pos, l) :- left(pos);
      var (pos, r) :- right(pos);
      PSuccess(pos, l)
  }

  ghost predicate RepeatSpec<T>(underlying: Parser<T>, pos: nat, remaining: nat, size: nat)
    // Encodes the proposition that, for all position between pos and size included,
    // the underlying parser should be able to parse there, and if it succeeds, then
    // its output position should be greater than the original parsing position,
    // but bounded by size
  {
    && pos + remaining == size
    && (forall pos' | pos <= pos' <= size ::
          && underlying.requires(pos')
          && (underlying(pos').PSuccess? ==> pos' <= underlying(pos').pos <= size))
  }

  function {:opaque} Repeat_<T>(
    ghost remaining: nat,
    ghost size: nat,
    underlying: Parser<T>
  ): (p: Parser<seq<T>>)
    // Given a parser on a string of size 'size' and with 'remaining' characters to parse
    // (typically obtained by size - pos), returns a parser that can repeatedly parse the string
    // This parser returns a sequence of all possible parsers
    // If the underlying parser fails, then an empty sequence is returned
    ensures forall pos: nat | RepeatSpec(underlying, pos, remaining, size) ::
              && p.requires(pos)
              && (p(pos).PSuccess? ==> pos <= p(pos).pos <= size)
              && (p(pos).PFailure? ==> p(pos).level != Recoverable)
  {
    (pos: nat) requires RepeatSpec(underlying, pos, remaining, size) =>
      match underlying(pos)
      case PSuccess(pos', head) =>
        if pos' <= pos then PSuccess(pos', [head]) else
        match Repeat_(remaining-(pos'-pos), size, underlying)(pos') {
          case PSuccess(pos'', tail) =>
            PSuccess(pos'', [head] + tail)
          case PFailure(Error, message, pos'') =>
            PFailure(Error, message, pos')
        }
      case PFailure(Error, message, pos') =>
        PFailure(Error, message, pos')
      case PFailure(Recoverable, message, pos') =>
        PSuccess(pos, [])
  }

  function {:opaque} {:tailrecursion true} Repeat0<T>(
    underlying: Parser<T>,
    pos: nat,
    acc: seq<T>,
    ghost size: nat
  ): (p: ParseResult<seq<T>>)
  // Alternative version of Repeat that does not return a parser, but directly the ParseResult
    decreases size - pos
    requires pos <= size
    //requires forall pos: nat :: RepeatSpec(underlying, pos, remaining, size)
    requires RepeatSpec(underlying, pos, size-pos, size)
    ensures p.PFailure? ==> p.level != Recoverable
    ensures p.PSuccess? ==> pos <= p.pos <= size
  {
    match underlying(pos)
    case PSuccess(pos', head) =>
      if pos' <= pos then PSuccess(pos', acc + [head]) else
      Repeat0(underlying, pos', acc + [head], size)
    case PFailure(Error, message, pos') =>
      PFailure(Error, message, pos')
    case PFailure(Recoverable, message, pos') =>
      PSuccess(pos, acc)
  }

  lemma Repeat0DoesIncreasePosSometimes<T>(underlying: Parser<T>, pos: nat, size: nat)
    requires pos <= size
    requires RepeatSpec(underlying, pos, size-pos, size)
    requires underlying.requires(pos) && underlying(pos).PSuccess? && pos < underlying(pos).pos
    ensures 
      var result := Repeat0(underlying, pos, [], size);
      result.PSuccess? && 0 < |result.t| ==> pos < result.pos
  {
    reveal Repeat0();
  }


  function {:opaque} RepeatAcc_<I, T>(
    underlying: Parser<T>,
    pos: nat,
    init: I,
    combine: (I, T) -> I,
    ghost size: nat
  ): (p: ParseResult<I>)
  // Alternative version of Repeat that does not return a parser, but directly the ParseResult
    decreases size - pos
    requires pos <= size
    //requires forall pos: nat :: RepeatSpec(underlying, pos, remaining, size)
    requires RepeatSpec(underlying, pos, size-pos, size)
    ensures p.PFailure? ==> p.level != Recoverable
    ensures p.PSuccess? ==> pos <= p.pos <= size
  {
    match underlying(pos)
    case PSuccess(pos', head) =>
      if pos' <= pos then PSuccess(pos', combine(init, head)) else
      match RepeatAcc_(underlying, pos', combine(init, head), combine, size) {
        case PSuccess(pos'', tail) =>
          PSuccess(pos'', tail)
        case PFailure(Error, message, pos'') =>
          PFailure(Error, message, pos')
      }
    case PFailure(Error, message, pos') =>
      PFailure(Error, message, pos')
    case PFailure(Recoverable, message, pos') =>
      PSuccess(pos, init)
  }

  ghost predicate FixSpecInner<T(!new)>(size: nat, callback: Parser<T>, u: nat)
    // Specificaiton for Fixpoint. In other terms, verifies that the callback parser
    // accepts all positions between u (exclusive) and size (inclusive)
  {
    && u <= size
    && forall u': nat | u <  u' <= size ::
      callback.requires(u')
      && (callback(u').PSuccess? ==> u' <= callback(u').pos <= size)
  }

  function {:opaque} Fixpoint_<T(!new)>(
    ghost size: nat,
    underlying: (Parser<T>, nat) --> ParseResult<T>,
    pos: nat
  ): (p: ParseResult<T>)
    // Given a function that combines a (recursive) parser and a position to obtain a parse result,
    // returns the parse result associated to recursively applying the function.
    // If partially applied on "underlying" and "size", it would returns the solution to the equation:
    // f = pos => underlying(f, pos)
    decreases size - pos
    requires pos <= size
    requires
      forall callback: Parser<T>, u: nat | FixSpecInner(size, callback, u) ::
        && underlying.requires(callback, u)
        && (underlying(callback, u).PSuccess? ==> u <= underlying(callback, u).pos <= size)
    ensures p.PSuccess? ==> pos <= p.pos <= size
  {
    var callback: Parser<T> := (pos': nat) requires pos < pos' <= size =>
                                 Fixpoint_(size, underlying, pos');
    underlying(callback, pos)
  }

  ghost predicate FixMapSpecInner<T(!new)>(fun: string, functions: set<string>, size: nat, callback: string --> nat --> ParseResult<T>, u: nat)
    // Specification for FixpointMap.
    // Ensures that, for any other function, if this function is in the set of admissible `functions`,
    // then callback should not only accept it, but then accept any position at a second argument if
    // 1) This position is strictly greater than the current position u
    // 2) Or this position is the same but the function name is smaller.
  {
    && u <= size
    && forall fun': string <- functions ::
        && callback.requires(fun')
        && forall u': nat | u <  u' <= size || (u == u' && |fun'| < |fun|) ::
          callback(fun').requires(u')
          && var x := callback(fun')(u');
          && (x.PSuccess? ==> u' <= x.pos <= size)
  }

  ghost predicate FixpointMapSpecOnce<T(!new)>(fun': string, impl: ParserMapper<T>, otherFuns: set<string>, size: nat)
  {
    forall callback: ParserSelector<T>, u: nat |
      && FixMapSpecInner(fun', otherFuns, size, callback, u)
    :: impl.requires(callback, u)
       && var x := impl(callback, u);
       && (x.PSuccess? ==> u <= x.pos <= size)
  }

  function {:opaque} FixpointMap_<T(!new)>(
    ghost size: nat,
    underlying: map<string, (string --> Parser<T>, nat) --> ParseResult<T>>,
    fun: string,
    pos: nat
  ): (p: ParseResult<T>)
    // Given a function that combines a (recursive) parser selector and a position to obtain a parse result,
    // returns the parse result associated to recursively applying the function.
    // If partially applied on "underlying" and "fun", it would return the solution f<"fun"> to the equations:
    // f<name> = pos => underlying[fun](f, pos)
    decreases size - pos, |fun|
    requires pos <= size
    requires
      && fun in underlying.Keys
      && forall fun': string  <- underlying.Keys ::
           FixpointMapSpecOnce(fun', underlying[fun'], underlying.Keys, size)
    ensures p.PSuccess? ==> pos <= p.pos <= size
  {
    var callback: string --> nat --> ParseResult<T>
      :=  (fun': string) requires fun' in underlying.Keys =>
        (pos': nat) requires pos < pos' <= size || (pos' == pos && |fun'| < |fun|) =>
           FixpointMap_(size, underlying, fun', pos');
    underlying[fun](callback, pos)
  }

  ghost predicate OrSpec<T>(
    size: nat,
    left: Parser<T>,
    right: Parser<T>,
    pos: nat)
    // Verifies that the two parsers can both be applied at the given position
  {
    && left.requires(pos)
    && (left(pos).PSuccess? ==> pos <= left(pos).pos <= size)
    && right.requires(pos)
    && (right(pos).PSuccess? ==> pos <= right(pos).pos <= size)
    // Since requires are only used for progression, I don't have a use case in which the following is useful
    /*&& var l := left(pos);
    && (l.PFailure? && l.level == Recoverable ==> right.requires(pos))*/
  }

  function {:opaque} Or_<T>(
    ghost size: nat,
    left: Parser<T>,
    right: Parser<T>
  ) : (p: Parser<T>)
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

  function {:opaque} EitherP_<L, R>(
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

  function {:opaque} Map__<T, U>(ghost size: nat, underlying: Parser<T>, mappingFunc: T --> U)
    : (p: Parser<U>)
    // Map is equivalent to a bind method:
    ensures forall pos: nat | MapSpec(size, underlying, mappingFunc, pos)
            :: p.requires(pos)
  {
    var p := Bind_(size, underlying, (t: T, pos': nat) requires mappingFunc.requires(t) => Succeed_(size, mappingFunc(t)));
    assert forall pos: nat | MapSpec(size, underlying, mappingFunc, pos) ::
        p.requires(pos) by {
      forall pos: nat | MapSpec(size, underlying, mappingFunc, pos)
        ensures p.requires(pos)
      {
        var left := underlying;
        var right := (t: T, pos': nat) requires mappingFunc.requires(t) => Succeed_(size, mappingFunc(t));
        assert BindSpec(size, left, right, pos);
      }
    }
    p
  }

  lemma Map_Map2<T, U>(size: nat, underlying: Parser<T>, mappingFunc: T --> U, pos: nat)
    requires MapSpec(size, underlying, mappingFunc, pos)
    ensures
      && Map__<T, U>(size, underlying, mappingFunc)(pos) == Map_<T, U>(size, underlying, mappingFunc)(pos)
  {
    reveal Map_();
    reveal Map__();
    reveal Bind_();
  }

  function {:opaque} Concat__<T, U>(ghost size: nat, left: Parser<T>, right: Parser<U>)
    : (p: Parser<(T, U)>)
    // Concat is equivalent to two binds methods
    ensures forall pos: nat | ConcatSpec_(size, left, right, pos)
            :: p.requires(pos)
  {
    Bind_(size, left, (t: T, pos': nat) requires right.requires(pos') =>
           Bind_(size, right, (u: U, pos'': nat) => Succeed_(size, (t, u))))
  }

  lemma Concat_Concat2<T, U>(size: nat, left: Parser<T>, right: Parser<U>, pos: nat)
    requires ConcatSpec_(size, left, right, pos)
    ensures BindSpec(size, left, (t: T, pos': nat) requires right.requires(pos') =>
                       Bind_(size, right, (u: U, pos'': nat) => Succeed_(size, (t, u))), pos)
    // TODO: Bug to report. Concat_() should not be needed
    ensures Concat_(size, left, right)(pos) == Concat__(size, left, right)(pos)
  {
    reveal Bind_();
    reveal Concat_();
    reveal Concat__();
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
  // don't need to provide it.
  datatype ParserBuilder<T> = B_(ghost size: nat, apply: Parser<T>)
  {
    function {:opaque} o_I<U>(other: ParserBuilder<U>): (p: ParserBuilder<U>)
      requires size == other.size
      ensures p.size == size
      ensures forall pos: nat |
                ConcatSpec_(size, apply, other.apply, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, ConcatR_(size, apply, other.apply))
    }
    function {:opaque} I_o<U>(other: ParserBuilder<U>): (p: ParserBuilder<T>)
      requires size == other.size
      ensures p.size == size
      ensures forall pos: nat |
                ConcatSpec_(size, apply, other.apply, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, ConcatL_(size, apply, other.apply))
    }
    function {:opaque} M<U>(mappingFunc: T --> U): (p: ParserBuilder<U>)
      ensures p.size == size
      ensures forall pos: nat |
                MapSpec(size, apply, mappingFunc, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, Map_(size, apply, mappingFunc))
    }
    function {:opaque} O(other: ParserBuilder<T>): (p: ParserBuilder<T>)
      requires size == other.size
      ensures size == p.size
      ensures forall pos: nat |
                OrSpec(size, apply, other.apply, pos)
              :: p.apply.requires(pos)
                 && (p.apply(pos).PSuccess? ==> pos <= p.apply(pos).pos <= size)
    {
      B_(size, Or_(size, apply, other.apply))
    }

    function {:opaque} Then<V>(other: (T, nat) --> ParserBuilder<V>): (p: ParserBuilder<V>)
      ensures size == p.size
      ensures forall pos: nat |
                       BindSpec(size, apply, (t: T, pos': nat) requires other.requires(t, pos') => other(t, pos').apply, pos)
                    :: p.apply.requires(pos)
                       && (
                        p.apply(pos).PSuccess? ==>
                          && apply(pos).PSuccess?
                          && apply(pos).pos <= p.apply(pos).pos <= size)
    {
      B_(size, Bind_(size, apply, (t: T, pos': nat) requires other.requires(t, pos') => other(t, pos').apply))
    }

    function {:opaque} Repeat(init: T, combine: (T, T) -> T): (p: ParserBuilder<T>)
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
  function {:opaque} FirstOf_<T>(ghost size: nat, others: seq<ParserBuilder<T>>): (p: ParserBuilder<T>)
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
  function R_<T>(ghost size: nat, t: T): (p: ParserBuilder<T>)
  {
    B_(size, Succeed_(size, t))
  }
  datatype FixMapParserBuilder<!T(!new)> = FixMapParserBuilder(ghost size: nat, ghost functions: set<string>, underlying: map<string, ParserMapper<T>> := map[])
  {
    static function Empty(ghost size: nat, ghost functions: set<string>): (b: FixMapParserBuilder<T>) ensures b.Valid() {
      FixMapParserBuilder(size, functions, map[])
    }
    ghost predicate Valid() {
      forall fun <- underlying :: FixpointMapSpecOnce(fun, underlying[fun], functions, size)
    }
    function {:opaque} Add(name: string, mapper: ParserMapper<T>): (f: FixMapParserBuilder<T>)
      requires Valid()
      requires name !in underlying
      requires FixpointMapSpecOnce(name, mapper, functions, size)
      ensures f.Valid()
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
  import opened Library
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

    function {:opaque} Succeed<T>(t: T): (p: Parser<T>)
      ensures forall pos: nat | pos <= |input| :: p.requires(pos) && p(pos).PSuccess? && pos == p(pos).pos <= |input|
      // A parser that does not consume any input and returns the given value
    {
      (pos: nat) requires pos <= |input| => PSuccess(pos, t)
    }

    function {:opaque} Bind<L, R>(
      left: Parser<L>,
      right: (L, nat) --> Parser<R>
    ) : (p: Parser<R>)
      // A parser such that, if the left parser succeeds, then the right parser is obtained by using the result of the left parser
      ensures forall pos: nat | BindSpec(|input|, left, right, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==>
                      && left(pos).PSuccess?
                      && left(pos).pos <= p(pos).pos <= |input|
                      && p(pos) == right(left(pos).t, left(pos).pos)(left(pos).pos))
    {
      Bind_(|input|, left, right)
    }

    function {:opaque} Epsilon(pos: nat): (pr: ParseResult<()>)
      requires pos <= |input|
      ensures pr.PSuccess? && pr.pos == pos
    {
      Epsilon_(|input|)(pos)
    }

    function {:opaque} Map<T, U>(underlying: Parser<T>, mappingFunc: T --> U)
    : (p: Parser<U>)
    // A parser combinator that makes it possible to transform the result of a parser in another one
    // The mapping function can be partial
    ensures forall pos: nat | MapSpec(|input|, underlying, mappingFunc, pos)
            :: && p.requires(pos)
               && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      Map_(|input|, underlying, mappingFunc)
    }

    ghost predicate MapFailureSpec<T>(pos: nat, underlying: Parser<T>) {
      pos <= |input| && underlying.requires(pos) 
    }

    function {:opaque} MapFailure<T(!new)>(underlying: Parser<T>, mappingFunc: ParseResult --> ParseResult)
    : (p: Parser<T>)
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

    function {:opaque} Concat<L, R>(
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

    function {:opaque} ConcatR<L, R>(
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

    function {:opaque} ConcatL<L, R>(
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

    function {:opaque} Or<T>(
      left: Parser<T>,
      right: Parser<T>
    ) : (p: Parser<T>)
      // Builds a parser from left and right such that, if left fails and is recoverable, then right is used instead.
      ensures forall pos: nat |
                OrSpec(|input|, left, right, pos)
                :: p.requires(pos)
                   && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      Or_(|input|, left, right)
    }

    function {:opaque} EitherP<L, R>(
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

    function {:opaque} Char(c: char): (p: Parser<char>)
      ensures forall pos: nat :: p.requires(pos)
      ensures forall pos: nat :: p(pos).PSuccess? ==>
                                   pos < |input| && p(pos).pos == pos + 1
    {
      (pos: nat) =>
        if pos < |input| && input[pos] == c then PSuccess(pos + 1, c)
        else PFailure(Error, "Expected '"+[c]+"'", pos)
    }

    function {:opaque} Char?(c: char): (p: Parser<char>)
      ensures forall pos: nat :: p.requires(pos)
      ensures forall pos: nat :: p(pos).PSuccess? ==>
                                   pos < |input| && p(pos).pos == pos + 1
    {
      (pos: nat) =>
        if pos < |input| && input[pos] == c then PSuccess(pos + 1, c)
        else PFailure(Recoverable, "Expected a different char but that's ok", pos)
    }

    // Returns a function that tests if, at the given position, we can find the string toTest
    function {:opaque} TestString(toTest: string): (test: nat --> bool)
      ensures forall pos: nat | pos <= |input| :: test.requires(pos)
    {
      (pos: nat) requires pos <= |input| => 
        pos + |toTest| <= |input| && input[pos..pos+|toTest|] == toTest
    }

    // Returns a function that tests if, at the given position, we can find the string toTest
    function {:opaque} TestNotString(toTest: string): (test: nat --> bool)
      ensures forall pos: nat | pos <= |input| :: test.requires(pos)
    {
      (pos: nat) requires pos <= |input| => 
        !(pos + |toTest| <= |input| && input[pos..pos+|toTest|] == toTest)
    }

    function {:opaque} CharTest?(test: nat --> bool): (p: Parser<char>)
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

    function {:opaque} C(expected: string): (p: ParserBuilder<string>)
      ensures p.size == |input|
      ensures ConstSpec(expected, p.apply)
    {
      B_(|input|, Const(expected))
    }
    function {:opaque} C?(expected: string): (p: ParserBuilder<string>)
      ensures p.size == |input|
      ensures ConstSpec(expected, p.apply)
    {
      B_(|input|, Const?(expected))
    }
    function B<T>(underlying: Parser<T>): (p: ParserBuilder<T>)
      ensures p.size == |input|
    {
      B_(|input|, underlying)
    }

    function {:opaque} Const(expected: string): (p: Parser<string>)
      ensures ConstSpec(expected, p)
    {
      (pos: nat) =>
        if pos + |expected| <= |input| && input[pos..pos + |expected|] == expected then PSuccess(pos + |expected|, expected)
        else PFailure(Error, "Expected '"+expected+"'", pos)
    }

    function {:opaque} Const?(expected: string): (p: Parser<string>)
      ensures ConstSpec(expected, p)
    {
      (pos: nat) =>
        if pos + |expected| <= |input| && input[pos..pos + |expected|] == expected then PSuccess(pos + |expected|, expected)
        else PFailure(Recoverable, "Possibly expecting something else but that's ok", pos)
    }

    function {:opaque} Maybe<T>(underlying: Parser<T>): (p: Parser<Option<T>>)
      requires IsRegular(underlying)
      ensures IsRegular(p)
    {
      Or(Map(underlying, (t: T) => Some(t)), Succeed(None))
    }

    function {:opaque} Newline(): (p: Parser<string>)
      ensures IsRegular(p)
    {
      Or(Const?("\r\n"), Or(Const?("\r"), Const("\n")))
    }

    function {:opaque} Test?(test: (string, nat) --> bool): (p: Parser<()>)
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
    function {:opaque} While?(test: nat --> bool): (p: Parser<string>)
      requires forall pos: nat | pos <= |input| :: test.requires(pos)
      ensures forall pos: nat | pos <= |input| :: p.requires(pos)
                  && (p(pos).PSuccess? ==> pos < p(pos).pos <= |input|)
    {
      var p := Bind(Rep(CharTest?(test)),
          (result: string, pos': nat) =>
            if result == "" then Fail("Did not find an non-empty string satisfying test", Recoverable)
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

    function {:opaque} EverythingUntilAndDrop(str: string): (p: Parser<string>)
      ensures forall pos: nat | pos <= |input| ::
        p.requires(pos)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      ConcatL(While?(TestNotString(str)), Const(str))
    }


    ghost predicate RepSpec<T>(underlying: Parser<T>, pos: nat) {
      && pos <= |input|
      && (forall pos' | pos <= pos' <= |input| ::
            && underlying.requires(pos')
            && (underlying(pos').PSuccess? ==> pos' <= underlying(pos').pos <= |input|))
    }

    function {:opaque} Rep<T>(underlying: Parser<T>): (p: Parser<seq<T>>)
      ensures forall pos: nat | RepSpec(underlying, pos) ::
        p.requires(pos)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat)
       requires RepSpec(underlying, pos)
      =>
        Repeat0(underlying, pos, [], |input|)
    }

    lemma RepDoesIncreasePosSometimes<T>(underlying: Parser<T>, pos: nat)
      requires pos <= |input| && RepeatSpec(underlying, pos, |input|-pos, |input|)
      requires underlying.requires(pos) && underlying(pos).PSuccess? ==>
        pos < underlying(pos).pos
      ensures
        var p := Rep(underlying);
        (p(pos).PSuccess? && |p(pos).t| > 0 ==> pos < p(pos).pos)
    {
      reveal Rep();
      reveal Repeat0();
    }

    function {:opaque} RepAcc<I, T>(
      underlying: Parser<T>,
      init: I,
      combine: (I, T) -> I
    ): (p: Parser<I>)
      ensures forall pos: nat | RepSpec(underlying, pos) ::
        && p.requires(pos)
        && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat) requires RepSpec(underlying, pos) =>
        RepeatAcc_(underlying, pos, init, combine, |input|)
    }

    ghost predicate FixSpec<T(!new)>(size: nat, underlying: (Parser<T>, nat) --> ParseResult<T>, pos: nat) {
      && pos <= size
      && forall callback: Parser<T>, u: nat |
        FixSpecInner(size, callback, u) ::
        underlying.requires(callback, u)
        && (underlying(callback, u).PSuccess? ==> u <= underlying(callback, u).pos <= size)
    }
    function GetFixBase<T>(): map<string, ParserMapper<T>> { map[] }

    function {:opaque} Fix<T(!new)>(underlying: (Parser<T>, nat) --> ParseResult<T>): (p: Parser<T>)
      ensures forall pos: nat| FixSpec(|input|, underlying, pos)
              :: p.requires(pos)
                 && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat)
       requires FixSpec(|input|, underlying, pos)
      =>
        Fixpoint_<T>(
          |input|,
          underlying,
          pos
        )
    }
    // TODO: Dafny clinic. Cannot make it opaque, otherwise
    // even with reveal cannot verify other functions
    ghost predicate FixMapInnerOnce<T(!new)>(fun: string, impl: ParserMapper<T>, otherFuns: set<string>, size: nat)
    {
      FixpointMapSpecOnce(fun, impl, otherFuns, |input|)
    }

    ghost predicate FixMapInner<T(!new)>(size: nat, underlying: map<string, ParserMapper<T>>) {
      forall fun: string <- underlying.Keys ::
        FixMapInnerOnce(fun, underlying[fun], underlying.Keys, size)
    }

    function {:opaque} FixMap<T(!new)>(
      underlying: map<string, ParserMapper<T>>,
      fun: string
    ): (p: Parser<T>)
      requires {:error "Second argument of FixMap might not be a key of the first"} fun in underlying.Keys
      requires {:error "First argument might not satisfy FixMapInner(|input|, arg). Said otherwise, key/value pairs of the first argument might not all satisfy FixMapInnerOnce(key, value, keys, |input|)"} FixMapInner(|input|, underlying)
      ensures forall pos: nat | pos <= |input| ::
                && p.requires(pos)
                && (p(pos).PSuccess? ==> pos <= p(pos).pos <= |input|)
    {
      (pos: nat) requires pos <= |input| =>
        //reveal FixMapInnerOnce();
        FixpointMap_<T>(
          |input|,
          underlying,
          fun,
          pos
        )
    }
    function {:opaque} FixMapBuilder<T>(ghost functions: set<string>): (r: FixMapParserBuilder<T>)
      ensures r.Valid()
      ensures |r.underlying.Keys| == 0
      ensures r.functions == functions
      ensures r.size == |input|
    {
      var underlying: map<string, ParserMapper<T>> := map[];
      FixMapParserBuilder(|input|, functions, underlying)
    }

    const EOS: Parser<()> :=
      (pos: nat) => if pos >= |input| then PSuccess(pos, ()) else PFailure(Error, "Expected end of string", pos)
    
    function {:opaque} FirstOf<T>(others: seq<ParserBuilder<T>>): (p: ParserBuilder<T>)
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

    function R<T>(t: T): (p: ParserBuilder<T>)
    {
      B(Succeed(t))
    }

    const natToDigit: seq<char> := "0123456789"
    const digitToNat: map<char, DigitNat> := map i | 0 <= i < |natToDigit| :: natToDigit[i] := i

    function {:opaque} Digit(test: bool := true): (p: Parser<nat>)
      ensures forall pos:nat | pos <= |input| ::
                && p.requires(pos)
                && (p(pos).PSuccess? ==>
                        && pos < |input|
                        && input[pos] in digitToNat
                        && digitToNat[input[pos]] == p(pos).t
                        && 0 <= p(pos).t <= 9
                        && p(pos).pos == pos + 1)
    {
      (pos: nat) requires pos <= |input| =>
        if pos == |input| then PFailure(if test then Recoverable else Error, "Expected a digit", pos) else
        if input[pos] in digitToNat then
          PSuccess(pos + 1, digitToNat[input[pos]])
        else PFailure(if test then Recoverable else Error, "Expected a digit", pos)
    }

    ghost predicate RecSpec<T(!new)>(fun: string, otherFuns: set<string>, rec: string --> Parser<T>, pos: nat)
    {
      FixMapSpecInner(fun, otherFuns, |input|, rec, pos)
    }

    ghost predicate RecSpecOnce<T(!new)>(fun: string, otherFuns: set<string>, mapper: ParserMapper<T>) {
      FixMapInnerOnce(fun, mapper, otherFuns, |input|)
    }

    // TODO: We have the ability to define another parser given the result of the first one,
    // but I'm missing the ability to call another parser builder with the result of the first one
    // to avoid callbacks.

    function {:opaque} {:vcs_split_on_every_assert} Nat(test: bool := true): (p: Parser<nat>)
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

    function {:opaque} {:vcs_split_on_every_assert} N(test: bool := true): (p: ParserBuilder<nat>)
      ensures p.size == |input| &&
              forall pos: nat | pos <= |input| ::
                && p.apply.requires(pos)
                && (p.apply(pos).PSuccess? ==> pos < p.apply(pos).pos <= |input|)
    {
      B(Nat(test))
    }

    function {:opaque} Spaces?(): (r: Parser<string>)
      ensures forall pos: nat | pos <= |input| ::
        r.requires(pos)
        && (r(pos).PSuccess? ==> pos <= r(pos).pos <= |input|)
    {
      (pos: nat) requires pos <= |input| =>
        if pos < |input| && input[pos] in " \n\r\t" then
          PSuccess(pos+1, input[pos..pos+1])
        else
          PFailure(Recoverable, "Spaces", pos)
    }

    function {:opaque} SkipSpaces<T>(p: Parser<T>): (r: Parser<T>)
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

    ghost predicate IsRegular<T>(p: Parser<T>) {
      IsRegular_(p, |input|)
    }

    /*function {:opaque} Regex(s: string): (r: Parser<string>)
      ensures forall pos: nat | pos <= |input| ::
        r.requires(pos)
        && (r(pos).PSuccess? ==> pos <= r(pos).pos <= |input|)
    {
      if s == "" then Epsilon
      else 
    } by method {

    }*/
    
    function FeedbackToString<T>(result: ParseResult<T>): string
      requires result.PFailure?
    {
      var (line, lineNumber, charNumber) := LineContainingPos(result.pos);
      result.message + " at position "+Printer.natToString(result.pos)+" line "+Printer.natToString(lineNumber)+", column "+Printer.natToString(charNumber)+":\n>"+
        line+"\n"+seq(charNumber, i => ' ')+"^\n"
    }
    method ReportError<T>(p: ParseResult<T>)
      requires p.PFailure?
    {
      var (line, lineNumber, charNumber) := LineContainingPos(p.pos);
      print "Parse error at position ",p.pos," line ",lineNumber,", column ",charNumber,":\n>",
        line, "\n", seq(charNumber, i => ' '), "^\n",
        p.message, "\n";
      return;
    }
    function Debug<T>(message: string, x: T): T {
      x
    } by method {
      print message, ":", x, "\n";
      return x;
    }
    
    function DebugParserFail<T>(msg: string): Parser<T> {
      (p: nat) => ParseResult.PFailure(Recoverable, "", Debug( 
        if p < |input| then msg + "'"+(
           if input[p] == '\r' then "\\r" else if input[p] == '\n' then "\\n" else input[p..p+1])
           + "' " + FeedbackToString<T>(PFailure(Recoverable, "", p)) + "\n" else
      msg, p))
    }

    function {:opaque} DebugParser<T>(msg: string, other: Parser<T>): (p: Parser<T>)
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
}