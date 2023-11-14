include "parsers.dfy"

// Nice wanna-to-be DSL to build parsers to avoid too much parenthesis nesting
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

abstract module ParserBuilders {
  import Parsers

  type Parser<A> = Parsers.Parser<A>
  type FailureLevel = Parsers.FailureLevel
  
  // Wrap the constructor in a class where the size is constant so that users
  // don'result need to provide it.
  datatype B<R> = B(apply: Parser<R>)
  {
    opaque function e_I<U>(other: B<U>): (p: B<U>)
      // Excludes the left, includes the right
    {
      B(Parsers.ConcatR(apply, other.apply))
    }
    opaque function I_o<U>(other: B<U>): (p: B<R>)
      // Includes the left, excludes the right
    {
      B(Parsers.ConcatL(apply, other.apply))
    }
    opaque function M<U>(mappingFunc: R -> U): (p: B<U>)
      // Maps the result
    {
      B(Parsers.Map(apply, mappingFunc))
    }
    static function BS<R>(result: R): (p: B<R>)
    {
      B(Parsers.Succeed(result))
    }

    static function BF<R>(message: string, level: FailureLevel := FailureLevel.Recoverable): (p: B<R>)
    {
      B(Parsers.Fail(message, level))
    }

    static function O(alternatives: seq<B<R>>): B<R>
      // Declares a set of alternatives as a single list
    {
      if |alternatives| == 0 then BF("no alternative") else
      if |alternatives| == 1 then alternatives[0]
      else
        B(Parsers.Or(alternatives[0].apply, O(alternatives[1..]).apply))
    }

    opaque function Then<V>(other: R -> B<V>): (p: B<V>)
    {
      B(Parsers.Bind(apply, (result: R) => other(result).apply))
    }

    opaque function Rep(init: R, combine: (R, R) -> R): (p: B<R>)
    {
      B(Parsers.Rep(apply, combine, init))
    }
  }
}
