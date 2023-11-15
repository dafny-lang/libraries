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
  import P: Parsers
  export
    provides P
    provides O
    provides Ok
    provides Fail
    provides Rec
    provides B.e_I
    provides B.I_e
    provides B.I_I
    provides B.M
    provides B.Maybe
    provides B.Bind
    provides B.Rep
    provides End
    provides Any, Many
    reveals B
    reveals RecDef, FailureLevel, RecSel

  type FailureLevel = P.FailureLevel
  type RecSel<A> = string -> B<A>
  
  // Wrap the constructor in a class where the size is constant so that users
  // don'result need to provide it.
  datatype B<R> = B(apply: P.Parser<R>)
  {
    function Maybe(): B<P.Option<R>> {
      B(P.Maybe(apply))
    }
    function e_I<U>(other: B<U>): (p: B<U>)
      // Excludes the left, includes the right
    {
      B(P.ConcatR(apply, other.apply))
    }
    function I_e<U>(other: B<U>): (p: B<R>)
      // Includes the left, excludes the right
    {
      B(P.ConcatL(apply, other.apply))
    }
    function I_I<U>(other: B<U>): (p: B<(R, U)>)
      // Includes the left, excludes the right
    {
      B(P.Concat(apply, other.apply))
    }
    function M<U>(mappingFunc: R -> U): (p: B<U>)
      // Maps the result
    {
      B(P.Map(apply, mappingFunc))
    }
    function Bind<V>(other: R -> B<V>): (p: B<V>)
    {
      B(P.Bind(apply, (result: R) => other(result).apply))
    }

    function Rep<A>(init: A, combine: (A, R) -> A): (p: B<A>)
    {
      B(P.Rep(apply, combine, init))
    }
  }

  function Ok<R>(result: R): (p: B<R>)
  {
    B(P.Succeed(result))
  }

  function Fail<R>(message: string, level: FailureLevel := FailureLevel.Recoverable): (p: B<R>)
  {
    B(P.Fail(message, level))
  }

  function O<R>(alternatives: seq<B<R>>): B<R>
    // Declares a set of alternatives as a single list
  {
    if |alternatives| == 0 then Fail("no alternative") else
    if |alternatives| == 1 then alternatives[0]
    else
      B(P.Or(alternatives[0].apply, O(alternatives[1..]).apply))
  }

  function End(): B<()>
  {
    B(P.EndOfString())
  }

  function Any(test: P.C -> bool, name: string): B<P.C>
  {
    B(P.Any(test, name))
  }

  function Many(test: P.C -> bool, name: string): B<seq<P.C>>
  {
    B(P.Many(test, name))
  }

  
  datatype RecDef<!R> = RecDef(
    order: nat, 
    definition: RecSel<R> -> B<R>)
  
  opaque function Rec<R(!new)>(
    underlying: map<string, RecDef<R>>,
    fun: string): (p: B<R>)
  {
    B(P.RecursiveMap(
      map k <- underlying :: k :=
        P.RecursiveDef(
          underlying[k].order,
          (selector: P.ParserSelector<R>) =>
            underlying[k].definition(
              (name: string) =>
                B(selector(name))
            ).apply),
      fun
    ))
  }
}