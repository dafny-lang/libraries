include "StringParsers.dfy"
include "ParsersBuilders.dfy"

module StringParsersBuilders refines ParserBuilders {
  import P = StringParsers
  export StringParsersBuilders extends ParserBuilders
    provides S, Int, WS, Except, ParseTest, Digit, DigitNumber, ParseTestCallback

  function S(s: string): B<string> {
    B(P.String(s))
  }
  function Int(): B<int> {
    B(P.Int())
  }
  function Digit(): B<char> {
    B(P.Digit())
  }
  function DigitNumber(): B<nat> {
    B(P.DigitNumber())
  }
  function WS(): B<string> {
    B(P.WS())
  }
  function Except(s: string): B<string> {
    B(P.ZeroOrMore(P.CharTest((c: char) => c !in s, s)))
  }
  method ParseTestCallback<T>(p: B<T>, input: string, printer: T -> string) {
    var result := p.apply(input);
    if result.Failure? {
      P.PrintFailure(input, result);
    } else {
      print printer(result.result), "\n";
    }
  }
  method ParseTest<T>(p: B<T>, input: string) {
    var result := p.apply(input);
    if result.Failure? {
      P.PrintFailure(input, result);
    } else {
      print result.result, "\n";
    }
  }
}