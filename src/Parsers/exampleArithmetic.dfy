include "parser.dfy"

module {:options "-functionSyntax:4", "-quantifierSyntax:4"}  EngineParens {
  import opened Parsers
  import opened ParserBuilders
  import opened ParserEngine

  class EngineParens extends ParserEngine.Engine {
    constructor(input: string) {
      this.input := input;
    }

    const fixmapBase: map<string, ParserMapper<Expression>> := map[]

    function {:opaque} atom(functions: set<string>): (mapper: ParserMapper<Expression>)
      requires "plus__" in functions
      ensures RecSpecOnce("atom", functions, mapper)
    {
      (rec: ParserSelector<Expression>, pos: nat) requires RecSpec("atom", functions, rec, pos) =>
        C?("(").o_I(B(rec("plus__")).I_o(C(")")))
        .O(N().M(n => Number(n))).apply(pos)
    }

    function {:opaque} times(functions: set<string>): (mapper: ParserMapper<Expression>)
      requires "atom" in functions
      ensures RecSpecOnce("times", functions, mapper)
    {
      (rec: ParserSelector<Expression>, pos: nat) requires RecSpec("times", functions, rec, pos) =>
       Bind(rec("atom"), (expr: Expression, pos': nat) =>
             RepAcc(Concat(Or(Const?("*"), Or(Const?("/"), Const?("%"))), rec("atom")), expr, Expression.InfixBuilder()))(pos)
    }

    function {:opaque} plus(functions: set<string>): (mapper: ParserMapper<Expression>)
      requires "times" in functions
      ensures RecSpecOnce("plus__", functions, mapper)
    {
      (rec: ParserSelector<Expression>, pos: nat) requires RecSpec("plus__", functions, rec, pos) =>
       Bind(rec("times"), (expr: Expression, pos': nat) =>
             RepAcc(Concat(Or(Const?("+"), Const?("-")), rec("times")), expr, Expression.InfixBuilder()))(pos)
    }

    /* The DSL makes verification 7/2 slower (7M resource units vs 2M resource units above*/
    /*function {:opaque} plus(functions: set<string>): (mapper: ParserMapper<Expression>)
      requires "times" in functions
      ensures FixMapInnerOnce("plus__", mapper, functions, |input|)
    {
       (rec: ParserSelector<Expression>, pos: nat)
         requires RecSpec("plus__", functions, rec, pos) =>
           B(rec("times")).Then((expr: Expression, pos': nat) =>
             C?("+").o_I(B(rec("times")))
             .Repeat(expr, Expression.BinaryBuilder("+"))).apply(pos)
    }*/

    function {:opaque} ExpressionsFix(): (r: ParseResult<Expression>)
    {
      var functions := {"atom", "times", "plus__"};
      var underlying := fixmapBase[ 
        "atom" := atom(functions)][
        "times" := times(functions)][
        "plus__" := plus(functions)];
      FixMap(underlying, "plus__")(0)
    }
  }

  function NatToString(n: nat): string {
    if 0 <= n <= 9 then
      ["0123456789"[n]]
    else
      NatToString(n/10) + NatToString(n%10)
  }

  datatype Expression =
    | Binary(op: string, left: Expression, right: Expression)
    | Number(x: nat)
  {
    static function BinaryBuilder(op: string): (Expression, Expression) -> Expression
    {
      (left: Expression, right: Expression) => Binary(op, left, right)
    }
    static function InfixBuilder(): (Expression, (string, Expression)) -> Expression
    {
      (left: Expression, right: (string, Expression)) => Binary(right.0, left, right.1)
    }
    function ToString(level: nat): string
      requires level <= 2
    {
      match this
      case Number(x) => NatToString(x)
      case Binary(op, left, right) => 
        (match level case 0 => "(" case 1 => "[" case 2 => "{")
        + left.ToString((level + 1)%3) + op + right.ToString((level + 1) % 3)
        + (match level case 0 => ")" case 1 => "]" case 2 => "}")
    }
  }

  function repeat(str: string, n: nat): (r: string)
    ensures |r| == |str| * n
  {
    if n == 0 then ""
    else str + repeat(str, n-1)
  }

  method Main(args: seq<string>) {
    if |args| <= 1 {
      return;
    }
    for i := 1 to |args| {
      var input := args[i];
      var engine := new EngineParens(input);
      match engine.ExpressionsFix() {
        case PSuccess(_, n) => print "result:", n.ToString(0);
        case PFailure(level, error, pos) => print input, "\n";
          print repeat(" ", pos), "^","\n";
        print error;
      }
      print "\n";
    }
  }
}