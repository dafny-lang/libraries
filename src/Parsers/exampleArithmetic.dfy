include "parser.dfy"

module ArithmeticParser {
  import opened StringParsers
  import opened Printer

  datatype Expression =
    | Binary(op: string, left: Expression, right: Expression)
    | Number(x: int)
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
      case Number(x) => (if x < 0 then "-" else "") + Printer.natToString(if x < 0 then -x else x)
      case Binary(op, left, right) => 
        (match level case 0 => "(" case 1 => "[" case 2 => "{")
        + left.ToString((level + 1)%3) + op + right.ToString((level + 1) % 3)
        + (match level case 0 => ")" case 1 => "]" case 2 => "}")
    }
  }

  const buildParsedExpr: ((Expression, Wrappers.Option<(string, Expression)>)) -> Expression
    := ((result: (Expression, Wrappers.Option<(string, Expression)>)) =>
     if result.1.None? then result.0 else
     Binary(result.1.value.0, result.0, result.1.value.1))

  const parser: Parser<Expression>
    := FixpointMap(
      map[
        "atom" :=
          RecursiveDef(0, (callback: ParserSelector<Expression>) => 
          Or(ConcatR(
              Const?("("),
                ConcatL(callback("term"), Const(")"))),
             Map(Int(), (result: int) => Number(result))    
            )),
        "factor" :=
          RecursiveDef(1, (callback: ParserSelector<Expression>) => 
            Map(
            Concat(
              callback("atom"),
              Maybe(Concat(Or(Const?("*"), Const?("/")),
                     callback("factor")))),
            buildParsedExpr
          )),
        "term" :=
          RecursiveDef(2, (callback: ParserSelector<Expression>) => 
            Map(
            Concat(callback("factor"),
            Maybe(Concat(Or(Const?("+"), Const?("-")),
                   callback("term")))),
            buildParsedExpr
          ))
      ],
      "term"
    );

  method Main(args: seq<string>) {
    if |args| <= 1 {
      return;
    }
    for i := 1 to |args| {
      var input := args[i];
      Succeed_NonCrashingAuto<Expression>();
      assume {:axiom} Valid(parser); // TODO: Prove
      reveal Valid();
      match parser(input) {
        case PSuccess(result, _) =>
          print "result:", result.ToString(0), "\n";
        case failure =>
          PrintFailure(input, failure);
      }
      print "\n";
    }
  }
}