include "parser.dfy"

module ArithmeticParser {
  import opened StringParsers
  import opened Printer

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
      case Number(x) => Printer.natToString(x)
      case Binary(op, left, right) => 
        (match level case 0 => "(" case 1 => "[" case 2 => "{")
        + left.ToString((level + 1)%3) + op + right.ToString((level + 1) % 3)
        + (match level case 0 => ")" case 1 => "]" case 2 => "}")
    }
  }

  const parser: Parser<Expression>
    := Succeed<Expression>(Number(1))
  
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
      Succeed_NonCrashingAuto<Expression>();
      assert Valid(parser);
      reveal Valid();
      match parser(input) {
        case PSuccess(result, _) =>
          print "result:", result.ToString(0), "\n";
        case PFailure(level, failureData) => print input, "\n";
          var pos: nat := |input| - |failureData.remaining|; // Need the parser to be Valid()
          print repeat(" ", pos), "^","\n";
        print failureData.message;
      }
      print "\n";
    }
  }
}