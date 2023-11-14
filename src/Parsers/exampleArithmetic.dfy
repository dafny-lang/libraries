include "stringParsers.dfy"

module ArithmeticParser {
  import opened StringParsers
  import opened StringNat

  // Pure functional style
  const parser: Parser<Expression>
    := ConcatL(
      RecursiveMap(
      map[
        "atom" :=
          RecursiveDef(0, (callback: ParserSelector<Expression>) => 
          Or(ConcatR(
            String("("), ConcatL(
            callback("term"),
            String(")"))),
          Or(
            Map(Int(), (result: int) => Number(result)), ConcatR(
            String("x"),
              Map(Maybe(ConcatR(
                String("^"), Int())),
                  (result: Option<int>) =>
                    if result.Some? then Unknown(result.value) else Unknown(1)
          ))))),
        "factor" :=
          RecursiveDef(1, (callback: ParserSelector<Expression>) => 
            Bind(callback("atom"), (atom: Expression) =>
              Rep(
                Concat(Or(String("*"), Or(String("/"), String("%"))),
                   callback("atom")),
                Expression.InfixBuilder(), atom)
              )
          ),
        "term" :=
          RecursiveDef(2, (callback: ParserSelector<Expression>) => 
            Bind(callback("factor"), (factor: Expression) =>
              Rep(
                Concat(Or(String("+"), String("-")),
                   callback("factor")),
                Expression.InfixBuilder(), factor)
              )
          )
      ],
      "term"
    ), EndOfString())

  // DSL style
  const parserDSL: Parser<Expression>
    := ConcatL(
      RecursiveMap(
      map[
        "atom" :=
          RecursiveDef(0, (callback: ParserSelector<Expression>) => 
          Or(ConcatR(
            String("("), ConcatL(
            callback("term"),
            String(")"))),
          Or(
            Map(Int(), (result: int) => Number(result)), ConcatR(
            String("x"),
              Map(Maybe(ConcatR(
                String("^"), Int())),
                  (result: Option<int>) =>
                    if result.Some? then Unknown(result.value) else Unknown(1)
          ))))),
        "factor" :=
          RecursiveDef(1, (callback: ParserSelector<Expression>) => 
            Bind(callback("atom"), (atom: Expression) =>
              Rep(
                Concat(Or(String("*"), Or(String("/"), String("%"))),
                   callback("atom")),
                Expression.InfixBuilder(), atom)
              )
          ),
        "term" :=
          RecursiveDef(2, (callback: ParserSelector<Expression>) => 
            Bind(callback("factor"), (factor: Expression) =>
              Rep(
                Concat(Or(String("+"), String("-")),
                   callback("factor")),
                Expression.InfixBuilder(), factor)
              )
          )
      ],
      "term"
    ), EndOfString())


  type Result<A, B> = StringParsers.Wrappers.Result<A, B>

  datatype Expression =
    | Binary(op: string, left: Expression, right: Expression)
    | Number(value: int)
    | Unknown(power: int)
  {

    function Simplify(): Result<Expression, string> {
      match this {
        case Number(x: int) => Result.Success(this)
        case Binary(op, left, right) =>
          var l :- left.Simplify();
          var r :- right.Simplify();
          if l.Number? && r.Number? then
            match op {
              case "+" => Result.Success(Number(l.value + r.value))
              case "-" => Result.Success(Number(l.value - r.value))
              case "*" => Result.Success(Number(l.value * r.value))
              case "/" => 
                if r.value == 0 then Result.Failure("Division by zero (" + right.ToString() + " evaluates to zero)") else
                Result.Success(Number(l.value / r.value))
              case "%" =>
                if r.value == 0 then Result.Failure("Modulo by zero (" + right.ToString() + " evaluates to zero)") else
                Result.Success(Number(l.value % r.value))
              case _ => Result.Failure("Unsupported operator: " + op)
            }
         else
           Result.Success(Binary(op, l, r))
        case Unknown(0) => Result.Success(Number(1))
        case Unknown(_) =>
          Result.Success(this)
      }
    }
    static function BinaryBuilder(op: string): (Expression, Expression) -> Expression
    {
      (left: Expression, right: Expression) => Binary(op, left, right)
    }
    static function InfixBuilder(): (Expression, (string, Expression)) -> Expression
    {
      (left: Expression, right: (string, Expression)) => Binary(right.0, left, right.1)
    }
    function ToString(): string
    {
      match this
      case Number(x) => (if x < 0 then "-" else "") + StringNat.natToString(if x < 0 then -x else x)
      case Binary(op, left, right) => 
        "("
        + left.ToString() + op + right.ToString()
        + ")"
      case Unknown(power) =>
        if power == 1 then "x" else if power == 0 then "1" else
        if power < 0 then "x^(-" + StringNat.natToString(0-power)+")" else
        "x^" + StringNat.natToString(power)
    }
  }

  const buildParsedExpr: ((Expression, Wrappers.Option<(string, Expression)>)) -> Expression
    := ((result: (Expression, Wrappers.Option<(string, Expression)>)) =>
     if result.1.None? then result.0 else
     Binary(result.1.value.0, result.0, result.1.value.1))

  method Main(args: seq<string>) {
    if |args| <= 1 {
      return;
    }
    for i := 1 to |args| {
      var input := args[i];
      match parser(input) {
        case Success(result, remaining) =>
          if |remaining| != 0 {
            print "'" + remaining +"'", "\n";
            PrintFailure<int>(input, Failure(Recoverable, FailureData("Expected end of string", remaining, Option.None)));
          }
          print "Computation:", result.ToString(), "\n";
          match result.Simplify() {
            case Success(x) =>
              print "Result:", x.ToString(), "\n";
            case Failure(message) =>
              print message;
          }
        case failure =>
          PrintFailure(input, failure);
      }
      print "\n";
    }
  }
}