include "../StringParsersBuilders.dfy"


module PolynomialParsersBuilder {
  import opened StringParsersBuilders

  import P = StringParsersBuilders.P

  // PArsers builder style
  const parser: B<Expr>
    := 
      Rec(map[
        "atom" := RecDef(0, (c: RecSel<Expr>) =>
            O([
              String("(").e_I(c("term")).I_e(String(")")),
              Int().M((result: int) => Number(result)),
              String("x").e_I(String("^").e_I(Int()).Maybe().M(
                (result: P.Option<int>) =>
                  if result.Some? then Unknown(result.value) else Unknown(1)))
            ])),

        "factor" := RecDef(1, (c: RecSel<Expr>) => 
          c("atom").Bind((atom: Expr) => // TODO: Finish this one
            O([String("*"), String("/"), String("%")])
            .I_I(c("atom")).Rep(atom, Expr.InfixBuilder()))),

        "term" := RecDef(2, (c: RecSel<Expr>) => 
          c("factor").Bind((atom: Expr) =>
            O([String("+"), String("-")])
            .I_I(c("factor")).Rep(atom, Expr.InfixBuilder())))
      ], "term")
      .I_e(End())

  type Result<A, B> = StringParsersBuilders.P.Wrappers.Result<A, B>

  datatype Expr =
    | Binary(op: string, left: Expr, right: Expr)
    | Number(value: int)
    | Unknown(power: int)
  {

    function Simplify(): Result<Expr, string> {
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
                if r.value == 0 then
                  Result.Failure("Division by zero (" + right.ToString()
                  + " evaluates to zero)")
                else
                  Result.Success(Number(l.value / r.value))
              case "%" =>
                if r.value == 0 then
                  Result.Failure("Modulo by zero (" + right.ToString()
                  + " evaluates to zero)")
                else
                  Result.Success(Number(l.value % r.value))
              case _ => Result.Failure("Unsupported operator: " + op)
            }
         else
           Result.Success(Binary(op, l, r))
        case Unknown(0) => Result.Success(Number(1))
        case Unknown(_) => Result.Success(this)
      }
    }
    static function InfixBuilder(): (Expr, (string, Expr)) -> Expr
    {
      (left: Expr, right: (string, Expr)) => Binary(right.0, left, right.1)
    }
    function ToString(): string {
      match this
      case Number(x) => P.intToString(x)
      case Binary(op, left, right) =>
        "("
        + left.ToString() + op + right.ToString()
        + ")"
      case Unknown(power) =>
        if power == 1 then "x" else if power == 0 then "1" else
        "x^" + P.intToString(power)
    }
  }
  
  method Main(args: seq<string>) {
    if |args| <= 1 {
      print "Please provide a polynomial to parse as argument\n";
      return;
    }
    for i := 1 to |args| {
      var input := args[i];
      match parser.apply(input) {
        case Success(result, remaining) =>
          print "Polynomial:", result.ToString(), "\n";
          match result.Simplify() {
            case Success(x) =>
              print "Simplified:", x.ToString(), "\n";
            case Failure(message) =>
              print message;
          }
        case failure =>
          P.PrintFailure(input, failure);
      }
      print "\n";
    }
  }
}