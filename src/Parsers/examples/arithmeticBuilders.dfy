include "../stringParsersBuilders.dfy"


module PolynomialParsersBuilder {
  import opened StringParsersBuilders

  type Result<A, B> = StringParsersBuilders.P.Wrappers.Result<A, B>

  datatype Expression =
    | Binary(op: string, left: Expression, right: Expression)
    | Number(value: int)
    | Unknown(power: int)
  {
    static function InfixBuilder(): (Expression, (string, Expression)) -> Expression
    {
      (left: Expression, right: (string, Expression)) => Binary(right.0, left, right.1)
    }
  }
  
  // DSL style
  const parserDSL: B<Expression>
    := 
      Rec(
      map[
        "atom" :=
          RecDef(0, (c: Sel<Expression>) =>
            O([
              String("(").e_I(c("term")).I_e(String(")")),
              Int().M((result: int) => Number(result)),
              String("x").e_I(String("^").e_I(Int()).Maybe().M(
                  (result: StringParsersBuilders.P.Option<int>) =>
                    if result.Some? then Unknown(result.value) else Unknown(1)))
            ])),
        "factor" :=
          RecDef(1, (c: Sel<Expression>) => 
            c("atom").Then((atom: Expression) => // TODO: Finish this one
              O([
                String("*"),
                String("/"),
                String("%")
              ]).I_I(c("atom")).Rep(atom, Expression.InfixBuilder()))),
        "term" :=
          RecDef(1, (c: Sel<Expression>) => 
            c("factor").Then((atom: Expression) =>
              O([
                String("+"),
                String("-")
              ]).I_I(c("factor")).Rep(atom, Expression.InfixBuilder())))
      ],
      "term"
    ).I_e(End())
}