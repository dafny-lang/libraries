// RUN: %test "%s"

include "../stringParsersBuilders.dfy"

// A small regex-like language that can be turned into a straightforward parser
// a compiler from this language to an imperative language
// and a parser that can act 
// and a parser that can act as a specification
module ParserGenerator {
  import opened StringParsersBuilders

  type Option<A> = StringParsersBuilders.P.Option<A>

  function ToBool<T>(): T -> bool {
    t => true
  }

  datatype ParserSpec =
    | Const(s: string)
    | And(left: ParserSpec, right: ParserSpec)
    | Or(left: ParserSpec, right: ParserSpec)
    | Repeat(p: ParserSpec)
  {
    function ToParser(): B<bool> {
      match this
      case Const(s) => S(s).M(ToBool())
      case And(left, right) => left.ToParser().e_I(right.ToParser()).M(ToBool())
      case Or(left, right) => O([left.ToParser().??(), right.ToParser()]).M(ToBool())
      case Repeat(x) => x.ToParser().ZeroOrMore().M(ToBool())
    }
    function ToString(): string {
      match this
      case Const(s) => s
      case And(left, right) => left.ToString() + right.ToString()
      case Or(left, right) => "(" + left.ToString() + "|" + right.ToString() + ")"
      case Repeat(underlying) =>
        var u := underlying.ToString();
        if |u| == 0 then "" else
        if u[0..1] == "(" then u + "*"
        else "(" + u + ")*"
    }
  }

  const parseSpec: B<ParserSpec> :=
    RecMap(map[
      "atom" := RecMapDef(0, (c: RecMapSel<ParserSpec>) =>
        O([
          S("(").e_I(c("or")).I_e(S(")")).Bind((atom: ParserSpec) => 
            S("*").?().M((star: Option<string>) =>
              if star.None? then atom else Repeat(atom))
          ),
          Except("()|").M((r: string) => ParserSpec.Const(r))
      ])),
      "and" := RecMapDef(1, (c: RecMapSel<ParserSpec>) =>
        c("atom").RepMerge((atom1: ParserSpec, atom2: ParserSpec) => And(atom1, atom2))),
      "or" := RecMapDef(2, (c: RecMapSel<ParserSpec>) =>
        c("and").RepSepMerge(S("|"), (and1: ParserSpec, and2: ParserSpec) => Or(and1, and2)))
    ], "or")

  method {:test} TestParser() {
    var program := "abc((de|f((g))*))ml";
    ParseTestCallback(parseSpec, program, (result: ParserSpec) => result.ToString());
    var parser := parseSpec.apply(program);
    expect parser.Success?;
    var underlying := parser.result.ToParser();
    program := "abcdeml";
    print underlying.apply(program); // Should print true
  }
}