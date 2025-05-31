// RUN: %test "%s"

include "../stringParsersBuilders.dfy"

// A small regex-like language that can be turned into a straightforward parser
// So first we parse the parser to ParserSpec, we convert it to a parser
// and we parse the string using this parser.
// TODO: Compile this parser and prove it does the same.
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
    predicate OnlyAndRepeat() {
      match this
      case Const(s) => true
      case And(left, right) => left.OnlyAndRepeat() && right.OnlyAndRepeat()
      case Or(left, right) => false
      case Repeat(p) => p.OnlyAndRepeat()
    }
    function ToParser(): B<bool> {
      match this
      case Const(s) => S(s).M(ToBool())
      case And(left, right) => left.ToParser().e_I(right.ToParser()).M(ToBool())
      case Or(left, right) => O([left.ToParser().??(), right.ToParser()]).M(ToBool())
      case Repeat(x) => x.ToParser().??().ZeroOrMore().M(ToBool())
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

  // TODO: Some kind of compilation?
/*
  datatype ParserStmt = 
      Expect(c: char)
    | Stmts(first: ParserStmt, next: PArserStmt)
    | Repeat(underlying: ParserStmt)
    | Break()
  {
    function ToProgram(indent: string := ""): string {
      match this {
        case Expect(c) => "if input[i] == '" + [c] + "' { }"
      }
    }
    // (ok, cancelling)
    function Run(input: string, index: nat): (bool, nat) {
      if |input| <= index then (false, index) else
      match this {
        case Expect(c) => (input[index] == c, index + 1)
        case Stmts(first) =>
          if s == [] then (true, index)
          else 
            var (r, newIndex) := !s[0].Run(input, index);
            if r then Stmts(s[1..]).Run(input, newIndex)
            else (false, index) // We completely forget about the failure
        case Break() => 
        case Repeat(stmts) =>
          stmts 
      }
    }

    method RunImperative(input: string) returns (b: bool)
      ensures b == Run(input, 0)
    {
      var i := 
    }
  }
  //datatype 
*/
  // A ParserSpec can be compiled to this non-deterministic Automata
  // We will prove that the two parsing strategies are equivalent
  /*datatype Automata = Automata(
    nStates: nat,
    startState: nat,
    transitions: set<(nat, char, nat)>,
    finalState: set<nat>
  )
  {
    static function FromParserSpec(spec: ParserSpec): Automata {
      match spec {
        case Const("") =>
          Automata(1, 0, {}, {0})
        case Const(s) =>
          var a := FromParserSpec(Const(s[1..]));
          var newStart := a.nStates;
          Automata(a.nStates + 1, newStart, a.transitions + {(newStart, s[0], a.startState)}, a.finalState)
        case Or(left, right) =>
          var l := FromParserSpec(left);
          var r := FromParserSpec(right);
          var offsetRight := (n: nat) => n + l.nStates;
          var newStart := l.nStates + r.nStates + 1;
          var rightTransitions := set rt <- r.transitions :: (offsetRight(rt.0), rt.1, offsetRight(rt.2));
          Automata(l.nStates + r.nStates + 1,
            newStart,
            l.transitions + rightTransitions +
            + set firstLeftTransition <- l.transitions |
                firstLeftTransition.0 == l.start
          )
        case _ => Automata(0, 0, {}, {})
      }
    }

    function Run(input: string, states: set<nat>, index: nat): set<nat> {
      if index >= |input| then {}
      else set newState: nat, s: nat |
              0 <= newState < nStates && 0 <= s < nStates &&
              (s, input[index], newState) in transitions
        :: newState 
    }
    predicate Accepts(input: string) {
      Run(input, {startState}, 0) * finalState != {}
    }

    lemma Equivalence(spec: ParserSpec, input: string)
      ensures spec.ToParser().apply(input).Success?
              <==> FromParserSpec(spec).Accepts(input)
    {
      
    }
  }*/
}