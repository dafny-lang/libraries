// RUN: %test "%s"

include "../stringParsersBuilders.dfy"

// A small regex-like language that can be turned into a straightforward parser
// So first we parse the parser to ParserSpec, we convert it to a parser
// and we parse the string using this parser.
// TODO: Compile this parser and prove it does the same.
module AdventOfCode1 {
  import opened StringParsersBuilders

  const nonDigit :=
    Except("0123456789\r\n").ZeroOrMore()

  const digit :=
    B(P.DigitNumber())

  const parseLine :=
    nonDigit.e_I(digit).Bind((first: nat) =>
      nonDigit.e_I(digit).??().Rep((first, first),
        (pair: (nat, nat), newDigit: nat) => (pair.0, newDigit)
      )).I_e(nonDigit)
      
  const parseInput :=
    parseLine.I_e(S("\r").?().e_I(S("\n").?()))
      .Rep(0, (acc: int, newElem: (nat, nat)) =>
      acc + newElem.0 * 10 + newElem.1)

  method {:test} TestParser() {
    var input := @"1abc2
pqr3stu8vwx
a1b2c3d4e5f
treb7uchet";
    ParseTest(parseInput, input);
  }
}