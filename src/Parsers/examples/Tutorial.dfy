// RUN: %test "%s"

include "../stringParsersBuilders.dfy"

module Tutorial.Parsers {
  import opened StringParsers
  
  method {:test} TestSplit1() {
    var nonComma: Parser<string> :=
      Many((c: char) => c != ',', "non-comma");
    var p :=
      Bind(nonComma, (result: string) =>
        Rep(ConcatR(String(","), nonComma),
          (acc, elem) => acc + [elem],
          [result]
        ));

    expect p("abc,d,efg") == ParseResult.Success(["abc","d","efg"], "");
    expect p("abc,d,,") ==
      ParseResult.Failure(Recoverable, FailureData("expected a non-comma", ",", Option.None));
    PrintFailure("abc,d,,", p("abc,d,,"));
    // Displays 
    // Error:
    // 1: abc,d,,
    //          ^
    // expected a non-comma
  }

  function flatten<A>(): ((A, (A, A))) -> (A, A, A) {
    (input: (A, (A, A))) =>
    (input.0, input.1.0, input.1.1)
  }

  method {:test} TestTicTacToe() {
    var x := OrSeq([
      String("O"), String("X"), String(" ")
    ]);
    var v := String("|");
    var row := Map(Concat(x, ConcatR(v, Concat(x, ConcatR(v, x)))),
      flatten<string>());
    var sep := String("\n-+-+-\n");
    var grid := Map(
      Concat(row, ConcatR(sep, Concat(row, ConcatR(sep, row)))),
      flatten<(string, string, string)>())
    ;
    var input := "O|X| \n-+-+-\nX|O| \n-+-+-\nP| |O";
               // 012345 678901 234567 890123 45678
    var r := grid(input);
    expect r.IsFailure();
    expect |input| - |r.data.remaining| == 24;
    expect r.data.message == "expected 'O'";
    expect r.data.next.Some?;
    expect r.data.next.value.message == "expected 'X'";
    expect r.data.next.value.next.Some?;
    expect r.data.next.value.next.value.message == "expected ' '";
    expect r.data.next.value.next.value.next.None?;
    PrintFailure(input, r);
    // Displays:
    // Error:
    //  5: P| |O
    //     ^
    //  expected 'O', or
    //  expected 'X', or
    //  expected ' '
  }
}


module Tutorial.ParsersBuilders {
  import opened StringParsersBuilders
  
  method {:test} TestSplit1() {
    var nonComma: B<string> :=
      Many((c: char) => c != ',', "non-comma");
    var p :=
      nonComma.Bind((result: string) =>
        String(",").e_I(nonComma).Rep([result],
          (acc: seq<string>, elem: string) => acc + [elem]
        ));

    expect p.apply("abc,d,efg") == P.ParseResult.Success(["abc","d","efg"], "");
  }
}