include "parsers.dfy"

module StringParsers refines Parsers {
  type C = char

  // ##################################
  // String-specific parser combinators
  // ##################################

  opaque function CharTest(test: char -> bool, name: string): (p: Parser<char>)
    // A parser that returns the current char if it passes the test
    // Returns a recoverable error based on the name otherwise
  {
    (input: string) =>
      if 0 < |input| && test(input[0]) then Success(input[0], input[1..])
      else Failure(Recoverable,
        FailureData("expected a "+name, input, Option.None))
  }

  opaque function Char(expectedChar: char): (p: Parser<char>)
    // A parser that tests if the current char is the given expected char
  {
    CharTest((c: char) => c == expectedChar, [expectedChar])
  }

  opaque function Digit(): (p: Parser<char>)
    // A parser that tests if the current char is a digit and returns it
  {
    CharTest(c => c in "0123456789", "digit")
  }

  opaque function DigitNumber(): (p: Parser<nat>)
    // A parser that returns the current char as a number if it is one
  {
    Map(Digit(), (c: char) =>
      var n: nat := (if StringNat.IsStringNat([c]) then // Should always be true
         StringNat.stringToNat([c])
       else 0); n
    )
  }

  opaque function Nat(): (p: Parser<nat>)
    // A parser that parses a natural number
  {
    Bind(DigitNumber(),
      (result: nat) =>
        Rep(DigitNumber(),
          (previous: nat, c: nat) =>
            var r: nat := previous * 10 + c; r,
          result          
        )
    )
  }

  opaque function Int(): (p: Parser<int>)
    // A parser that parses a integer, possibly negative
  {
    Bind(Maybe(Char('-')),
      (minusSign: Option<char>) =>
        Map<nat, int>(Nat(), (result: nat) => if minusSign.Some? then 0-result else result))
  }

  opaque function String(expected: string): (p: Parser<string>)
    // A parser that succeeds only if the input starts with the given string
  {
    (input: string) =>
      if |expected| <= |input| && input[0..|expected|] == expected then Success(expected, input[|expected|..])
      else Failure(Recoverable, FailureData("expected '"+expected+"'", input, Option.None))
  }

  // ########################
  // Error handling utilities
  // ########################

  function repeat_(str: string, n: nat): (r: string)
    // Repeats the given string n times
    ensures |r| == |str| * n
  {
    if n == 0 then ""
    else str + repeat_(str, n-1)
  }

  method ExtractLineCol(input: string, pos: nat)
    returns (lineNumber: nat, lineStr: string, colNumber: nat)
    // Returns the line number, the extracted line, and the column number
    // corresponding to a given position in the given input  
  {
    lineNumber := 1;
    var startLinePos: nat := 0;
    colNumber := 0;
    var i := 0;
    while i < |input| && i != pos
      invariant 0 <= startLinePos <= i <= |input|
    {
      colNumber := colNumber + 1;
      if input[i] == '\r' && i + 1 < |input| && input[i+1] == '\n' {
        lineNumber := lineNumber + 1;
        colNumber := 0;
        i := i + 1;
        startLinePos := i + 1;
      } else if input[i] in "\r\n" {
        lineNumber := lineNumber + 1;
        colNumber := 0;
        startLinePos := i + 1;
      }
      i := i + 1;
    }
    while i < |input| && input[i] !in "\r\n"
      invariant startLinePos <= i <= |input|
    {
      i := i + 1;
    }
    lineStr := input[startLinePos..i];
  }
  
  method PrintFailure<R>(input: string, result: ParseResult<R>, printPos: int := -1)
    // Util to print the line, the column, and all the error messages
    // associated to a given parse failure
    requires result.Failure?
    decreases result.data
  {
    if printPos == -1 {
      print if result.level == Fatal then "Fatal error" else "Error", ":\n";
    }
    var pos: int := |input| - |result.data.remaining|; // Need the parser to be Valid()
    if pos < 0 { // Could be proved false if parser is Valid()
      pos := 0;
    }
    if printPos != pos {
      var line, lineStr, col := ExtractLineCol(input, pos);
      print line, ": ", lineStr, "\n";
      print repeat_(" ", col + 2 + |intToString(line)|), "^","\n";
    }
    print result.data.message;
    if result.data.next.Some? {
      print ", or\n";
      PrintFailure<R>(input, Failure(result.level, result.data.next.value), pos);
    } else {
      print "\n";
    }
  }
}