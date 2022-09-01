include "../BoundedInts.dfy"
include "../Wrappers.dfy"

module {:options "-functionSyntax:4"} Str {
  import opened Wrappers

  abstract module ParametricConversion {
    import opened Wrappers

    type Char(==)
    type String = seq<Char>

    // FIXME the design in LittleEndianNat makes BASE a module-level constant
    // instead of a function argument
    function Digits(n: int, base: int): (digits: seq<int>)
      requires base > 1
      requires n >= 0
      decreases n
      ensures forall d | d in digits :: 0 <= d < base
    {
      if n == 0 then
        []
      else
        assert n > 0;
        assert base > 1;
        assert n < base * n;
        assert n / base < n;
        Digits(n / base, base) + [n % base]
    }

    function OfDigits(digits: seq<int>, chars: seq<Char>) : (str: String)
      requires forall d | d in digits :: 0 <= d < |chars|
      ensures forall c | c in str :: c in chars
    {
      if digits == [] then []
      else
        assert digits[0] in digits;
        assert forall d | d in digits[1..] :: d in digits;
        [chars[digits[0]]] + OfDigits(digits[1..], chars)
    }

    function OfNat_any(n: nat, chars: seq<Char>) : (str: String)
      requires |chars| > 1
      ensures forall c | c in str :: c in chars
    {
      var base := |chars|;
      if n == 0 then [chars[0]]
      else OfDigits(Digits(n, base), chars)
    }

    predicate NumberStr(str: String, minus: Char, is_digit: Char -> bool) {
      str != [] ==>
        && (str[0] == minus || is_digit(str[0]))
        && forall c | c in str[1..] :: is_digit(c)
    }

    function OfInt_any(n: int, chars: seq<Char>, minus: Char) : (str: String)
      requires |chars| > 1
      ensures NumberStr(str, minus, c => c in chars)
    {
      if n >= 0 then OfNat_any(n, chars)
      else [minus] + OfNat_any(-n, chars)
    }

    function DigitsTable(digits: seq<Char>): map<Char, nat>
      requires forall i, j | 0 <= i < j < |digits| :: digits[i] != digits[j]
    {
      map i: nat | 0 <= i < |digits| :: digits[i] := i
    }

    function ToNat_any(str: String, base: nat, digits: map<Char, nat>) : (n: nat)
      requires forall c | c in str :: c in digits
      requires base > 0
    {
      if str == [] then 0
      else ToNat_any(str[..|str| - 1], base, digits) * base + digits[str[|str| - 1]]
    }

    function ToInt_any(str: String, minus: Char, base: nat, digits: map<Char, nat>) : (s: int)
      requires NumberStr(str, minus, c => c in digits)
      requires str != [minus]
      requires base > 0
    {
      if [minus] <= str then -(ToNat_any(str[1..], base, digits) as int)
      else
        assert str == [] || str == [str[0]] + str[1..];
        ToNat_any(str, base, digits)
    }
  }

  abstract module ParametricEscaping {
    import opened Wrappers

    type Char(==)
    type String = seq<Char>

    function Escape(str: String, special: set<Char>, escape: Char): String {
      if str == [] then str
      else if str[0] in special then [escape, str[0]] + Escape(str[1..], special, escape)
      else [str[0]] + Escape(str[1..], special, escape)
    }

    datatype UnescapeError =
      EscapeAtEOS

    function Unescape(str: String, escape: Char): Result<String, UnescapeError> {
      if str == [] then Success(str)
      else if str[0] == escape then
        if |str| > 1 then var tl :- Unescape(str[2..], escape); Success([str[1]] + tl)
        else Failure(EscapeAtEOS)
      else var tl :- Unescape(str[1..], escape); Success([str[0]] + tl)
    }

    lemma {:induction false} Unescape_Escape(str: String, special: set<Char>, escape: Char)
      requires escape in special
      ensures Unescape(Escape(str, special, escape), escape) == Success(str)
    {
      if str == [] {
      } else {
        assert str == [str[0]] + str[1..];
        Unescape_Escape(str[1..], special, escape);
      }
    }
  }

  module CharStrConversion refines ParametricConversion {
    type Char = char
  }

  module CharStrEscaping refines ParametricEscaping {
    type Char = char
  }

  const HEX_DIGITS := [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'A', 'B', 'C', 'D', 'E', 'F']
  const HEX_TABLE :=
    CharStrConversion.DigitsTable(HEX_DIGITS);

  function OfInt(n: int, base: int := 10) : (str: string)
    requires 2 <= base <= 16
    ensures CharStrConversion.NumberStr(str, '-', c => c in HEX_DIGITS[..base])
  {
    CharStrConversion.OfInt_any(n, HEX_DIGITS[..base], '-')
  }

  function ToInt(str: string, base: int := 10) : (n: int)
    requires str != "-"
    requires 2 <= base <= 16
    requires CharStrConversion.NumberStr(str, '-', c => c in HEX_DIGITS[..base])
  {
    CharStrConversion.ToInt_any(str, '-', base, HEX_TABLE)
  }

  function EscapeQuotes(str: string): string {
    CharStrEscaping.Escape(str, {'\"', '\''}, '\\')
  }

  function UnescapeQuotes(str: string): Result<string, CharStrEscaping.UnescapeError> {
    CharStrEscaping.Unescape(str, '\\')
  }

  method Test() { // FIXME {:test}?
    expect OfInt(0, 10) == "0";
    expect OfInt(3, 10) == "3";
    expect OfInt(302, 10) == "302";
    expect OfInt(-3, 10) == "-3";
    expect OfInt(-302, 10) == "-302";
  }

  function OfBool(b: bool) : string {
    if b then "true" else "false"
  }

  function OfChar(c: char) : string {
    [c]
  }

  function Join(sep: string, strs: seq<string>) : string {
    if |strs| == 0 then ""
    else if |strs| == 1 then strs[0]
    else strs[0] + sep + Join(sep, strs[1..])
  }

  function Concat(strs: seq<string>) : string {
    Join("", strs)
  }

  import opened BoundedInts

  function ToBytes(s: string) : seq<uint8>
    requires forall c: char | c in s :: c as int < 256
  {
    seq(|s|, i requires 0 <= i < |s| =>
      assert s[i] in s; s[i] as byte)
  }
}
