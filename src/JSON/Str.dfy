include "../BoundedInts.dfy"

module {:options "/functionSyntax:4"} Str {
  module Private {
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

    function OfDigits(digits: seq<int>, chars: seq<char>) : string
      requires forall d | d in digits :: 0 <= d < |chars|
    {
      if digits == [] then ""
      else
        assert digits[0] in digits;
        assert forall d | d in digits[1..] :: d in digits;
        [chars[digits[0]]] + OfDigits(digits[1..], chars)
    }
  }

  function OfInt_any(n: int, chars: seq<char>) : string
    requires |chars| > 1
  {
    var base := |chars|;
    if n == 0 then
      "0"
    else if n > 0 then
      Private.OfDigits(Private.Digits(n, base), chars)
    else
      "-" + Private.OfDigits(Private.Digits(-n, base), chars)
  }

  const HEX_DIGITS := [
    '0', '1', '2', '3', '4', '5', '6', '7', '8', '9',
    'A', 'B', 'C', 'D', 'E', 'F']

  function OfInt(n: int, base: int := 10) : string
    requires 2 <= base <= 16
  {
    OfInt_any(n, HEX_DIGITS[..base])
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
