/// ===============================================
///  Deserialization from JSON.Grammar to JSON.AST
/// ===============================================
///
/// For the spec, see ``JSON.Spec.dfy``.

include "../Collections/Sequences/Seq.dfy"
include "../BoundedInts.dfy"
include "../Math.dfy"

include "Views.dfy"
include "Vectors.dfy"
include "UtfUtils.dfy"
include "JSON.Errors.dfy"
include "JSON.AST.dfy"
include "JSON.Grammar.dfy"
include "JSON.Spec.dfy"

module {:options "/functionSyntax:4"} JSON.Deserializer {
  import Seq
  import Math

  import opened Wrappers
  import opened BoundedInts
  import opened Str
  import UtfUtils

  import AST
  import Spec
  import opened Errors
  import opened Vectors
  import opened Grammar
  import opened Views.Core

  function Bool(js: Grammar.jbool): bool {
    assert js.Bytes() in {Grammar.TRUE, Grammar.FALSE};
    js.At(0) == 't' as byte
  }

  function Unescape(str: string, start: nat := 0): DeserializationResult<string>
    decreases |str| - start
  { // Assumes UTF-16 strings
    if start >= |str| then Success([])
    else if str[start] == '\\' then
      if |str| == start + 1 then
        Failure(EscapeAtEOS)
      else
        var c := str[start + 1];
        if c == 'u' then
          if |str| <= start + 6 then
            Failure(EscapeAtEOS)
          else
            var code := str[start + 2..start + 6];
            if exists c | c in code :: c !in Str.HEX_TABLE then
              Failure(UnsupportedEscape(code))
            else
              var tl :- Unescape(str, start + 6);
              var hd := Str.ToNat(code, 16);
              assert hd < 0x10000 by { reveal Math.IntPow(); }
              Success([hd as char] + tl)
        else
          var unescaped: uint16 := match c
             case '\"' => 0x22 as uint16 // quotation mark
             case '\\' => 0x5C as uint16 // reverse solidus
             case 'b'  => 0x08 as uint16 // backspace
             case 'f'  => 0x0C as uint16 // form feed
             case 'n'  => 0x0A as uint16 // line feed
             case 'r'  => 0x0D as uint16 // carriage return
             case 't'  => 0x09 as uint16 // tab
             case _    => 0 as uint16;
          if unescaped == 0 as uint16 then
            Failure(UnsupportedEscape(str[start..start+2]))
          else
            var tl :- Unescape(str, start + 2);
            Success([unescaped as char] + tl)
    else
      var tl :- Unescape(str, start + 1);
      Success([str[start]] + tl)
  }

  function Transcode8To16Unescaped(str: seq<byte>): DeserializationResult<string>
    // TODO Optimize with a function by method
  {
    Unescape(UtfUtils.Transcode8To16(str))
  }

  function String(js: Grammar.jstring): DeserializationResult<string> {
    Transcode8To16Unescaped(js.contents.Bytes())
  }

  module ByteStrConversion refines Str.ParametricConversion {
    import opened BoundedInts
    type Char = byte
  }

  const DIGITS := map[
    '0' as uint8 := 0, '1' as uint8 := 1, '2' as uint8 := 2, '3' as uint8 := 3,
    '4' as uint8 := 4, '5' as uint8 := 5, '6' as uint8 := 6, '7' as uint8 := 7,
    '8' as uint8 := 8, '9' as uint8 := 9
  ]

  const MINUS := '-' as uint8

  function ToInt(sign: jsign, n: jnum): DeserializationResult<int> {
    var n: int := ByteStrConversion.ToNat_any(n.Bytes(), 10, DIGITS);
    Success(if sign.Char?('-') then -n else n)
  }

  function Number(js: Grammar.jnumber): DeserializationResult<AST.Decimal> {
    var JNumber(minus, num, frac, exp) := js;
    var n :-
      ToInt(minus, num);
    var e10 :- match exp
      case Empty => Success(0)
      case NonEmpty(JExp(_, sign, num)) => ToInt(sign, num);
    match frac
      case Empty => Success(AST.Decimal(n, e10))
      case NonEmpty(JFrac(_, num)) =>
        var pow10 := num.Length() as int;
        var frac :- ToInt(minus, num);
        Success(AST.Decimal(n * Math.IntPow(10, pow10) + frac, e10 - pow10))
  }

  function KV(js: Grammar.jkv): DeserializationResult<(string, AST.JSON)> {
    var k :- String(js.k);
    var v :- Value(js.v);
    Success((k, v))
  }

  function Object(js: Grammar.jobject): DeserializationResult<seq<(string, AST.JSON)>> {
    Seq.MapWithResult(d requires d in js.data => KV(d.t), js.data)
  }

  function Array(js: Grammar.jarray): DeserializationResult<seq<AST.JSON>> {
    Seq.MapWithResult(d requires d in js.data => Value(d.t), js.data)
  }

  function Value(js: Grammar.Value): DeserializationResult<AST.JSON> {
    match js
      case Null(_) => Success(AST.Null())
      case Bool(b) => Success(AST.Bool(Bool(b)))
      case String(str) => var s :- String(str); Success(AST.String(s))
      case Number(dec) => var n :- Number(dec); Success(AST.Number(n))
      case Object(obj) => var o :- Object(obj); Success(AST.Object(o))
      case Array(arr) => var a :- Array(arr); Success(AST.Array(a))
  }

  function JSON(js: Grammar.JSON): DeserializationResult<AST.JSON> {
    Value(js.t)
  }
}
