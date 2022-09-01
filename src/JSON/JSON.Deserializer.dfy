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

module {:options "-functionSyntax:4"} JSON.Deserializer {
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

  function Transcode8To16Unescaped(str: seq<byte>): DeserializationResult<string>
    // TODO Optimize with a function by method
  { // FIXME unescape unicode
    Str.UnescapeQuotes(UtfUtils.Transcode8To16(str)).MapFailure(_ => EscapeAtEOS)
  }

  function String(js: Grammar.jstring): DeserializationResult<string> {
    Transcode8To16Unescaped(js.Bytes())
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
        var frac :- ToInt(View.Empty, num);
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
}
