/// =============================================
///  Serialization from JSON.AST to JSON.Grammar
/// =============================================
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

module {:options "-functionSyntax:4"} JSON.Serializer {
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

  type Result<+T> = SerializationResult<T>

  type bytes = seq<uint8>
  type bytes32 = bs: bytes | |bs| < TWO_TO_THE_32
  type string32 = s: string | |s| < TWO_TO_THE_32

  function Bool(b: bool): jbool {
    View.OfBytes(if b then TRUE else FALSE)
  }

  // method Utf8Encode(st: Vector<uint8>, cp: uint32)

  function Transcode16To8Escaped(str: string32, start: uint32 := 0): bytes {
    UtfUtils.Transcode16To8(Str.EscapeQuotes(str))
  }
  // by method {
  //   var len := |str| as uint32;
  //   if len == 0 {
  //     return [];
  //   }
  //   var st := new Vectors.Vector(0, len);
  //   var c0: uint16 := 0;
  //   var c1: uint16 := str[0] as uint16;
  //   var idx: uint32 := 0;
  //   while idx < len {
  //     var c0 := c1;
  //     var c1 := str[idx + 1] as uint16;
  //     if c0 < 0xD800 || c0 > 0xDBFF {
  //       Utf8Encode(st, UtfUtils.Utf16Decode1(c0));
  //       idx := idx +1;
  //     } else {
  //       Utf8Encode(st, UtfUtils.Utf16Decode2(c0, c1));
  //       idx := idx + 2;
  //     }
  //   }
  // }

  function CheckLength<T>(s: seq<T>, err: SerializationError): Outcome<SerializationError> {
    Need(|s| < TWO_TO_THE_32, err)
  }

  function String(str: string): Result<jstring> {
    :- CheckLength(str, StringTooLong(str));
    var bs := Transcode16To8Escaped(str);
    :- CheckLength(bs, StringTooLong(str));
    Success(View.OfBytes(bs))
  }

  function Sign(n: int): jminus {
    View.OfBytes(if n < 0 then ['-' as byte] else [])
  }

  module ByteStrConversion refines Str.ParametricConversion {
    import opened BoundedInts
    type Char = uint8
  }

  const DIGITS := [
    '0' as uint8, '1' as uint8, '2' as uint8, '3' as uint8,
    '4' as uint8, '5' as uint8, '6' as uint8, '7' as uint8,
    '8' as uint8, '9' as uint8
  ]

  const MINUS := '-' as uint8

  function Int'(n: int) : (str: bytes)
    ensures forall c | c in str :: c in DIGITS || c == MINUS
  {
    ByteStrConversion.OfInt_any(n, DIGITS, MINUS)
  }

  function Int(n: int) : Result<View> {
    var bs := Int'(n);
    :- CheckLength(bs, IntTooLarge(n));
    Success(View.OfBytes(bs))
  }

  function Number(dec: AST.Decimal): Result<jnumber> {
    var minus: jminus := Sign(dec.n);
    var num: jnum :- Int(Math.Abs(dec.n));
    var frac: Maybe<jexp> := Empty();
    var exp: jexp :-
      var e: je := View.OfBytes(['e' as byte]);
      var sign: jsign := Sign(dec.e10);
      var num: jnum :- Int(Math.Abs(dec.e10));
      Success(JExp(e, sign, num));
    Success(JNumber(minus, num, Empty, NonEmpty(exp)))
  }

  function MkStructural<T>(v: T): Structural<T> {
    Structural(EMPTY, v, EMPTY)
  }

  const COLON: Structural<jcolon> :=
    MkStructural(Grammar.COLON)

  function KV(kv: (string, AST.JSON)): Result<jkv> {
    var k :- String(kv.0);
    var v :- Value(kv.1);
    Success(Grammar.KV(k, COLON, v))
  }

  function MkSuffixedSequence<D, S>(ds: seq<D>, suffix: Structural<S>)
    : SuffixedSequence<D, S>
  {
    match |ds|
      case 0 => []
      case 1 => [Suffixed(ds[0], Empty)]
      case _ => [Suffixed(ds[0], NonEmpty(suffix))]
        + MkSuffixedSequence(ds[1..], suffix)
  }

  const COMMA: Structural<jcomma> :=
    MkStructural(Grammar.COMMA)

  function Object(obj: seq<(string, AST.JSON)>): Result<jobject> {
    var items :- Seq.MapWithResult(v requires v in obj => KV(v), obj);
    Success(Bracketed(MkStructural(LBRACE),
                      MkSuffixedSequence(items, COMMA),
                      MkStructural(RBRACE)))
  }


  function Array(arr: seq<AST.JSON>): Result<jarray> {
    var items :- Seq.MapWithResult(v requires v in arr => Value(v), arr);
    Success(Bracketed(MkStructural(LBRACKET),
                      MkSuffixedSequence(items, COMMA),
                      MkStructural(RBRACKET)))
  }

  function Value(js: AST.JSON): Result<Grammar.Value> {
    match js
      case Null => Success(Grammar.Null(View.OfBytes(NULL)))
      case Bool(b) => Success(Grammar.Bool(Bool(b)))
      case String(str) => var s :- String(str); Success(Grammar.String(s))
      case Number(dec) => var n :- Number(dec); Success(Grammar.Number(n))
      case Object(obj) => var o :- Object(obj); Success(Grammar.Object(o))
      case Array(arr) => var a :- Array(arr); Success(Grammar.Array(a))
  }

  function JSON(js: AST.JSON): Result<Grammar.JSON> {
    var val :- Value(js);
    Success(MkStructural(val))
  }
}
