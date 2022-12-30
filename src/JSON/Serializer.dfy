// RUN: %dafny -compile:0 "%s"

/// =============================================
///  Serialization from JSON.AST to JSON.Grammar
/// =============================================
///
/// For the spec, see ``JSON.Spec.dfy``.

include "../Collections/Sequences/Seq.dfy"
include "../BoundedInts.dfy"
include "../Math.dfy"

include "Utils/Views.dfy"
include "Utils/Vectors.dfy"
include "Utils/Unicode.dfy"
include "Errors.dfy"
include "AST.dfy"
include "Grammar.dfy"
include "Spec.dfy"

module {:options "-functionSyntax:4"} JSON.Serializer {
  import Seq
  import Math
  import opened Wrappers
  import opened BoundedInts
  import opened Utils.Str
  import Utils.Unicode

  import AST
  import Spec
  import opened Errors
  import opened Utils.Vectors
  import opened Grammar
  import opened Utils.Views.Core

  type Result<+T> = SerializationResult<T>

  type bytes = seq<uint8>
  type bytes32 = bs: bytes | |bs| < TWO_TO_THE_32
  type string32 = s: string | |s| < TWO_TO_THE_32

  function Bool(b: bool): jbool {
    View.OfBytes(if b then TRUE else FALSE)
  }

  function Transcode16To8Escaped(str: string, start: uint32 := 0): bytes {
    Unicode.Transcode16To8(Spec.Escape(str))
  } // FIXME speed up using a `by method`
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
  //       Utf8Encode(st, Unicode.Utf16Decode1(c0));
  //       idx := idx +1;
  //     } else {
  //       Utf8Encode(st, Unicode.Utf16Decode2(c0, c1));
  //       idx := idx + 2;
  //     }
  //   }
  // }

  function CheckLength<T>(s: seq<T>, err: SerializationError): Outcome<SerializationError> {
    Need(|s| < TWO_TO_THE_32, err)
  }

  function String(str: string): Result<jstring> {
    var bs := Transcode16To8Escaped(str);
    :- CheckLength(bs, StringTooLong(str));
    Success(Grammar.JString(Grammar.DOUBLEQUOTE, View.OfBytes(bs), Grammar.DOUBLEQUOTE))
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
    var frac: Maybe<jfrac> := Empty();
    var exp: Maybe<jexp> :-
      if dec.e10 == 0 then
        Success(Empty())
      else
        var e: je := View.OfBytes(['e' as byte]);
        var sign: jsign := Sign(dec.e10);
        var num: jnum :- Int(Math.Abs(dec.e10));
        Success(NonEmpty(JExp(e, sign, num)));
    Success(JNumber(minus, num, Empty, exp))
  }

  function MkStructural<T>(v: T): Structural<T> {
    Structural(EMPTY, v, EMPTY)
  }

  const COLON: Structural<jcolon> :=
    MkStructural(Grammar.COLON)

  function KeyValue(kv: (string, AST.JSON)): Result<jKeyValue> {
    var k :- String(kv.0);
    var v :- Value(kv.1);
    Success(Grammar.KeyValue(k, COLON, v))
  }

  function MkSuffixedSequence<D, S>(ds: seq<D>, suffix: Structural<S>, start: nat := 0)
    : SuffixedSequence<D, S>
    decreases |ds| - start
  {
    if start >= |ds| then []
    else if start == |ds| - 1 then [Suffixed(ds[start], Empty)]
    else [Suffixed(ds[start], NonEmpty(suffix))] + MkSuffixedSequence(ds, suffix, start + 1)
  }

  const COMMA: Structural<jcomma> :=
    MkStructural(Grammar.COMMA)

  function Object(obj: seq<(string, AST.JSON)>): Result<jobject> {
    var items :- Seq.MapWithResult(v requires v in obj => KeyValue(v), obj);
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
