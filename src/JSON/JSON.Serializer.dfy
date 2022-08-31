/// =============================================
///  Serialization from JSON.AST to JSON.Grammar
/// =============================================
///
/// For the spec, see ``JSON.Spec.HighLevel.dfy``.

include "../Collections/Sequences/Seq.dfy"
include "../BoundedInts.dfy"
include "../Math.dfy"

include "Views.dfy"
include "Vectors.dfy"
include "UtfUtils.dfy"
include "JSON.AST.dfy"
include "JSON.Grammar.dfy"
include "JSON.Spec.HighLevel.dfy"
include "JSON.Spec.LowLevel.dfy"

module {:options "-functionSyntax:4"} JSON.Serializer {
  import Seq
  import Math
  import opened BoundedInts
  import opened Str
  import UtfUtils

  import AST
  import Spec.HighLevel
  import opened Vectors
  import opened Grammar
  import opened Views.Core

  type bytes = seq<uint8>
  type string32 = s: string | |s| < TWO_TO_THE_32

  function Bool(b: bool): jbool {
    View.OfBytes(if b then TRUE else FALSE)
  }

  method Utf8Encode(st: Vector<uint8>, cp: uint32)
    ensures st.Model()
  {

  }

  function Transcode16To8Escaped(str: string32, start: uint32 := 0): seq<uint8> {
    UtfUtils.Transcode16To8(HighLevel.Escape(str))
  } by method {
    var len := |str| as uint32;
    if len == 0 {
      return [];
    }
    var st := new Vectors.Vector(0, len);
    var c0: uint16 := 0;
    var c1: uint16 := str[0] as uint16;
    var idx: uint32 := 0;
    while idx < len {
      var c0 := c1;
      var c1 := str[idx + 1] as uint16;
      if c0 < 0xD800 || c0 > 0xDBFF {
        Utf8Encode(st, UtfUtils.Utf16Decode1(c0));
        idx := idx +1;
      } else {
        Utf8Encode(st, UtfUtils.Utf16Decode2(c0, c1));
        idx := idx + 2;
      }
    }
  }





  function String(str: string): jstring {
    Transcode16To8Escaped(str)
  }

  function Sign(n: int): jminus {
    View.OfBytes(if n < 0 then ['-' as byte] else [])
  }

  function Number(dec: AST.Decimal): jnumber {
    var minus: jminus := Sign(dec.n);
    var num: jnum := View.OfBytes(Str.OfInt(Math.Abs(dec.n))); // FIXME
    var frac: Maybe<jexp> := Empty();
    var exp: jexp :=
      var e: je := View.OfBytes(['e' as byte]);
      var sign: jsign := Sign(dec.e10);
      var num: jnum := View.OfBytes(Str.OfInt(Math.Abs(dec.e10)));
      JExp(e, sign, num);
    JNumber(minus, num, Empty, NonEmpty(exp))
  }

  function KV(kv: AST.KV): Suffixed<jkv, jcomma> {
    String(kv.k) + Bytes(", ") + Value(kv.v)
  }

  function MkStructural(v: View): Structural<View> {
    Structural(EMPTY, v, EMPTY)
  }

  function Object(obj: seq<AST.KV>): jobject {
    Bracketed(MkStructural(LBRACE), [], MkStructural(RBRACE))
    // Bytes("{") + Join(Bytes(","), Seq.Map(kv requires kv in obj => KV(kv), obj)) + Bytes("}")
  }

  function Array(arr: seq<AST.Value>): jarray {
    Bracketed(MkStructural(LBRACKET), [], MkStructural(RBRACKET))
    // Bytes("[") + Join(Bytes(","), Seq.Map(v requires v in arr => Value(v), arr)) + Bytes("]")
  }

  function Value(js: AST.Value): Value {
    match js
      case Null => Grammar.Null(View.OfBytes(NULL))
      case Bool(b) => Grammar.Bool(Bool(b))
      case String(str) => Grammar.String(String(str))
      case Number(dec) => Grammar.Number(Number(dec))
      case Object(obj) => Grammar.Object(Object(obj))
      case Array(arr) => Grammar.Array(Array(arr))
  }
}
