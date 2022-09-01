/// =============================================
///  Serialization from AST.JSON to bytes (Spec)
/// =============================================
///
/// This is the high-level spec.  For the implementation, see
/// ``JSON.Serializer.dfy``.

include "../BoundedInts.dfy"

include "JSON.AST.dfy"
include "UtfUtils.dfy"
include "Str.dfy"

module {:options "/functionSyntax:4"} JSON.Spec {
  import opened BoundedInts

  import opened Str
  import opened AST
  import opened UtfUtils

  type bytes = seq<uint8>

  function String(str: string): bytes {
    Str.ToBytes("'") + Transcode16To8(Str.EscapeQuotes(str)) + Str.ToBytes("'")
  }

  function Number(dec: Decimal): bytes {
    Transcode16To8(Str.OfInt(dec.n)) + Str.ToBytes("e") + Transcode16To8(Str.OfInt(dec.e10))
  }

  function KV(kv: (string, JSON)): bytes {
    String(kv.0) + Str.ToBytes(", ") + JSON(kv.1)
  }

  function Join(sep: bytes, items: seq<bytes>): bytes {
    if |items| == 0 then []
    else if |items| == 1 then items[0]
    else items[0] + sep + Join(sep, items[1..])
  }

  function Object(obj: seq<(string, JSON)>): bytes {
    Str.ToBytes("{") +
    Join(Str.ToBytes(","), seq(|obj|, i requires 0 <= i < |obj| => KV(obj[i]))) +
    Str.ToBytes("}")
  }

  function Array(arr: seq<JSON>): bytes {
    Str.ToBytes("[") +
    Join(Str.ToBytes(","), seq(|arr|, i requires 0 <= i < |arr| => JSON(arr[i]))) +
    Str.ToBytes("]")
  }

  function JSON(js: JSON): bytes {
    match js
      case Null => Str.ToBytes("null")
      case Bool(b) => if b then Str.ToBytes("true") else Str.ToBytes("false")
      case String(str) => String(str)
      case Number(dec) => Number(dec)
      case Object(obj) => Object(obj)
      case Array(arr) => Array(arr)
  }
}
