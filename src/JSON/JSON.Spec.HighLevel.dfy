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

module {:options "-functionSyntax:4"} JSON.Spec.HighLevel {
  import opened BoundedInts

  import opened Str
  import opened AST
  import opened UtfUtils

  type bytes = seq<uint8>

  function Escape(str: string): string {
    if str == [] then []
    else
      (if str[0] == '\"' || str[0] == '\\' then ['\\', str[0]] else [str[0]])
      + Escape(str[1..])
  }

  function String(str: string): bytes {
    Str.ToBytes("'") + Transcode16To8(Escape(str)) + Str.ToBytes("'")
  }

  function Number(dec: Decimal): bytes {
    Transcode16To8(Str.OfInt(dec.n)) + Str.ToBytes("e") + Transcode16To8(Str.OfInt(dec.e10))
  }

  function KV(kv: KV): bytes {
    String(kv.k) + Str.ToBytes(", ") + Value(kv.v)
  }

  function Join(sep: bytes, items: seq<bytes>): bytes {
    if |items| == 0 then []
    else if |items| == 1 then items[0]
    else items[0] + sep + Join(sep, items[1..])
  }

  function Object(obj: seq<KV>): bytes {
    Str.ToBytes("{") +
    Join(Str.ToBytes(","), seq(|obj|, i requires 0 <= i < |obj| => KV(obj[i]))) +
    Str.ToBytes("}")
  }

  function Array(arr: seq<Value>): bytes {
    Str.ToBytes("[") +
    Join(Str.ToBytes(","), seq(|arr|, i requires 0 <= i < |arr| => Value(arr[i]))) +
    Str.ToBytes("]")
  }

  function Value(js: Value): seq<byte> {
    match js
      case Null => Str.ToBytes("null")
      case Bool(b: bool) => if b then Str.ToBytes("true") else Str.ToBytes("false")
      case String(str: string) => String(str)
      case Number(dec: Decimal) => Number(dec)
      case Object(obj: seq<KV>) => Object(obj)
      case Array(arr: seq<Value>) => Array(arr)
  }
}
