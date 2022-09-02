/// =============================================
///  Serialization from AST.JSON to bytes (Spec)
/// =============================================
///
/// This is the high-level spec.  For the implementation, see
/// ``JSON.Serializer.dfy``.

include "../BoundedInts.dfy"

include "JSON.AST.dfy"
include "Unicode.dfy"
include "Str.dfy"

module {:options "/functionSyntax:4"} JSON.Spec {
  import opened BoundedInts

  import opened Str
  import opened AST
  import opened Unicode

  type bytes = seq<uint8>

  function EscapeUnicode(c: uint16): string {
    var s := Str.OfNat(c as nat, 16);
    assert |s| <= 4 by {
      assert c as nat <= 0xFFFF;
      assert Math.IntLog(16, c as nat) <= Math.IntLog(16, 0xFFFF) by {
        Math.IntLog_Increasing(16, c as nat, 0xFFFF);
      }
      assert Math.IntLog(16, 0xFFFF) == 3 by { reveal Math.IntLog(); }
    }
    s + seq(4 - |s|, _ => ' ')
  }

  function Escape(str: string, start: nat := 0): string
    decreases |str| - start
  {
    if start >= |str| then []
    else
      (match str[start] as uint16
         case 0x22 => "\\\"" // quotation mark
         case 0x5C => "\\\\"  // reverse solidus
         case 0x08 => "\\b"  // backspace
         case 0x0C => "\\f"  // form feed
         case 0x0A => "\\n"  // line feed
         case 0x0D => "\\r"  // carriage return
         case 0x09 => "\\t"  // tab
         case c =>
           if c < 0x001F then "\\u" + EscapeUnicode(c)
           else [str[start]])
      + Escape(str, start + 1)
  }

  function String(str: string): bytes {
    Str.ToBytes("\"") + Transcode16To8(Escape(str)) + Str.ToBytes("\"")
  }

  function Number(dec: Decimal): bytes {
    Transcode16To8(Str.OfInt(dec.n)) +
      (if dec.e10 == 0 then []
       else Str.ToBytes("e") + Transcode16To8(Str.OfInt(dec.e10)))
  }

  function KV(kv: (string, JSON)): bytes {
    String(kv.0) + Str.ToBytes(":") + JSON(kv.1)
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
