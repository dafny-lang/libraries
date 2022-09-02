/// =============================================
///  Serialization from AST.JSON to bytes (Spec)
/// =============================================
///
/// This is the high-level spec.  For the implementation, see
/// ``JSON.Serializer.dfy``.

include "../BoundedInts.dfy"
include "../NonlinearArithmetic/Logarithm.dfy"

include "AST.dfy"
include "Utils/Unicode.dfy"
include "Utils/Str.dfy"

module {:options "-functionSyntax:4"} JSON.Spec {
  import opened BoundedInts

  import opened Utils.Str
  import opened AST
  import opened Utils.Unicode
  import opened Logarithm

  type bytes = seq<uint8>

  function EscapeUnicode(c: uint16): string {
    var s := Str.OfNat(c as nat, 16);
    assert |s| <= 4 by {
      assert c as nat <= 0xFFFF;
      assert Log(16, c as nat) <= Log(16, 0xFFFF) by {
        LemmaLogIsOrdered(16, c as nat, 0xFFFF);
      }
      assert Log(16, 0xFFFF) == 3 by { reveal Log(); }
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

  function ToBytes(s: string) : seq<uint8>
    requires forall c: char | c in s :: c as int < 256
  {
    seq(|s|, i requires 0 <= i < |s| =>
      assert s[i] in s; s[i] as byte)
  }

  function String(str: string): bytes {
    ToBytes("\"") + Transcode16To8(Escape(str)) + ToBytes("\"")
  }

  function Number(dec: Decimal): bytes {
    Transcode16To8(Str.OfInt(dec.n)) +
      (if dec.e10 == 0 then []
       else ToBytes("e") + Transcode16To8(Str.OfInt(dec.e10)))
  }

  function KV(kv: (string, JSON)): bytes {
    String(kv.0) + ToBytes(":") + JSON(kv.1)
  }

  function Join(sep: bytes, items: seq<bytes>): bytes {
    if |items| == 0 then []
    else if |items| == 1 then items[0]
    else items[0] + sep + Join(sep, items[1..])
  }

  function Object(obj: seq<(string, JSON)>): bytes {
    ToBytes("{") +
    Join(ToBytes(","), seq(|obj|, i requires 0 <= i < |obj| => KV(obj[i]))) +
    ToBytes("}")
  }

  function Array(arr: seq<JSON>): bytes {
    ToBytes("[") +
    Join(ToBytes(","), seq(|arr|, i requires 0 <= i < |arr| => JSON(arr[i]))) +
    ToBytes("]")
  }

  function JSON(js: JSON): bytes {
    match js
      case Null => ToBytes("null")
      case Bool(b) => if b then ToBytes("true") else ToBytes("false")
      case String(str) => String(str)
      case Number(dec) => Number(dec)
      case Object(obj) => Object(obj)
      case Array(arr) => Array(arr)
  }
}
