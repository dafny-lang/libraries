include "../BoundedInts.dfy"

module {:options "/functionSyntax:4"} UtfUtils {
  import opened BoundedInts

  function Utf16Decode1(c: uint16): uint32
    requires c < 0xD800 || c > 0xDBFF
  {
    c as uint32
  }

  function Utf16Decode2(c0: uint16, c1: uint16): uint32
    requires 0xD800 <= c0 as int <= 0xDBFF
  {
    (0x10000
      | (((c0 as bv32) & 0x03FF) << 10)
      |  ((c1 as bv32) & 0x03FF))
    as uint32
  }

  newtype opt_uint16 = c: int | -1 <= c as int < TWO_TO_THE_16

  function Utf16DecodeChars(c0: uint16, c1: opt_uint16): (r: (uint32, uint8))
    ensures r.1 in {1, 2}
    ensures c1 == -1 ==> r.1 == 1
  {
    if c0 < 0xD800 || c0 > 0xDBFF then
      (Utf16Decode1(c0), 1)
    else if c1 >= 0 then
      (Utf16Decode2(c0, c1 as uint16), 2)
    else
      (0xFFFD, 1)
  }

  function Utf16Decode(str: string): seq<uint32> {
    if str == [] then
      []
    else
      var c0 := str[0] as uint16;
      var c1 := if |str| > 1 then str[1] as opt_uint16 else -1;
      var (cp, delta) := Utf16DecodeChars(c0, c1);
      [cp] + Utf16Decode(str[delta..])
  }

   function Utf8Encode1(cp: uint32): seq<uint8> {
    var bv := cp as bv32;
    if cp < 0x80 then
      [cp as uint8]
    else if cp < 0x0800 then
      [( (bv >>  6) & 0x1F)         as uint8,
       ( (bv        & 0x3F) | 0x80) as uint8]
    else if cp < 0x10000 then
      [( (bv >> 12) & 0x0F)         as uint8,
       (((bv >>  6) & 0x3F) | 0x80) as uint8,
       ( (bv & 0x3F)        | 0x80) as uint8]
    else if cp < 0x110000 then
      [( (bv >> 18) & 0x07)         as uint8,
       (((bv >> 12) & 0x3F) | 0x80) as uint8,
       (((bv >>  6) & 0x3F) | 0x80) as uint8,
       ( (bv        & 0x3F) | 0x80) as uint8]
    else
      [] // Invalid: drop // TODO
  }

  function Utf8Encode(codepoints: seq<uint32>): seq<uint8> {
    if codepoints == [] then []
    else Utf8Encode1(codepoints[0]) + Utf8Encode(codepoints[1..])
  }

  function Transcode16To8(s: string): seq<uint8> {
    Utf8Encode(Utf16Decode(s))
  }
}
