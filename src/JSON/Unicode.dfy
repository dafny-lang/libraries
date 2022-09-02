include "../BoundedInts.dfy"

module {:options "/functionSyntax:4"} JSON.Unicode {
  import opened BoundedInts

  function Utf16Decode1(c: uint16): uint32
    requires c < 0xD800 || 0xDBFF < c
  {
    c as uint32
  }

  function Utf16Decode2(c0: uint16, c1: uint16): uint32
    requires 0xD800 <= c0 as int <= 0xDBFF
  {
    (0x10000
     + ((((c0 as bv32) & 0x03FF) << 10)
       | ((c1 as bv32) & 0x03FF)))
    as uint32
  }

  newtype opt_uint16 = c: int | -1 <= c as int < TWO_TO_THE_16

  function Utf16DecodeChars(c0: uint16, c1: opt_uint16): (r: (uint32, uint8))
    ensures r.1 in {1, 2}
    ensures c1 == -1 ==> r.1 == 1
  {
    if c0 < 0xD800 || 0xDBFF < c0 then
      (Utf16Decode1(c0), 1)
    else if c1 >= 0 then
      (Utf16Decode2(c0, c1 as uint16), 2)
    else
      (0xFFFD, 1) // Replacement character
  }

  function Utf16Decode(str: string, start: nat := 0): seq<uint32>
    decreases |str| - start
  {
    if start >= |str| then []
    else
      var c0 := str[start] as uint16;
      var c1 := if |str| > start + 1 then str[start + 1] as opt_uint16 else -1;
      var (cp, delta) := Utf16DecodeChars(c0, c1);
      [cp] + Utf16Decode(str, start + delta as nat)
  }

  function Utf16Encode2(cp: uint32): seq<char>
    requires cp < 0x100000
  {
    var bv := cp as bv32;
    [(0xD800 | (bv >> 10))     as char,
     (0xDC00 | (bv  & 0x03FF)) as char]
  }

  function Utf16Encode1(cp: uint32): seq<char> {
    if cp < 0xD800 || 0xDBFF < cp < 0x10000 then
      [cp as char]
    else if 0x10000 <= cp < 0x110000 then
      Utf16Encode2(cp - 0x10000)
    else
      [] // Invalid: drop // TODO
  }

  function Utf16Encode(codepoints: seq<uint32>, start: nat := 0): seq<char>
    decreases |codepoints| - start
  {
    if start >= |codepoints| then []
    else Utf16Encode1(codepoints[start]) + Utf16Encode(codepoints, start + 1)
  }

  function Utf8Encode1(cp: uint32): seq<uint8> {
    var bv := cp as bv32;
    if cp < 0x80 then
      [cp as uint8]
    else if cp < 0x0800 then
      [(((bv >>  6) & 0x1F) | 0xC0) as uint8,
       ( (bv        & 0x3F) | 0x80) as uint8]
    else if cp < 0x10000 then
      [(((bv >> 12) & 0x0F) | 0xE0) as uint8,
       (((bv >>  6) & 0x3F) | 0x80) as uint8,
       ( (bv        & 0x3F) | 0x80) as uint8]
    else if cp < 0x110000 then
      [(((bv >> 18) & 0x07) | 0xF0) as uint8,
       (((bv >> 12) & 0x3F) | 0x80) as uint8,
       (((bv >>  6) & 0x3F) | 0x80) as uint8,
       ( (bv        & 0x3F) | 0x80) as uint8]
    else
      [] // Invalid: drop // TODO
  }

  newtype opt_uint8 = c: int | -1 <= c as int < TWO_TO_THE_8

  function Utf8DecodeChars(c0: uint8, c1: opt_uint8, c2: opt_uint8, c3: opt_uint8): (r: (uint32, uint8))
    ensures r.1 in {1, 2, 3, 4}
    ensures c1 == -1 ==> r.1 <= 1
    ensures c2 == -1 ==> r.1 <= 2
    ensures c3 == -1 ==> r.1 <= 3
  {
    if (c0 as bv32 & 0x80) == 0 then
      (c0 as uint32, 1)
    else if (c0 as bv32 & 0xE0) == 0xC0 && c1 > -1 then
	    (( (((c0 as bv32) & 0x1F) <<  6)
	      | ((c1 as bv32) & 0x3F       )) as uint32,
       2)
    else if (c0 as bv32 & 0xF0) == 0xE0 && c1 > -1 && c2 > -1 then
      ((  (((c0 as bv32) & 0x0F) << 12)
        | (((c1 as bv32) & 0x3F) <<  6)
        | ( (c2 as bv32) & 0x3F       )) as uint32,
       3)
    else if (c0 as bv32 & 0xF8) == 0xF0 && c1 > -1 && c2 > -1 && c3 > -1 then
      ((  (((c0 as bv32) & 0x07) << 18)
        | (((c1 as bv32) & 0x3F) << 12)
        | (((c2 as bv32) & 0x3F) <<  6)
        | ( (c3 as bv32) & 0x3F       )) as uint32,
       4)
    else
      (0xFFFD, 1) // Replacement character
  }

  function Utf8Decode(str: seq<uint8>, start: nat := 0): seq<uint32>
    decreases |str| - start
  {
    if start >= |str| then []
    else
      var c0 := str[start] as uint8;
      var c1 := if |str| > start + 1 then str[start + 1] as opt_uint8 else -1;
      var c2 := if |str| > start + 2 then str[start + 2] as opt_uint8 else -1;
      var c3 := if |str| > start + 3 then str[start + 3] as opt_uint8 else -1;
      var (cp, delta) := Utf8DecodeChars(c0, c1, c2, c3);
      [cp] + Utf8Decode(str, start + delta as nat)
  }

  function Utf8Encode(codepoints: seq<uint32>, start: nat := 0): seq<uint8>
    decreases |codepoints| - start
  {
    if start >= |codepoints| then []
    else Utf8Encode1(codepoints[start]) + Utf8Encode(codepoints, start + 1)
  }

  function Transcode16To8(s: string): seq<uint8> {
    Utf8Encode(Utf16Decode(s))
  }

  function Transcode8To16(s: seq<uint8>): string {
    Utf16Encode(Utf8Decode(s))
  }
}
