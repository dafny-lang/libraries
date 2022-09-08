// RUN: %dafny /compile:0 "%s"

module BoundedInts {
  const TWO_TO_THE_0:   int := 1

  const TWO_TO_THE_1:   int := 2
  const TWO_TO_THE_2:   int := 4
  const TWO_TO_THE_4:   int := 16
  const TWO_TO_THE_5:   int := 32
  const TWO_TO_THE_8:   int := 0x100
  const TWO_TO_THE_16:  int := 0x10000
  const TWO_TO_THE_24:  int := 0x1000000
  const TWO_TO_THE_32:  int := 0x1_00000000
  const TWO_TO_THE_40:  int := 0x100_00000000
  const TWO_TO_THE_48:  int := 0x10000_00000000
  const TWO_TO_THE_56:  int := 0x1000000_00000000
  const TWO_TO_THE_64:  int := 0x1_00000000_00000000
  const TWO_TO_THE_128: int := 0x1_00000000_00000000_00000000_00000000
  const TWO_TO_THE_256: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
  const TWO_TO_THE_512: int :=
  0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000;

  newtype uint8 = x: int  | 0 <= x < TWO_TO_THE_8
  newtype uint16 = x: int | 0 <= x < TWO_TO_THE_16
  newtype uint32 = x: int | 0 <= x < TWO_TO_THE_32
  newtype uint64 = x: int | 0 <= x < TWO_TO_THE_64

  newtype int8 = x: int   | -0x80 <= x < 0x80
  newtype int16 = x: int  | -0x8000 <= x < 0x8000
  newtype int32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
  newtype int64 = x: int  | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

  newtype nat8 = x: int   | 0 <= x < 0x80
  newtype nat16 = x: int  | 0 <= x < 0x8000
  newtype nat32 = x: int  | 0 <= x < 0x8000_0000
  newtype nat64 = x: int  | 0 <= x < 0x8000_0000_0000_0000
   
  newtype posInt64 = x | 0 < x < 0x8000_0000_0000_0000 witness 1

  const UINT8_MAX:  uint8  := 0xFF
  const UINT16_MAX: uint16 := 0xFFFF
  const UINT32_MAX: uint32 := 0xFFFF_FFFF
  const UINT64_MAX: uint64 := 0xFFFF_FFFF_FFFF_FFFF

  const INT8_MIN:  int8  := -0x80
  const INT8_MAX:  int8  :=  0x7F
  const INT16_MIN: int16 := -0x8000
  const INT16_MAX: int16 :=  0x7FFF
  const INT32_MIN: int32 := -0x8000_0000
  const INT32_MAX: int32 :=  0x7FFFFFFF
  const INT64_MIN: int64 := -0x8000_0000_0000_0000
  const INT64_MAX: int64 :=  0x7FFFFFFF_FFFFFFFF

  const NAT8_MAX:  nat8  := 0x7F
  const NAT16_MAX: nat16 := 0x7FFF
  const NAT32_MAX: nat32 := 0x7FFFFFFF
  const NAT64_MAX: nat64 := 0x7FFFFFFF_FFFFFFFF

  const UINT16_LIMIT := 0x1_0000
  const UINT32_LIMIT := 0x1_0000_0000
  const UINT64_LIMIT := 0x1_0000_0000_0000_0000
  const INT32_MAX_LIMIT := 0x8000_0000
  const INT64_MAX_LIMIT := 0x8000_0000_0000_0000

  type byte = uint8
  type bytes = seq<byte>
  newtype opt_byte = c: int | -1 <= c < TWO_TO_THE_8

  predicate method UInt8Less(a: uint8, b: uint8) { a < b }

  predicate method HasUint16Len<T>(s: seq<T>) {
    |s| < UINT16_LIMIT
  }

  type seq16<T> = s: seq<T> | HasUint16Len(s)
  type Uint8Seq16 = seq16<uint8>

  predicate method HasUint32Len<T>(s: seq<T>) {
    |s| < UINT32_LIMIT
  }

  type seq32<T> = s: seq<T> | HasUint32Len(s)
  type Uint8Seq32 = seq32<uint8>

  predicate method HasUint64Len<T>(s: seq<T>) {
    |s| < UINT64_LIMIT
  }

  type seq64<T> = s: seq<T> | HasUint64Len(s)
  type Uint8Seq64 = seq64<uint8>

  function method UInt16ToSeq(x: uint16): (ret: seq<uint8>)
    ensures |ret| == 2
    ensures 0x100 * ret[0] as uint16 + ret[1] as uint16 == x
  {
    var b0 := (x / 0x100) as uint8;
    var b1 := (x % 0x100) as uint8;
    [b0, b1]
  }

  function method SeqToUInt16(s: seq<uint8>): (x: uint16)
    requires |s| == 2
    ensures UInt16ToSeq(x) == s
    ensures x >= 0
  {
    var x0 := s[0] as uint16 * 0x100;
    x0 + s[1] as uint16
  }

  lemma UInt16SeqSerializeDeserialize(x: uint16)
    ensures SeqToUInt16(UInt16ToSeq(x)) == x
  {}

  lemma UInt16SeqDeserializeSerialize(s: seq<uint8>)
    requires |s| == 2
    ensures UInt16ToSeq(SeqToUInt16(s)) == s
  {}

  function method UInt32ToSeq(x: uint32): (ret: seq<uint8>)
    ensures |ret| == 4
    ensures 0x100_0000 * ret[0] as uint32 + 0x1_0000 * ret[1] as uint32 + 0x100 * ret[2] as uint32 + ret[3] as uint32 == x
  {
    var b0 := (x / 0x100_0000) as uint8;
    var x0 := x - (b0 as uint32 * 0x100_0000);

    var b1 := (x0 / 0x1_0000) as uint8;
    var x1 := x0 - (b1 as uint32 * 0x1_0000);

    var b2 := (x1 / 0x100) as uint8;
    var b3 := (x1 % 0x100) as uint8;
    [b0, b1, b2, b3]
  }

  function method SeqToUInt32(s: seq<uint8>): (x: uint32)
    requires |s| == 4
    ensures UInt32ToSeq(x) == s
  {
    var x0 := s[0] as uint32 * 0x100_0000;
    var x1 := x0 + s[1] as uint32 * 0x1_0000;
    var x2 := x1 + s[2] as uint32 * 0x100;
    x2 + s[3] as uint32
  }

  lemma UInt32SeqSerializeDeserialize(x: uint32)
    ensures SeqToUInt32(UInt32ToSeq(x)) == x
  {}

  lemma UInt32SeqDeserializeSerialize(s: seq<uint8>)
    requires |s| == 4
    ensures UInt32ToSeq(SeqToUInt32(s)) == s
  {}

  function method UInt64ToSeq(x: uint64): (ret: seq<uint8>)
    ensures |ret| == 8
    ensures 0x100_0000_0000_0000 * ret[0] as uint64 + 0x1_0000_0000_0000 * ret[1] as uint64 +
      0x100_0000_0000 * ret[2] as uint64 + 0x1_0000_0000 * ret[3] as uint64 + 0x100_0000 * ret[4] as uint64 +
      0x1_0000 * ret[5] as uint64 + 0x100 * ret[6] as uint64 + ret[7] as uint64 == x
  {
    var b0 := (x / 0x100_0000_0000_0000) as uint8;
    var x0 := x - (b0 as uint64 * 0x100_0000_0000_0000);

    var b1 := (x0 / 0x1_0000_0000_0000) as uint8;
    var x1 := x0 - (b1 as uint64 * 0x1_0000_0000_0000);

    var b2 := (x1 / 0x100_0000_0000) as uint8;
    var x2 := x1 - (b2 as uint64 * 0x100_0000_0000);

    var b3 := (x2 / 0x1_0000_0000) as uint8;
    var x3 := x2 - (b3 as uint64 * 0x1_0000_0000);

    var b4 := (x3 / 0x100_0000) as uint8;
    var x4 := x3 - (b4 as uint64 * 0x100_0000);

    var b5 := (x4 / 0x1_0000) as uint8;
    var x5 := x4 - (b5 as uint64 * 0x1_0000);

    var b6 := (x5 / 0x100) as uint8;
    var b7 := (x5 % 0x100) as uint8;
    [b0, b1, b2, b3, b4, b5, b6, b7]
  }

  function method SeqToUInt64(s: seq<uint8>): (x: uint64)
    requires |s| == 8
    ensures UInt64ToSeq(x) == s
  {
    var x0 := s[0] as uint64 * 0x100_0000_0000_0000;
    var x1 := x0 + s[1] as uint64 * 0x1_0000_0000_0000;
    var x2 := x1 + s[2] as uint64 * 0x100_0000_0000;
    var x3 := x2 + s[3] as uint64 * 0x1_0000_0000;
    var x4 := x3 + s[4] as uint64 * 0x100_0000;
    var x5 := x4 + s[5] as uint64 * 0x1_0000;
    var x6 := x5 + s[6] as uint64 * 0x100;
    var x := x6 + s[7] as uint64;
    UInt64SeqSerialize(x, s);
    x
  }

  lemma UInt64SeqSerialize(x: uint64, s: seq<uint8>)
    requires |s| == 8
    requires 0x100_0000_0000_0000 * s[0] as uint64
      + 0x1_0000_0000_0000 * s[1] as uint64
      + 0x100_0000_0000 * s[2] as uint64
      + 0x1_0000_0000 * s[3] as uint64
      + 0x100_0000 * s[4] as uint64
      + 0x1_0000 * s[5] as uint64
      + 0x100 * s[6] as uint64
      + s[7] as uint64 == x
    ensures UInt64ToSeq(x) == s
  {
    calc {
      UInt64ToSeq(x);
    ==
      UInt64ToSeq(s[0] as uint64 * 0x100_0000_0000_0000
      + s[1] as uint64 * 0x1_0000_0000_0000
      + s[2] as uint64 * 0x100_0000_0000
      + s[3] as uint64 * 0x1_0000_0000
      + s[4] as uint64 * 0x100_0000
      + s[5] as uint64 * 0x1_0000
      + s[6] as uint64 * 0x100
      + s[7] as uint64);
    ==
      var b0 := ((s[0] as uint64 * 0x100_0000_0000_0000
        + s[1] as uint64 * 0x1_0000_0000_0000
        + s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64) / 0x100_0000_0000_0000) as uint8;
      assert b0 == s[0];
      var x0 := (s[0] as uint64 * 0x100_0000_0000_0000
        + s[1] as uint64 * 0x1_0000_0000_0000
        + s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64) - (b0 as uint64 * 0x100_0000_0000_0000);
      assert x0 == (s[1] as uint64 * 0x1_0000_0000_0000
        + s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b1 := (x0 / 0x1_0000_0000_0000) as uint8;
      assert b1 == s[1];
      var x1 := x0 - (b1 as uint64 * 0x1_0000_0000_0000);
      assert x1 == (s[2] as uint64 * 0x100_0000_0000
        + s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b2 := (x1 / 0x100_0000_0000) as uint8;
      assert b2 == s[2];
      var x2 := x1 - (b2 as uint64 * 0x100_0000_0000);
      assert x2 == (s[3] as uint64 * 0x1_0000_0000
        + s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b3 := (x2 / 0x1_0000_0000) as uint8;
      assert b3 == s[3];
      var x3 := x2 - (b3 as uint64 * 0x1_0000_0000);
      assert x3 == (s[4] as uint64 * 0x100_0000
        + s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b4 := (x3 / 0x100_0000) as uint8;
      assert b4 == s[4];
      var x4 := x3 - (b4 as uint64 * 0x100_0000);
      assert x4 == (s[5] as uint64 * 0x1_0000
        + s[6] as uint64 * 0x100
        + s[7] as uint64);

      var b5 := (x4 / 0x1_0000) as uint8;
      assert b5 == s[5];
      var x5 := x4 - (b5 as uint64 * 0x1_0000);
      assert x5 == (s[6] as uint64 * 0x100 + s[7] as uint64);

      var b6 := (x5 / 0x100) as uint8;
      assert b6 == s[6];
      var b7 := (x5 % 0x100) as uint8;
      assert b7 == s[7];
      [b0, b1, b2, b3, b4, b5, b6, b7];
    ==
      [s[0], s[1], s[2], s[3], s[4], s[5], s[6], s[7]];
    ==
      s;
    }
  }

  lemma UInt64SeqSerializeDeserialize(x: uint64)
    ensures SeqToUInt64(UInt64ToSeq(x)) == x
  {}

  lemma UInt64SeqDeserializeSerialize(s: seq<uint8>)
    requires |s| == 8
    ensures UInt64ToSeq(SeqToUInt64(s)) == s
  {}

  function SeqToNat(s: seq<uint8>): nat {
    if s == [] then
      0
    else
      var finalIndex := |s| - 1;
      SeqToNat(s[..finalIndex]) * 0x100 + s[finalIndex] as nat
  }

  // By the following lemma, prepending a 0 to a byte sequence does not change its SeqToNat value
  lemma SeqToNatZeroPrefix(s: seq<uint8>)
    ensures SeqToNat(s) == SeqToNat([0] + s)
  {
    if s == [] {
    } else {
      var s' := [0] + s;
      var sLength := |s|;
      var sFinalIndex := sLength - 1;
      calc {
        SeqToNat(s);
      ==
        SeqToNat(s[..sFinalIndex]) * 0x100 + s[sFinalIndex] as nat;
      ==
        SeqToNat([0] + s[..sFinalIndex]) * 0x100 + s[sFinalIndex] as nat;
      == { assert (s'[..sLength] == [0] + s[..sFinalIndex]) && s'[sLength] == s[sFinalIndex]; }
        SeqToNat(s'[..sLength]) * 0x100 + s'[sLength] as nat;
      ==
        SeqToNat(s');
      ==
        SeqToNat([0] + s);
      }
    }
  }

  // By the following lemma, SeqToNat(s) == n is automatically true if the given preconditions are true
  lemma SeqWithUInt32Suffix(s: seq<uint8>, n: nat)
    requires n < UINT32_LIMIT
    requires 4 <= |s|
    requires var suffixStartIndex := |s| - 4;
      (s[suffixStartIndex..] == UInt32ToSeq(n as uint32)) &&
      (forall i :: 0 <= i < suffixStartIndex ==> s[i] == 0)
    ensures SeqToNat(s) == n
  {
    if |s| == 4 {
      calc {
        SeqToNat(s);
      ==
        SeqToNat(s[..3])
          * 0x100 + s[3] as nat;
      ==  { assert s[..3][..2] == s[..2] && s[..3][2] == s[2]; }
        (SeqToNat(s[..2])
          * 0x100 + s[2] as nat)
          * 0x100 + s[3] as nat;
      ==  { assert s[..2][..1] == s[..1] && s[..2][1] == s[1]; }
        ((SeqToNat(s[..1])
          * 0x100 + s[1] as nat)
          * 0x100 + s[2] as nat)
          * 0x100 + s[3] as nat;
      ==  { assert s[..1][..0] == s[..0] && s[..1][0] == s[0]; }
        (((SeqToNat(s[..0])
          * 0x100 + s[0] as nat)
          * 0x100 + s[1] as nat)
          * 0x100 + s[2] as nat)
          * 0x100 + s[3] as nat;
      ==
        n;
      }
    } else {
      assert s == [0] + s[1..];
      SeqToNatZeroPrefix(s[1..]);
      SeqWithUInt32Suffix(s[1..], n);
    }
  }


}
