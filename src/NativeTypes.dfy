// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module NativeTypes {
  const BASE_0:   int := 1

  const BASE_1:   int := 2
  const BASE_2:   int := 4
  const BASE_4:   int := 16
  const BASE_5:   int := 32
  const BASE_8:   int := 0x1_00
  const BASE_16:  int := 0x1_0000
  const BASE_24:  int := 0x1_000000
  const BASE_32:  int := 0x1_00000000
  const BASE_40:  int := 0x1_00000000_00
  const BASE_48:  int := 0x1_00000000_0000
  const BASE_56:  int := 0x1_00000000_000000
  const BASE_64:  int := 0x1_00000000_00000000
  const BASE_128: int := 0x1_00000000_00000000_00000000_00000000
  const BASE_256: int := 0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000
  const BASE_512: int :=
  0x1_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000_00000000;

  newtype {:nativeType "byte"}    uint8 = x:int   | 0 <= x < 0x1_00
  newtype {:nativeType "ushort"}  uint16 = x: int | 0 <= x < 0x1_0000
  newtype {:nativeType "uint"}    uint32 = x: int | 0 <= x < 0x1_00000000
  newtype {:nativeType "ulong"}   uint64 = x: int | 0 <= x < 0x1_00000000_00000000

  newtype {:nativeType "sbyte"}   int8 = x: int   | -0x80 <= x < 0x80
  newtype {:nativeType "short"}   int16 = x: int  | -0x8000 <= x < 0x8000
  newtype {:nativeType "int"}     int32 = x: int  | -0x8000_0000 <= x < 0x8000_0000
  newtype {:nativeType "long"}    int64 = x: int  | -0x8000_0000_0000_0000 <= x < 0x8000_0000_0000_0000

  newtype {:nativeType "sbyte"}   nat8 = x: int   | 0 <= x < 0x80
  newtype {:nativeType "short"}   nat16 = x: int  | 0 <= x < 0x8000
  newtype {:nativeType "int"}     nat32 = x: int  | 0 <= x < 0x8000_0000
  newtype {:nativeType "long"}    nat64 = x: int  | 0 <= x < 0x8000_0000_0000_0000

}
