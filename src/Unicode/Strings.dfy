

// RUN: %verify %s

include "../BoundedInts.dfy"
include "../Wrappers.dfy"
include "Utf8EncodingForm.dfy"
include "Utf16EncodingForm.dfy"

abstract module AbstractStrings {

  import opened Wrappers
  import opened BoundedInts

  function ToUTF8(s: string): Option<seq<uint8>>

  function FromUTF8(bs: seq<uint8>): Option<string>
}