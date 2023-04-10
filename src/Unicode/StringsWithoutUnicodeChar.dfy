// RUN: %verify --unicode-char:false %s

include "Strings.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module Strings refines AbstractStrings {

  import Unicode
  import Utf8EncodingForm
  import Utf16EncodingForm 
  import Seq
  
  function ToUTF8(s: string): Option<seq<uint8>> {
    var asCodeUnits := Seq.Map(c => c as Utf16EncodingForm.CodeUnit, s);
    var utf32 :- Utf16EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asUtf8CodeUnits := Utf8EncodingForm.EncodeScalarSequence(utf32);
    var asBytes := Seq.Map(cu => cu as uint8, asUtf8CodeUnits);
    Some(asBytes)
  }

  function FromUTF8(bs: seq<uint8>): Option<string> {
    var asCodeUnits := Seq.Map(c => c as Utf8EncodingForm.CodeUnit, bs);
    var utf32 :- Utf8EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asUtf16CodeUnits := Utf16EncodingForm.EncodeScalarSequence(utf32);
    var asChars := Seq.Map(cu => cu as char, asUtf16CodeUnits);
    Some(asChars)
  }
}