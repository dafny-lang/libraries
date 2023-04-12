// RUN: %verify --unicode-char:false %s

include "UnicodeStrings.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module {:options "-functionSyntax:4"} UnicodeStrings refines AbstractUnicodeStrings {

  import Unicode
  import Utf8EncodingForm
  import Utf16EncodingForm 
  
  predicate IsWellFormedString(s: string)
    ensures |s| == 0 ==> IsWellFormedString(s) 
  {
    Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map(c => c as Utf16EncodingForm.CodeUnit, s)) 
  }

  function ToUTF8Checked(s: string): Option<seq<uint8>> {
    var asCodeUnits := Seq.Map(c => c as Utf16EncodingForm.CodeUnit, s);
    var utf32 :- Utf16EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asUtf8CodeUnits := Utf8EncodingForm.EncodeScalarSequence(utf32);
    Some(Utf8EncodingScheme.Serialize(asUtf8CodeUnits))
  }

  function {:vcs_split_on_every_assert} FromUTF8Checked(bs: seq<uint8>): Option<string> {
    var asCodeUnits := Seq.Map(c => c as Utf8EncodingForm.CodeUnit, bs);
    var utf32 :- Utf8EncodingForm.DecodeCodeUnitSequenceChecked(asCodeUnits);
    var asUtf16CodeUnits := Utf16EncodingForm.EncodeScalarSequence(utf32);
    var asChars := Seq.Map(cu => cu as char, asUtf16CodeUnits);
    assert Seq.Map(c => c as Utf16EncodingForm.CodeUnit, asChars) == asUtf16CodeUnits;
    assert Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map(c => c as Utf16EncodingForm.CodeUnit, asChars));
    Some(asChars)
  }

  function ToUTF16Checked(s: string): Option<seq<uint16>> {
    if Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map(c => c as Utf16EncodingForm.CodeUnit, s)) then
      Some(Seq.Map(c => c as uint16, s))
    else
      None
  }

  function FromUTF16Checked(bs: seq<uint16>): Option<string> {
    if Utf16EncodingForm.IsWellFormedCodeUnitSequence(Seq.Map(c => c as Utf16EncodingForm.CodeUnit, bs)) then
      Some(Seq.Map(c => c as char, bs))
    else
      None
  }
}