// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../Collections/Sequences/Seq.dfy"
include "../BoundedInts.dfy"

include "Unicode.dfy"
include "Utf16EncodingForm.dfy"

/**
  * The Unicode encoding scheme that serializes a UTF-16 code unit sequence in exactly the same order as the code unit
  * sequence itself.
  *
  * Because the UTF-8 encoding form deals in ordered byte sequences, the UTF-8 encoding scheme is trivial.
  * The byte ordering is completely defined by the UTF-16 code unit sequence itself.
  * We implement the encoding scheme here for completeness of the Unicode character encoding model,
  * and to perform the (trivial) conversion between `uint16` and `bv16` values.
  *
  * (Section 3.10 D95)
  *
  * TODO: this should refine an abstract UnicodeEncodingScheme module
  * that states lemmas/conditions about Serialize and Deserialize
  * which refining modules would prove about their own implementations.
  * Proving those lemmas are easier to write using `calc`,
  * but that runs into <https://github.com/dafny-lang/dafny/issues/1639>.
  */
module {:options "-functionSyntax:4"} Utf16EncodingScheme {
  import opened Wrappers

  import BoundedInts
  import Seq
  import Unicode
  import Utf16EncodingForm

  type uint16 = BoundedInts.uint16
  type utf16bytes = b: seq<uint16> | Utf16EncodingForm.IsWellFormedCodeUnitSequence(Deserialize(b))

  /**
    * Returns the byte serialization of the given code unit sequence.
    */
  function Serialize(s: Utf16EncodingForm.CodeUnitSeq): (b: seq<uint16>)
  {
    Seq.Map(c => c as uint16, s)
  }

  /**
    * Returns the code unit sequence that serializes to the given byte sequence.
    */
  function Deserialize(b: seq<uint16>): (s: Utf16EncodingForm.CodeUnitSeq)
  {
    Seq.Map(b => b as Utf16EncodingForm.CodeUnit, b)
  }

  /**
    * Serializing a code unit sequence and then deserializing the result, yields the original code unit sequence.
    */
  lemma LemmaSerializeDeserialize(s: Utf16EncodingForm.CodeUnitSeq)
    ensures Deserialize(Serialize(s)) == s
  {}

  /**
    * Deserializing a byte sequence and then serializing the result, yields the original byte sequence.
    */
  lemma LemmaDeserializeSerialize(b: seq<uint16>)
    ensures Serialize(Deserialize(b)) == b
  {
    calc {
      Serialize(Deserialize(b));
    == // Definitions of Serialize, Deserialize
      Seq.Map(c => c as uint16, Seq.Map(b => b as Utf16EncodingForm.CodeUnit, b));
    == // Compositionality of Map
      Seq.Map(b => (b as Utf16EncodingForm.CodeUnit) as uint16, b);
    == // Simplify map
      Seq.Map(b => b, b);
    == // Identity function
      b;
    }
  }
}
