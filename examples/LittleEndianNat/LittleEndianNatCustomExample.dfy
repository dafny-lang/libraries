// RUN: %dafny /compile:3 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../src/Collections/Sequences/LittleEndianNatConversions.dfy"

module Uint3_6 refines LittleEndianNatConversions {

  module Uint3Seq refines SmallSeq {
    function method BITS(): nat { 3 }
  }
  module Uint6Seq refines LargeSeq {
    import Small = Uint3Seq
    function method BITS(): nat { 6 }
  }
  import opened Large = Uint6Seq
  import Small = Large.Small

}

module LittleEndianNatCustomExample {

  import opened Uint3_6

  method Main() {
    var n := 165;

    // Convert n to uint3 and uint6 sequences
    var smallSeq, largeSeq := Small.FromNat(n), Large.FromNat(n);
    expect smallSeq == [5, 4, 2];
    expect largeSeq == [37, 2];

    Small.LemmaNatSeqNat(n);
    Large.LemmaNatSeqNat(n);
    assert Small.ToNatRight(smallSeq) == Large.ToNatRight(largeSeq) == n;
  }

}
