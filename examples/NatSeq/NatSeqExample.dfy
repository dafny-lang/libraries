// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/Collections/Sequences/NatSeqConversions.dfy"

module NatSeqExample {

  import opened Uint8_32

  method Main() {
    var n := 49602234234;

    // Convert n to uint8 and uint32 sequences
    var smallSeq, largeSeq := Small.FromNat(n), Large.FromNat(n);

    Small.LemmaNatSeqNat(n);
    Large.LemmaNatSeqNat(n);
    assert Small.ToNat(smallSeq) == Large.ToNat(largeSeq) == n;

    // Extend smallSeq
    smallSeq := Small.SeqExtendMultiple(smallSeq, E());
    assert Small.ToNat(smallSeq) == n;

    // Convert between smallSeqExtended and largeSeq
    LemmaToSmall(largeSeq);
    LemmaToLarge(smallSeq);
    assert Small.ToNat(ToSmall(largeSeq)) == n;
    assert Large.ToNat(ToLarge(smallSeq)) == n;
    assert |ToSmall(largeSeq)|  == |largeSeq| * E();
    assert |ToLarge(smallSeq)|  == |smallSeq| / E();

    LemmaSmallLargeSmall(smallSeq);
    LemmaLargeSmallLarge(largeSeq);
    assert ToSmall(ToLarge(smallSeq)) == smallSeq;
    assert ToLarge(ToSmall(largeSeq)) == largeSeq;
  }

}
