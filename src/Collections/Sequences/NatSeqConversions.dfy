// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../NonlinearArithmetic/DivMod.dfy"
include "../../NonlinearArithmetic/Mul.dfy"
include "../../NonlinearArithmetic/Power.dfy"
include "Seq.dfy"
include "NatSeq.dfy"

/* Sequence with smaller bound. */
abstract module SmallSeq refines NatSeq {

  function method BITS(): nat
    ensures BITS() > 1

  function method BOUND(): nat
  {
    LemmaPowPositive(2, BITS() - 1);
    LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
    Pow(2, BITS())
  }

}

/* Sequence with larger bound. */
abstract module LargeSeq refines NatSeq {

  import Small : SmallSeq

  function method BITS(): nat
    ensures BITS() > Small.BITS() && BITS() % Small.BITS() == 0

  function method BOUND(): nat
  {
    LemmaPowPositive(2, BITS() - 1);
    LemmaPowStrictlyIncreases(2, BITS() - 1, BITS());
    Pow(2, BITS())
  }

}

abstract module NatSeqConversions {

  import opened DivMod
  import opened Mul
  import opened Power
  import opened Seq

  import opened Large : LargeSeq

  /* Small.BOUND() to the power of E is Large.BOUND(). */
  function method E(): (E: nat)
    ensures Pow(Small.BOUND(), E) == Large.BOUND()
    ensures E > 0
  {
    LemmaDivBasicsAuto();
    LemmaPowMultipliesAuto();
    LemmaFundamentalDivMod(Large.BITS(), Small.BITS());
    Large.BITS() / Small.BITS()
  }

  /* Converts a sequence from Large.BOUND() to Small.BOUND(). */
  function method {:opaque} ToSmall(xs: seq<Large.uint>): (ys: seq<Small.uint>)
    ensures |ys| == |xs| * E()
  {
    if |xs| == 0 then []
    else
      LemmaMulIsDistributiveAddOtherWay(E(), 1, |xs| - 1);
      Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs))
  }

  /* Converts a sequence from Small.BOUND() to Large.BOUND(). */
  function method {:opaque} ToLarge(xs: seq<Small.uint>): (ys: seq<Large.uint>)
    requires |xs| % E() == 0
    ensures |ys| == |xs| / E()
  {
    if |xs| == 0 then LemmaDivBasicsAuto(); []
    else
      LemmaModIsZero(|xs|, E());
      assert |xs| >= E();

      Small.LemmaSeqNatBound(xs[..E()]);
      LemmaModSubMultiplesVanishAuto();
      LemmaDivMinusOne(|xs|, E());
      [Small.ToNat(xs[..E()]) as Large.uint] + ToLarge(xs[E()..])
  }

  /* Sequence conversion from Large.BOUND() to Small.BOUND() does not
  change its nat representation. */
  lemma LemmaToSmall(xs: seq<Large.uint>)
    ensures Small.ToNat(ToSmall(xs)) == Large.ToNat(xs)
  {
    reveal Small.ToNat();
    reveal Large.ToNat();
    reveal ToSmall();
    if |xs| == 0 {
    } else {
      calc {
        Small.ToNat(ToSmall(xs));
        Small.ToNat(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
          {
            Small.LemmaSeqPrefix(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)), E());
            LemmaToSmall(DropFirst(xs));
          }
        First(xs) + Large.ToNat(DropFirst(xs)) * Pow(Small.BOUND(), E());
          { assert Pow(Small.BOUND(), E()) == Large.BOUND(); }
        Large.ToNat(xs);
      }
    }
  }

  /* Sequence conversion from Small.BOUND() to Large.BOUND() does not
  change its nat representation. */
  lemma LemmaToLarge(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures Large.ToNat(ToLarge(xs)) == Small.ToNat(xs)
  {
    reveal Large.ToNat();
    reveal Small.ToNat();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        Large.ToNat(ToLarge(xs));
          {
            LemmaModIsZero(|xs|, E());
            LemmaModSubMultiplesVanishAuto();
            Small.LemmaSeqNatBound(xs[..E()]);
          }
        Large.ToNat([Small.ToNat(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
          { LemmaToLarge(xs[E()..]); }
        Small.ToNat(xs[..E()]) + Small.ToNat(xs[E()..]) * Pow(Small.BOUND(), E());
          { Small.LemmaSeqPrefix(xs, E()); }
        Small.ToNat(xs);
      }
    }
  }

  /* ToSmall is injective. */
  lemma LemmaToSmallIsInjective(xs: seq<Large.uint>, ys: seq<Large.uint>)
    requires ToSmall(xs) == ToSmall(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    LemmaToSmall(xs);
    LemmaToSmall(ys);
    assert Large.ToNat(xs) == Large.ToNat(ys);
    Large.LemmaSeqEq(xs, ys);
  }

  /* ToLarge is injective. */
  lemma LemmaToLargeIsInjective(xs: seq<Small.uint>, ys: seq<Small.uint>)
    requires |xs| % E() == |ys| % E() == 0 
    requires ToLarge(xs) == ToLarge(ys)
    requires |xs| == |ys|
    ensures xs == ys
  {
    LemmaToLarge(xs);
    LemmaToLarge(ys);
    assert Small.ToNat(xs) == Small.ToNat(ys);
    Small.LemmaSeqEq(xs, ys);
  }

  /* If we start with a Small sequence, convert it to a Large sequence,
  and convert it back, we get the same sequence we started with. */
  lemma LemmaSmallLargeSmall(xs: seq<Small.uint>)
    requires |xs| % E() == 0
    ensures ToSmall(ToLarge(xs)) == xs
  {
    reveal ToSmall();
    reveal ToLarge();
    if |xs| == 0 {
    } else {
      calc {
        ToSmall(ToLarge(xs));
          {
            LemmaModIsZero(|xs|, E());
            Small.LemmaSeqNatBound(xs[..E()]);
            LemmaModSubMultiplesVanishAuto();
          }
        ToSmall([Small.ToNat(xs[..E()]) as Large.uint] + ToLarge(xs[E()..]));
        Small.FromNatWithLen(Small.ToNat(xs[..E()]), E()) + ToSmall(ToLarge(xs[E()..]));
          {
            Small.LemmaSeqNatSeq(xs[..E()]);
            LemmaSmallLargeSmall(xs[E()..]);
          }
        xs;
      }
    }
  }

  /* If we start with a Large sequence, convert it to a Sequence sequence,
  and convert it back, we get the same sequence we started with. */
  lemma LemmaLargeSmallLarge(xs: seq<Large.uint>)
    ensures |ToSmall(xs)| % E() == 0
    ensures ToLarge(ToSmall(xs)) == xs
  {
    reveal ToSmall();
    reveal ToLarge();
    LemmaModMultiplesBasicAuto();
    if |xs| == 0 {
    } else {
      calc {
        ToLarge(ToSmall(xs));
        ToLarge(Small.FromNatWithLen(First(xs), E()) + ToSmall(DropFirst(xs)));
        [Small.ToNat(Small.FromNatWithLen(First(xs), E())) as Large.uint] + ToLarge(ToSmall(DropFirst(xs)));
        [First(xs)] + ToLarge(ToSmall(DropFirst(xs)));
          { LemmaLargeSmallLarge(DropFirst(xs)); }
        [First(xs)] + DropFirst(xs);
        xs;
      }
    }
  }

}

/* Conversions between sequences of uint8 and uint16. */
module Uint8_16 refines NatSeqConversions {

  module Uint8Seq refines SmallSeq {
    function method BITS(): nat { 8 }
  }

  module Uint16Seq refines LargeSeq {
    import Small = Uint8Seq
    function method BITS(): nat { 16 }
  }

  import opened Large = Uint16Seq
  import Small = Large.Small

}

/* Conversions between sequences of uint8 and uint32. */
module Uint8_32 refines NatSeqConversions {

  module Uint8Seq refines SmallSeq {
    function method BITS(): nat { 8 }
  }

  module Uint32Seq refines LargeSeq {
    import Small = Uint8Seq
    function method BITS(): nat { 32 }
  }

  import opened Large = Uint32Seq
  import Small = Large.Small

}

/* Conversions between sequences of uint8 and uint64. */
module Uint8_64 refines NatSeqConversions {

  module Uint8Seq refines SmallSeq {
    function method BITS(): nat { 8 }
  }

  module Uint64Seq refines LargeSeq {
    import Small = Uint8Seq
    function method BITS(): nat { 64 }
  }

  import opened Large = Uint64Seq
  import Small = Large.Small

}

/* Conversions between sequences of uint16 and uint32. */
module Uint16_32 refines NatSeqConversions {

  module Uint16Seq refines SmallSeq {
    function method BITS(): nat { 16 }
  }

  module Uint32Seq refines LargeSeq {
    import Small = Uint16Seq
    function method BITS(): nat { 32 }
  }

  import opened Large = Uint32Seq
  import Small = Large.Small

}

/* Conversions between sequences of uint32 and uint64. */
module Uint32_64 refines NatSeqConversions {

  module Uint32Seq refines SmallSeq {
    function method BITS(): nat { 32 }
  }

  module Uint64Seq refines LargeSeq {
    import Small = Uint32Seq
    function method BITS(): nat { 64 }
  }

  import opened Large = Uint64Seq
  import Small = Large.Small

}
