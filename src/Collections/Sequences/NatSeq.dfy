// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* The first element of a sequence is the least significant word; the last
element is the most significant word. */

include "../../NonlinearArithmetic/DivMod.dfy"
include "../../NonlinearArithmetic/Mul.dfy"
include "../../NonlinearArithmetic/Power.dfy"
include "Seq.dfy"

abstract module NatSeq {

  import opened DivMod
  import opened Mul
  import opened Power
  import opened Seq

  /* Upper bound of a word */
  function method BOUND(): nat
		ensures BOUND() > 1

  type uint = i: int | 0 <= i < BOUND()

  //////////////////////////////////////////////////////////////////////////////
  //
  // ToNat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a sequence to a nat beginning from the least significant word. */
  function method {:opaque} ToNat(xs: seq<uint>): nat
  {
    if |xs| == 0 then 0
    else
      LemmaMulNonnegativeAuto();
      ToNat(DropFirst(xs)) * BOUND() + First(xs)
  }

  /* Converts a sequence to a nat beginning from the most significant word. */
  function method {:opaque} ToNatRev(xs: seq<uint>): nat
  {
    if |xs| == 0 then 0
    else
      LemmaPowPositiveAuto();
      LemmaMulNonnegativeAuto();
      ToNatRev(DropLast(xs)) + Last(xs) * Pow(BOUND(), |xs| - 1)
  }

  /* Given the same sequence, ToNat and ToNatRev return the same nat. */
  lemma LemmaToNatEqToNatRev(xs: seq<uint>)
    ensures ToNat(xs) == ToNatRev(xs)
  {
    reveal ToNat();
    reveal ToNatRev();
    if xs == [] {
    } else {
      if DropLast(xs) == [] {
        calc {
          ToNatRev(xs);
          Last(xs) * Pow(BOUND(), |xs| - 1);
            { LemmaPow0Auto(); }
          ToNat(xs);
        }
      } else {
        calc {
          ToNatRev(xs);
          ToNatRev(DropLast(xs)) + Last(xs) * Pow(BOUND(), |xs| - 1);
            { LemmaToNatEqToNatRev(DropLast(xs)); }
          ToNat(DropLast(xs)) + Last(xs) * Pow(BOUND(), |xs| - 1);
          ToNat(DropFirst(DropLast(xs))) * BOUND() + First(xs) + Last(xs)
            * Pow(BOUND(), |xs| - 1);
            { LemmaToNatEqToNatRev(DropFirst(DropLast(xs))); }
          ToNatRev(DropFirst(DropLast(xs))) * BOUND() + First(xs) + Last(xs)
            * Pow(BOUND(), |xs| - 1);
            {
              assert DropFirst(DropLast(xs)) == DropLast(DropFirst(xs));
              reveal Pow();
              LemmaMulProperties();
            }
          ToNatRev(DropLast(DropFirst(xs))) * BOUND() + First(xs) + Last(xs)
            * Pow(BOUND(), |xs| - 2) * BOUND();
            { LemmaMulIsDistributiveAddOtherWayAuto(); }
          ToNatRev(DropFirst(xs)) * BOUND() + First(xs);
            { LemmaToNatEqToNatRev(DropFirst(xs)); }
          ToNat(xs);
        }
      }
    }
  }

  lemma LemmaToNatEqToNatRevAuto()
    ensures forall xs: seq<uint> {:trigger ToNatRev(xs)}{:trigger ToNat(xs)}
      :: ToNat(xs) == ToNatRev(xs)
  {
    reveal ToNat();
    reveal ToNatRev();
    forall xs: seq<uint> {:trigger ToNatRev(xs)}{:trigger ToNat(xs)}
      ensures ToNat(xs) == ToNatRev(xs)
    {
      LemmaToNatEqToNatRev(xs);
    }
  }

  /* The nat representation of a sequence of length 1 is its first (and only)
  word. */
  lemma LemmaSeqLen1(xs: seq<uint>)
    requires |xs| == 1
    ensures ToNat(xs) == First(xs)
  {
    reveal ToNat();
  }

  /* The nat representation of a sequence of length 2 is sum of its first
  word and the product of its second word and BOUND(). */
  lemma LemmaSeqLen2(xs: seq<uint>)
    requires |xs| == 2
    ensures ToNat(xs) == First(xs) + xs[1] * BOUND()
  {
    reveal ToNat();
    LemmaSeqLen1(DropLast(xs));
  }

  /* Appending a zero does not change the nat representation of the sequence. */
  lemma LemmaSeqAppendZero(xs: seq<uint>) 
    ensures ToNat(xs + [0]) == ToNat(xs)
  {
    reveal ToNatRev();
    LemmaToNatEqToNatRevAuto();
    calc == {
      ToNat(xs + [0]);
      ToNatRev(xs + [0]);
      ToNatRev(xs) + 0 * Pow(BOUND(), |xs|);
        { LemmaMulBasicsAuto(); }
      ToNatRev(xs);
      ToNat(xs);
    }
  }

  /* The nat representation of a sequence is bounded by BOUND() to the power of
  the sequence length. */
  lemma LemmaSeqNatBound(xs: seq<uint>)
    ensures ToNat(xs) < Pow(BOUND(), |xs|)
  {
    reveal Pow();
    if |xs| == 0 {
      reveal ToNat();
    } else {
      var len' := |xs| - 1;
      var pow := Pow(BOUND(), len');
      calc {
        ToNat(xs);
           { LemmaToNatEqToNatRev(xs); }
        ToNatRev(xs);
           { reveal ToNatRev(); }
        ToNatRev(DropLast(xs)) + Last(xs) * pow;
        <  {
             LemmaToNatEqToNatRev(DropLast(xs));
             LemmaSeqNatBound(DropLast(xs));
           }
        pow + Last(xs) * pow;
        <= {
            LemmaPowPositiveAuto();
            LemmaMulInequalityAuto();
           }
        pow + (BOUND() - 1) * pow;
           { LemmaMulIsDistributiveAuto(); }
        Pow(BOUND(), len' + 1);
      }
    }
  }

  /* The nat representation of a sequence can be calculated using the nat
  representation of its prefix. */
  lemma LemmaSeqPrefix(xs: seq<uint>, i: nat)
    requires 0 <= i <= |xs|
    ensures ToNat(xs[..i]) + ToNat(xs[i..]) * Pow(BOUND(), i) == ToNat(xs)
  {
    reveal ToNat();
    reveal Pow();
    if i == 1 {
      assert ToNat(xs[..1]) == First(xs);
    } else if i > 1 {
      calc {
        ToNat(xs[..i]) + ToNat(xs[i..]) * Pow(BOUND(), i);
        ToNat(DropFirst(xs[..i])) * BOUND() + First(xs) + ToNat(xs[i..]) * Pow(BOUND(), i);
          {
            assert DropFirst(xs[..i]) == DropFirst(xs)[..i-1];
            LemmaMulProperties();
          }
        ToNat(DropFirst(xs)[..i-1]) * BOUND() + First(xs) + (ToNat(xs[i..]) * Pow(BOUND(), i - 1)) * BOUND();
          { LemmaMulIsDistributiveAddOtherWayAuto(); }
        (ToNat(DropFirst(xs)[..i-1]) + ToNat(DropFirst(xs)[i-1..]) * Pow(BOUND(), i - 1)) * BOUND() + First(xs);
          { LemmaSeqPrefix(DropFirst(xs), i - 1); }
        ToNat(xs);
      }
    }
  }

  /* If there is an inequality between the most significant words of two
  sequences, then there is an inequality between the nat representations of
  those sequences. Helper lemma for LemmaSeqNeq. */
  lemma LemmaSeqMswInequality(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys| > 0
    requires Last(xs) < Last(ys)
    ensures ToNat(xs) < ToNat(ys)
  {
    reveal ToNatRev();
    LemmaToNatEqToNatRevAuto();
    var len' := |xs| - 1;
    calc {
      ToNat(xs);
      ToNatRev(xs);
      <  { LemmaSeqNatBound(DropLast(xs)); }
      Pow(BOUND(), len') + Last(xs) * Pow(BOUND(), len');
      == { LemmaMulIsDistributiveAuto(); }
      (1 + Last(xs)) * Pow(BOUND(), len');
      <= { LemmaPowPositiveAuto(); LemmaMulInequalityAuto(); }
      ToNatRev(ys);
      ToNat(ys);
    }
  }

  /* Two sequences do not have the same nat representations if their prefixes
  do not have the same nat representations. Helper lemma for LemmaSeqNeq. */
  lemma LemmaSeqPrefixNeq(xs: seq<uint>, ys: seq<uint>, i: nat)
    requires 0 <= i <= |xs| == |ys|
    requires ToNat(xs[..i]) != ToNat(ys[..i])
    ensures ToNat(xs) != ToNat(ys)
    decreases |xs| - i
  {
    if i == |xs| {
      assert xs[..i] == xs;
      assert ys[..i] == ys;
    } else {
      if xs[i] == ys[i] {
        reveal ToNatRev();
        assert DropLast(xs[..i+1]) == xs[..i];
        assert DropLast(ys[..i+1]) == ys[..i];

        LemmaToNatEqToNatRevAuto();
        assert ToNat(xs[..i+1]) == ToNatRev(xs[..i+1]);
      } else {
        if xs[i] < ys[i]  { LemmaSeqMswInequality(xs[..i+1], ys[..i+1]); }
        else              { LemmaSeqMswInequality(ys[..i+1], xs[..i+1]); }
      }
      LemmaSeqPrefixNeq(xs, ys, i + 1);
    }
  }

  /* If two sequences of the same length are not equal, their nat
  representations are not equal. */
  lemma LemmaSeqNeq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires xs != ys
    ensures ToNat(xs) != ToNat(ys)
  {
    ghost var i: nat, n: nat := 0, |xs|;

    while i < n
      invariant 0 <= i < n
      invariant xs[..i] == ys[..i]
    {
      if xs[i] != ys[i] {
        break;
      }
      i := i + 1;
    }
    assert ToNatRev(xs[..i]) == ToNatRev(ys[..i]);

    reveal ToNatRev();
    assert xs[..i+1][..i] == xs[..i];
    assert ys[..i+1][..i] == ys[..i];
    LemmaPowPositiveAuto();
    LemmaMulStrictInequalityAuto();
    assert ToNatRev(xs[..i+1]) != ToNatRev(ys[..i+1]);
    LemmaToNatEqToNatRevAuto();

    LemmaSeqPrefixNeq(xs, ys, i+1);
  }

  /* If the nat representations of two sequences of the same length are equal
  to each other, the sequences are the same. */
  lemma LemmaSeqEq(xs: seq<uint>, ys: seq<uint>)
    requires |xs| == |ys|
    requires ToNat(xs) == ToNat(ys)
    ensures xs == ys
  {
    calc ==> {
      xs != ys;
        { LemmaSeqNeq(xs, ys); }
      ToNat(xs) != ToNat(ys);
      false;
    }
  }

  /* The nat representation of a sequence and its least significant word are
  congruent. */
  lemma LemmaSeqLswModEquivalence(xs: seq<uint>)
    requires |xs| >= 1;
    ensures IsModEquivalent(ToNat(xs), First(xs), BOUND());
  {
    if |xs| == 1 {
      LemmaSeqLen1(xs);
      LemmaModEquivalenceAuto();
    } else {
      assert IsModEquivalent(ToNat(xs), First(xs), BOUND()) by {
        reveal ToNat();
        calc ==> {
          true;
            { LemmaModEquivalenceAuto(); }
          IsModEquivalent(ToNat(xs), ToNat(DropFirst(xs)) * BOUND() + First(xs), BOUND());
            { LemmaModMultiplesBasicAuto(); }
          IsModEquivalent(ToNat(xs), First(xs), BOUND());
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // FromNat definition and lemmas
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Converts a nat to a sequence. */
  function method {:opaque} FromNat(n: nat): (xs: seq<uint>)
  {
    if n == 0 then []
    else
      LemmaDivBasicsAuto();
      LemmaDivDecreasesAuto();
      [n % BOUND()] + FromNat(n / BOUND())
  }

  /* Ensures length of the sequence generated by FromNat is less than len.
  Helper lemma for FromNatWithLen. */
  lemma LemmaFromNatLen(n: nat, len: nat)
    requires Pow(BOUND(), len) > n
    ensures |FromNat(n)| <= len
    decreases n
  {
    reveal FromNat();
    if n == 0 {
    } else {
      calc {
        |FromNat(n)|;
        == { LemmaDivBasicsAuto(); }
        1 + |FromNat(n / BOUND())|;
        <= {
             LemmaMultiplyDivideLtAuto();
             LemmaDivDecreasesAuto();
             reveal Pow();
             LemmaFromNatLen(n / BOUND(), len - 1);
           }
        len;
      }
    }
  }

  /* If we start with a nat, convert it to a sequence, and convert it back, we
  get the same nat we started with. */
  lemma LemmaNatSeqNat(n: nat)
    ensures ToNat(FromNat(n)) == n
    decreases n
  {
    reveal ToNat();
    reveal FromNat();
    if n == 0 {
    } else {
      calc {
        ToNat(FromNat(n));
          { LemmaDivBasicsAuto(); }
        ToNat([n % BOUND()] + FromNat(n / BOUND()));
        n % BOUND() + ToNat(FromNat(n / BOUND())) * BOUND();
          {
            LemmaDivDecreasesAuto();
            LemmaNatSeqNat(n / BOUND());
          }
        n % BOUND() + n / BOUND() * BOUND();
          { LemmaFundamentalDivMod(n, BOUND()); }
        n;
      }
    }
  }

  /* Extends a sequence to a specified length. */
  function method {:opaque} SeqExtend(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires |xs| <= n
    ensures |ys| == n
    ensures ToNat(ys) == ToNat(xs)
    decreases n - |xs|
  {
    if |xs| >= n then xs else LemmaSeqAppendZero(xs); SeqExtend(xs + [0], n)
  }

  /* Extends a sequence to a length that is a multiple of n. */
  function method {:opaque} SeqExtendMultiple(xs: seq<uint>, n: nat): (ys: seq<uint>)
    requires n > 0
    ensures |ys| % n == 0
    ensures ToNat(ys) == ToNat(xs)
  {
    var newLen := |xs| + n - (|xs| % n);
    LemmaSubModNoopRight(|xs| + n, |xs|, n);
    LemmaModBasicsAuto();
    assert newLen % n == 0;

    LemmaSeqNatBound(xs);
    LemmaPowIncreasesAuto();
    SeqExtend(xs, newLen)
  }

  /* Converts a nat to a sequence of a specified length. */
  function method {:opaque} FromNatWithLen(n: nat, len: nat): (xs: seq<uint>)
    requires Pow(BOUND(), len) > n
    ensures |xs| == len
    ensures ToNat(xs) == n
  {
    LemmaFromNatLen(n, len);
    LemmaNatSeqNat(n);
    SeqExtend(FromNat(n), len)
  }

  /* If the nat representation of a sequence is zero, then the sequence is a
  sequence of zeros. */
  lemma LemmaSeqZero(xs: seq<uint>)
    requires ToNat(xs) == 0
    ensures forall i {:trigger xs[i]} :: 0 <= i < |xs| ==> xs[i] == 0
  {
    reveal ToNat();
    if |xs| == 0 {
    } else {
      LemmaMulNonnegativeAuto();
      assert First(xs) == 0;

      LemmaMulNonzeroAuto();
      LemmaSeqZero(DropFirst(xs));
    }
  }

  /* Generates a sequence of zeros of a specified length. */
  function method {:opaque} SeqZero(len: nat): (xs: seq<uint>)
    ensures |xs| == len
    ensures forall i {:trigger xs[i]} :: 0 <= i < |xs| ==> xs[i] == 0
    ensures ToNat(xs) == 0
  {
    LemmaPowPositive(BOUND(), len);
    var xs := FromNatWithLen(0, len);
    LemmaSeqZero(xs);
    xs
  }

  /* If we start with a sequence, convert it to a nat, and convert it back to a
  sequence with the same length as the original sequence, we get the same
  sequence we started with. */
  lemma LemmaSeqNatSeq(xs: seq<uint>)
    ensures Pow(BOUND(), |xs|) > ToNat(xs)
    ensures FromNatWithLen(ToNat(xs), |xs|) == xs
  {
    reveal FromNat();
    reveal ToNat();
    LemmaSeqNatBound(xs);
    if |xs| > 0 {
      calc {
        FromNatWithLen(ToNat(xs), |xs|) != xs;
          { LemmaSeqNeq(FromNatWithLen(ToNat(xs), |xs|), xs); }
        ToNat(FromNatWithLen(ToNat(xs), |xs|)) != ToNat(xs);
        ToNat(xs) != ToNat(xs);
        false;
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  //
  // Addition and subtraction
  //
  //////////////////////////////////////////////////////////////////////////////

  /* Adds two sequences. */
  function method {:opaque} SeqAdd(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := SeqAdd(xs, ys);
      |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then ([], 0)
    else
      var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
      var sum: int := Last(xs) + Last(ys) + cin;
      var (sum_out, cout) := if sum < BOUND() then (sum, 0)
                             else (sum - BOUND(), 1);
      (zs' + [sum_out], cout)
  }

  /* SeqAdd returns the same value as converting the sequences to nats, then
  adding them. */
  lemma LemmaSeqAdd(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqAdd(xs, ys) == (zs, cout)
    ensures ToNat(xs) + ToNat(ys) == ToNat(zs) + cout * Pow(BOUND(), |xs|)
  {
    reveal SeqAdd();
    if |xs| == 0 {
      reveal ToNat();
    } else {
      var pow := Pow(BOUND(), |xs| - 1);
      var (zs', cin) := SeqAdd(DropLast(xs), DropLast(ys));
      var sum: int := Last(xs) + Last(ys) + cin;
      var z := if sum < BOUND() then sum else sum - BOUND();
      assert sum == z + cout * BOUND();

      reveal ToNatRev();
      LemmaToNatEqToNatRevAuto();
      calc {
        ToNat(zs);
        ToNatRev(zs);
        ToNatRev(zs') + z * pow;
          { LemmaSeqAdd(DropLast(xs), DropLast(ys), zs', cin); }
        ToNatRev(DropLast(xs)) + ToNatRev(DropLast(ys)) - cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert sum * pow == (z + cout * BOUND()) * pow;
            LemmaMulIsDistributiveAuto();
          } 
        ToNatRev(xs) + ToNatRev(ys) - cout * BOUND() * pow;
          {
            LemmaMulIsAssociative(cout, BOUND(), pow);
            reveal Pow();
          }
        ToNatRev(xs) + ToNatRev(ys) - cout * Pow(BOUND(), |xs|);
        ToNat(xs) + ToNat(ys) - cout * Pow(BOUND(), |xs|);
      }
    }
  }

  /* Subtracts two sequences. */
  function method {:opaque} SeqSub(xs: seq<uint>, ys: seq<uint>): (seq<uint>, nat)
    requires |xs| == |ys|
    ensures var (zs, cout) := SeqSub(xs, ys);
      |zs| == |xs| && 0 <= cout <= 1
    decreases xs
  {
    if |xs| == 0 then ([], 0)
    else 
      var (zs, cin) := SeqSub(DropLast(xs), DropLast(ys));
      var (diff_out, cout) := if Last(xs) >= Last(ys) + cin
                              then (Last(xs) - Last(ys) - cin, 0)
                              else (BOUND() + Last(xs) - Last(ys) - cin, 1);
      (zs + [diff_out], cout)
  }

  /* SeqSub returns the same value as converting the sequences to nats, then
  subtracting them. */
  lemma LemmaSeqSub(xs: seq<uint>, ys: seq<uint>, zs: seq<uint>, cout: nat)
    requires |xs| == |ys|
    requires SeqSub(xs, ys) == (zs, cout)
    ensures ToNat(xs) - ToNat(ys) + cout * Pow(BOUND(), |xs|) == ToNat(zs)
  {
    reveal SeqSub();
    if |xs| == 0 {
      reveal ToNat();
    } else {
      var pow := Pow(BOUND(), |xs| - 1);
      var (zs', cin) := SeqSub(DropLast(xs), DropLast(ys));
      var z := if Last(xs) >= Last(ys) + cin
               then Last(xs) - Last(ys) - cin
               else BOUND() + Last(xs) - Last(ys) - cin;
      assert cout * BOUND() + Last(xs) - cin - Last(ys) == z;

      reveal ToNatRev();
      LemmaToNatEqToNatRevAuto();
      calc {
        ToNat(zs);
        ToNatRev(zs);
        ToNatRev(zs') + z * pow;
          { LemmaSeqSub(DropLast(xs), DropLast(ys), zs', cin); }
        ToNatRev(DropLast(xs)) - ToNatRev(DropLast(ys)) + cin * pow + z * pow;
          {
            LemmaMulEqualityAuto();
            assert pow * (cout * BOUND() + Last(xs) - cin - Last(ys)) == pow * z;
            LemmaMulIsDistributiveAuto();
          }
        ToNatRev(xs) - ToNatRev(ys) + cout * BOUND() * pow;
          {
            LemmaMulIsAssociative(cout, BOUND(), pow);
            reveal Pow();
          }
        ToNatRev(xs) - ToNatRev(ys) + cout * Pow(BOUND(), |xs|);
        ToNat(xs) - ToNat(ys) + cout * Pow(BOUND(), |xs|);
      }
    }
  }

}
