// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module Math {
  function method Min(a: int, b: int): int
  {
    if a < b
      then a
    else
      b
  }

  function method Max(a: int, b: int): int
  {
    if a < b
      then b
    else
      a
  }

  function method Abs(a: int): (a': int)
    ensures a' >= 0
  {
    if a >= 0 then a else -a
  }

  function method {:opaque} IntPow(base: int, n: nat): int {
    if n == 0 then 1
    else base * IntPow(base, n - 1)
  }

  function method {:opaque} IntLog(base: nat, pow: nat): nat
    requires base > 1
    decreases pow
    // TODO: pow > 0 ==> IntPow(base, IntLog(base, pow)) <= pow < IntPow(base, IntLog(base, pow) + 1)
  {
    if pow < base then 0
    else
      assert pow < pow * base; assert pow / base < pow;
      1 + IntLog(base, pow / base)
  }

  lemma {:induction false} Divide_Increasing(base: nat, pow: nat, pow': nat)
    requires base > 1
    requires pow <= pow'
    ensures pow / base <= pow' / base
  {
    var q, q', r, r' := pow / base, pow' / base, pow % base, pow' % base;
    assert pow == q * base + r;
    assert pow' == q' * base + r';
    assert 0 <= r < base && 0 <= r' < base;
    var dp, dq, dr := pow' - pow, q' - q, r' - r;
    assert dp == dq * base + dr;
    if dq < 0 {
      assert dq * base < -base;
      assert dr <= base;
      assert dp == dq * base + dr < 0;
      assert false;
    }
  }

  lemma {:induction false} IntLog_Increasing(base: nat, pow: nat, pow': nat)
    requires base > 1
    requires pow <= pow'
    ensures IntLog(base, pow) <= IntLog(base, pow')
    decreases pow
  {
    reveal IntLog();
    if pow' < base {
      assert IntLog(base, pow) == 0 == IntLog(base, pow');
    } else if pow < base {
      assert IntLog(base, pow) == 0;
    } else {
      assert pow < pow * base; assert pow / base < pow;
      assert pow' < pow' * base; assert pow' / base < pow';
      assert pow / base <= pow' / base by { Divide_Increasing(base, pow, pow'); }
      IntLog_Increasing(base, pow / base, pow' / base);
    }
  }

  // lemma {:induction n} IntPow_Nat(base: nat, n: nat)
  //   ensures IntPow(base, n) >= 0
  // {
  //   reveal IntPow();
  // }

  // lemma {:induction n} IntPow_NonZero(base: int, n: nat)
  //   requires base != 0
  //   ensures IntPow(base, n) != 0
  // {
  //   reveal IntPow();
  // }

  // function method {:opaque} NatPow(base: nat, n: nat): nat {
  //   IntPow_Nat(base, n);
  //   IntPow(base, n)
  // }

  // lemma {:induction false} NatPow_NonZero(base: nat, n: nat)
  //   requires base != 0
  //   ensures NatPow(base, n) != 0
  // {
  //   reveal NatPow(); IntPow_NonZero(base, n);
  // }

  // function method {:opaque} IntLogSup(base: nat, pow: nat): (log: nat)
  //   requires base > 1
  //   ensures log > 0
  //   decreases pow
  //   // IntPow(base, IntLogSup(base, pow) - 1) - 1 <= pow <= IntPow(base, IntLogSup(base, pow))
  // {
  //   if pow < base then 1
  //   else
  //     assert pow < pow * base;
  //     assert pow / base < pow;
  //     1 + IntLog(base, pow / base)
  // }

  // // lemma {:induction false} IntLogSup_transfer(base: nat, n: nat, n': nat)
  // //   requires base > 1
  // //   requires n > n'
  // //   ensures
  // //     (NatPow_NonZero(base, n); NatPow_NonZero(base, n');
  // //      IntLogSup(base, NatPow(base, n), NatPow(base, n')) == IntLogSup(base, NatPow(base, n - n')))
  // // {
  // //   reveal NatPow();
  // //   reveal IntPow();
  // //   reveal IntLogSup();
  // //   if n' == 0 {
  // //   } else {
  // //     NatPow_NonZero(base, n); NatPow_NonZero(base, n'); NatPow_NonZero(base, n' - 1);
  // //     calc {
  // //       IntLogSup(base, NatPow(base, n), NatPow(base, n'));
  // //       1 + IntLogSup(base, NatPow(base, n), NatPow(base, n' - 1) * base) - 1;
  // //       { assume NatPow(base, n) > NatPow(base, n'); } // FIXME wrong
  // //       IntLogSup(base, NatPow(base, n), NatPow(base, n' - 1)) - 1;
  // //       { IntLogSup_transfer(); }
  // //       IntLogSup(base, NatPow(base, n - n'))
  // //     }
  // //   }
  // // }

  // lemma {:induction false} IntPow_IntLogSup(base: nat, n: nat)
  //   requires base > 1
  //   ensures IntLogSup(base, NatPow(base, n)) - 1 < n <= IntLogSup(base, NatPow(base, n))
  // {
  //   reveal IntLogSup();
  //   reveal IntPow();
  //   reveal NatPow();
  //   if n == 0 {
  //   } else {
  //     calc {
  //       IntLogSup(base, NatPow(base, n));
  //       IntLogSup(base, NatPow(base, n - 1) * base);
  //       IntLogSup(base, NatPow(base, n - 1) * base);
  //       1 + IntLogSup(base, NatPow(base, n - 1));
  //     }
  //   }
  // }
}
