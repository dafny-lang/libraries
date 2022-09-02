// include "../.s./NonlinearArithmetic/DivMod.dfy" // Only needed for unused proofs

module JSON.Utils.Math {
  function method {:opaque} IntPow(base: int, n: nat): int {
    if n == 0 then 1
    else base * IntPow(base, n - 1)
  }

  lemma {:induction n} IntPow_Nat(base: nat, n: nat)
    ensures IntPow(base, n) >= 0
  {
    reveal IntPow();
  }

  lemma {:induction n} IntPow_NonZero(base: int, n: nat)
    requires base != 0
    ensures IntPow(base, n) != 0
  {
    reveal IntPow();
  }

  function method {:opaque} IntLog(base: nat, pow: nat): nat
    requires base > 1
    decreases pow
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

  /*
  import DivMod

  lemma {:induction false} Multiply_Divide(p: int, q: nat)
    requires q != 0
    ensures q * p / q == p
  {
    DivMod.LemmaDivMultiplesVanish(p, q);
  }

  lemma {:induction false} IntLog_IntPow(base: nat, n: nat)
    requires base > 1
    ensures (IntPow_Nat(base, n); IntLog(base, IntPow(base, n)) == n)
  {
    if n == 0 {
      reveal IntPow();
      reveal IntLog();
    } else {
      IntPow_Nat(base, n);
      calc {
        IntLog(base, IntPow(base, n));
        { reveal IntPow(); }
        IntLog(base, base * IntPow(base, n - 1));
        { reveal IntLog(); IntPow_Nat(base, n - 1); IntPow_NonZero(base, n - 1); }
        1 + IntLog(base, base * IntPow(base, n - 1) / base);
        { Multiply_Divide(IntPow(base, n - 1), base); }
        1 + IntLog(base, IntPow(base, n - 1));
        { IntLog_IntPow(base, n - 1); }
        1 + (n - 1);
      }
    }
  }

  lemma {:induction false} IntPow_IntLog(base: nat, pow: nat)
    requires base > 1
    requires pow > 0
     ensures IntPow(base, IntLog(base, pow)) <= pow < IntPow(base, IntLog(base, pow) + 1)
  */
}
