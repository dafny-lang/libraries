// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* lemmas and functions in this file are used in the proofs in DivMod.dfy */

/* Specs/implements mathematical div and mod, not the C version.
This may produce "surprising" results for negative values
For example, -3 div 5 is -1 and -3 mod 5 is 2.
Note this is consistent: -3 * -1 + 2 == 5 */

include "GeneralInternals.dfy"
include "ModInternals.dfy"

module DivInternals {

  import opened GeneralInternals
  import opened ModInternals
  import opened ModInternalsNonlinear
  import opened DivInternalsNonlinear
  import opened MulInternals

  /* Performs division recursively with positive denominator. */
  function method {:opaque} div_pos(x: int, d: int): int
    requires d > 0
    decreases if x < 0 then (d - x) else x
  {
    if x < 0 then
      -1 + div_pos(x + d, d)
    else if x < d then
      0
    else
      1 + div_pos(x - d, d)
  }

  /* Performs division recursively. */
  function {:opaque} div_recursive(x: int, d: int): int
    requires d != 0
  {
    reveal_div_pos();
    if d > 0 then
      div_pos(x, d)
    else
      -1 * div_pos(x, -1 * d)
  }

  /* proves the basics of the division operation */
  lemma lemma_div_basics(n: int)
    requires n > 0
    ensures  n / n == -((-n) / n) == 1
    ensures  forall x:int {:trigger x / n} :: 0 <= x < n <==> x / n == 0
    ensures  forall x:int {:trigger (x + n) / n} :: (x + n) / n == x / n + 1
    ensures  forall x:int {:trigger (x - n) / n} :: (x - n) / n == x / n - 1
  {
    lemma_mod_auto(n);
    lemma_mod_basics(n);
    lemma_small_div();
    lemma_div_by_self(n);
    forall x: int | x / n == 0
      ensures 0 <= x < n
    {
      lemma_fundamental_div_mod(x, n);
    }
  }

  /* automates the division operator process */
  predicate div_auto(n: int)
    requires n > 0
  {
    && mod_auto(n)
    && (n / n == -((-n) / n) == 1)
    && (forall x: int {:trigger x / n} :: 0 <= x < n <==> x / n == 0)
    && (forall x: int, y: int {:trigger (x + y) / n} ::
          (var z := (x % n) + (y % n);
                    ((0 <= z < n && (x + y) / n == x / n + y / n) ||
                    (n <= z < n + n && (x + y) / n == x / n + y / n + 1))))
    && (forall x: int, y: int {:trigger (x - y) / n} ::
          (var z := (x % n) - (y % n);
                    ((0 <= z < n && (x - y) / n == x / n - y / n) ||
                    (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))))
  }

  /* ensures that div_auto is true */
  lemma lemma_div_auto(n: int)
    requires n > 0
    ensures  div_auto(n)
  {
    lemma_mod_auto(n);
    lemma_div_basics(n);
    assert (0 + n) / n == 1;
    assert (0 - n) / n == -1;
    forall x:int, y:int {:trigger (x + y) / n}
      ensures  var z := (x % n) + (y % n);
                      (|| (0 <= z < n && (x + y) / n == x / n + y / n)
                        || (n <= z < 2 * n && (x + y) / n == x / n + y / n + 1))
    {
      var f := (xx:int, yy:int) =>
                  (var z := (xx % n) + (yy % n);
                      (   (0 <= z < n && (xx + yy) / n == xx / n + yy / n)
                        || (n <= z < 2 * n && (xx + yy) / n == xx / n + yy / n + 1)));
      forall i, j
        ensures j >= 0 && f(i, j) ==> f(i, j + n)
        ensures i < n  && f(i, j) ==> f(i - n, j)
        ensures j < n  && f(i, j) ==> f(i, j - n)
        ensures i >= 0 && f(i, j) ==> f(i + n, j)
      {
        assert ((i + n) + j) / n == ((i + j) + n) / n;
        assert (i + (j + n)) / n == ((i + j) + n) / n;
        assert ((i - n) + j) / n == ((i + j) - n) / n;
        assert (i + (j - n)) / n == ((i + j) - n) / n;
      }
      forall i, j
        ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
      {
        assert ((i + n) + j) / n == ((i + j) + n) / n;
        assert (i + (j + n)) / n == ((i + j) + n) / n;
        assert ((i - n) + j) / n == ((i + j) - n) / n;
        assert (i + (j - n)) / n == ((i + j) - n) / n;
      }
      lemma_mod_induction_forall2(n, f);
      assert f(x, y);
    }
    forall x:int, y:int {:trigger (x - y) / n}
      ensures  var z := (x % n) - (y % n);
                      (|| (0 <= z < n && (x - y) / n == x / n - y / n)
                        || (-n <= z < 0 && (x - y) / n == x / n - y / n - 1))
    {
      var f := (xx:int, yy:int) =>
                  (var z := (xx % n) - (yy % n);
                      (   (0 <= z < n && (xx - yy) / n == xx / n - yy / n)
                      || (-n <= z < 0 && (xx - yy) / n == xx / n - yy / n - 1)));
      forall i, j
        ensures j >= 0 && f(i, j) ==> f(i, j + n)
        ensures i < n  && f(i, j) ==> f(i - n, j)
        ensures j < n  && f(i, j) ==> f(i, j - n)
        ensures i >= 0 && f(i, j) ==> f(i + n, j)
      {
        assert ((i + n) - j) / n == ((i - j) + n) / n;
        assert (i - (j - n)) / n == ((i - j) + n) / n;
        assert ((i - n) - j) / n == ((i - j) - n) / n;
        assert (i - (j + n)) / n == ((i - j) - n) / n;
      }
      forall i, j
        ensures 0 <= i < n && 0 <= j < n ==> f(i, j)
      {
        assert ((i + n) - j) / n == ((i - j) + n) / n;
        assert (i - (j - n)) / n == ((i - j) + n) / n;
        assert ((i - n) - j) / n == ((i - j) - n) / n;
        assert (i - (j + n)) / n == ((i - j) - n) / n;
      }
      lemma_mod_induction_forall2(n, f);
      assert f(x, y);
    }
  }

  /* performs auto induction for division */
  lemma lemma_div_induction_auto(n: int, x: int, f: int->bool)
    requires n > 0
    requires div_auto(n) ==> && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger is_le(i + 1, n)} :: is_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  div_auto(n)
    ensures  f(x)
  {
    lemma_div_auto(n);
    assert forall i :: is_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: is_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: is_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
    assert f(x);
  }

  /* performs auto induction on division for all i s.t. f(i) exists */
  lemma lemma_div_induction_auto_forall(n:int, f:int->bool)
    requires n > 0
    requires div_auto(n) ==> && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && i < n ==> f(i))
                          && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + n))
                          && (forall i {:trigger is_le(i + 1, n)} :: is_le(i + 1, n) && f(i) ==> f(i - n))
    ensures  div_auto(n)
    ensures  forall i {:trigger f(i)} :: f(i)
  {
    lemma_div_auto(n);
    assert forall i :: is_le(0, i) && i < n ==> f(i);
    assert forall i {:trigger f(i), f(i + n)} :: is_le(0, i) && f(i) ==> f(i + n);
    assert forall i {:trigger f(i), f(i - n)} :: is_le(i + 1, n) && f(i) ==> f(i - n);
    lemma_mod_induction_forall(n, f);
  }

} 