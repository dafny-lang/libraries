// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

module GeneralInternals {

  /* this predicate is primarily used as a trigger */
  predicate is_le(x: int, y: int) 
  { 
    x <= y 
  }

  /* aids in the process of induction for modulus */
  lemma lemma_induction_helper(n: int, f: int -> bool, x: int)
    requires n > 0
    requires forall i :: 0 <= i < n ==> f(i)
    requires forall i {:trigger f(i), f(i + n)} :: i >= 0 && f(i) ==> f(i + n)
    requires forall i {:trigger f(i), f(i - n)} :: i < n  && f(i) ==> f(i - n)
    ensures  f(x)
    decreases if x >= n then x else -x
  {
    if (x >= n)
    {
      lemma_induction_helper(n, f, x - n);
      assert f((x - n) + n);
    }
    else if (x < 0)
    {
      lemma_induction_helper(n, f, x + n);
      assert f((x + n) - n);
    }
  }
}