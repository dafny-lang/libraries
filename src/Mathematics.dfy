module Mathematics {
  function method min(a: int, b: int): int
  {
    if a < b
      then a
    else
      b
  }

  function method max(a: int, b: int): int
  {
    if a < b
      then b
    else
      a
  }

  lemma pos_mul_pos_is_pos(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures 0 < x * y
  {
  }
  
  lemma div_ceil_LT(x: int, d: int)
    requires 1 < d
    requires 1 < x
    ensures (x + d - 1) / d < x
  {
    pos_mul_pos_is_pos(d-1, x-1);
    calc <= {
      0; <
      (d-1) * (x-1);
    }
  }

  lemma pos_mul_preserves_order(x: nat, y: nat, m: nat)
    requires x <= y
    ensures x * m <= y * m
  {
  }

  predicate injective<X(!new), Y>(f: X-->Y)
    reads f.reads
    requires forall x :: f.requires(x)
  {
    forall x1, x2 :: f(x1) == f(x2) ==> x1 == x2
  }
}
