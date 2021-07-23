// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* Every lemma comes in 2 forms: 'lemma_property' and 'lemma_property_auto'. The former takes arguments and may 
be more stable and less reliant on Z3 heuristics. The latter includes automation and its use requires less effort */

include "DivMod.dfy"
include "../Mathematics.dfy"
include "Internals/GeneralInternals.dfy"
include "Mul.dfy"
include "Internals/MulInternals.dfy"

module Power {
  import opened DivMod
  import opened Mathematics
  import opened GeneralInternals
  import opened Mul
  import opened MulInternals

  function method {:opaque} power(b: int, e: nat): int
    decreases e
  {
    if e == 0 then
      1
    else
      b * power(b, e - 1)
  }

  /* A number raised to the power of 0 equals 1. */
  lemma lemma_power_0(b: int)
    ensures power(b, 0) == 1
  {
    reveal_power();
  }

  lemma lemma_power_0_auto()
    ensures forall b: nat {:trigger power(b, 0)} :: power(b, 0) == 1
  {
    reveal_power();
    forall b: nat {:trigger power(b, 0)}
      ensures power(b, 0) == 1
    {
      lemma_power_0(b);
    }
  }

  /* A number raised to the power of 1 equals the number itself. */
  lemma lemma_power_1(b: int)
    ensures power(b, 1) == b
  {
    calc {
      power(b, 1);
        { reveal_power(); }
      b * power(b, 0);
        { lemma_power_0(b); }
      b * 1;
        { lemma_mul_basics_auto(); }
      b;
    }
  }

  lemma lemma_power_1_auto()
    ensures forall b: nat {:trigger power(b, 1)} :: power(b, 1) == b
  {
    reveal_power();
    forall b: nat {:trigger power(b, 1)}
      ensures power(b, 1) == b
    {
      lemma_power_1(b);
    }
  }

  /* 0 raised to a positive power equals 0. */
  lemma lemma_0_power(e: nat)
    requires e > 0
    ensures power(0, e) == 0
  {
    reveal_power();
    lemma_mul_basics_auto();
    if e != 1 {
      lemma_0_power(e - 1);
    }
  }

  lemma lemma_0_power_auto()
    ensures forall e: nat {:trigger power(0, e)} :: e > 0 ==> power(0, e) == 0
  {
    reveal_power();
    forall e: nat {:trigger power(0, e)} | e > 0
      ensures power(0, e) == 0
    {
      lemma_0_power(e);
    }
  }

  /* 1 raised to any power equals 1. */
  lemma lemma_1_power(e: nat)
    ensures power(1, e) == 1
  {
    reveal_power();
    lemma_mul_basics_auto();
    if e != 0 {
      lemma_1_power(e - 1);
    }
  }

  lemma lemma_1_power_auto()
    ensures forall e: nat {:trigger power(1, e)} :: power(1, e) == 1
  {
    reveal_power();
    forall e: nat {:trigger power(1, e)}
      ensures power(1, e) == 1
    {
      lemma_1_power(e);
    }
  }

  /* Squaring a number is equal to raising it to the power of 2. */
  lemma lemma_square_is_power_2(x: nat)
    ensures power(x, 2) == x * x
  {
    reveal_power();
  }

  lemma lemma_square_is_power_2_auto()
    ensures forall x: nat {:trigger power(x, 2)} :: power(x, 2) == x * x
  {
    reveal_power();
    forall x: nat {:trigger power(x, 2)}
      ensures power(x, 2) == x * x
    {}
  }

  /* A positive number raised to any power is positive. */
  lemma lemma_power_positive(b: int, e: nat)
    requires b > 0
    ensures  0 < power(b, e)
  {
    lemma_power_auto();
    lemma_mul_induction_auto(e, u => 0 <= u ==> 0 < power(b, u));
  }

  lemma lemma_power_positive_auto()
    ensures forall b: int, e: nat {:trigger power(b, e)}
      :: b > 0 ==> 0 < power(b, e)
  {
    reveal_power();
    forall b: int, e: nat {:trigger power(b, e)} | b > 0
      ensures 0 < power(b, e)
    {
      lemma_power_positive(b, e);
    }
  }

  /* Add exponents when multiplying powers with the same base. */
  lemma lemma_power_adds(b: int, e1: nat, e2: nat)
    decreases e1
    ensures power(b, e1 + e2) == power(b, e1) * power(b, e2)
  {
    if e1 == 0 {
      calc {
        power(b, e1) * power(b, e2);
          { lemma_power_0(b); }
        1 * power(b, e2);
          { lemma_mul_basics_auto(); }
        power(b, 0 + e2);
      }
    }
    else {
      calc {
        power(b, e1) * power(b, e2);
          { reveal_power(); }
        (b * power(b, e1 - 1)) * power(b, e2);
          { lemma_mul_is_associative_auto(); }
        b * (power(b, e1 - 1) * power(b, e2));
          { lemma_power_adds(b, e1 - 1, e2); }
        b * power(b, e1 - 1 + e2);
          { reveal_power(); }
        power(b, e1 + e2);
      }
    }
  }

  lemma lemma_power_adds_auto()
    ensures forall b: int, e1: nat, e2: nat {:trigger power(b, e1 + e2)}
      :: power(b, e1 + e2) == power(b, e1) * power(b, e2)
  {
    reveal_power();
    forall b: int, e1: nat, e2: nat {:trigger power(b, e1 + e2)}
      ensures power(b, e1 + e2) == power(b, e1) * power(b, e2)
    {
      lemma_power_adds(b, e1, e2);
    }
  }

  /* Subtract exponents when dividing powers. */
  lemma lemma_power_subtracts(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures power(b, e1) > 0
    ensures power(b, e2 - e1) == power(b, e2) / power(b, e1) > 0
  {
    lemma_power_positive_auto();
    calc {
      power(b, e2) / power(b, e1);
        { lemma_power_adds(b, e2 - e1, e1); }
      power(b, e2 - e1) * power(b, e1) / power(b, e1);
        { lemma_div_by_multiple(power(b, e2 - e1), power(b, e1)); }
      power(b, e2 - e1);
    }
  }

  lemma lemma_power_subtracts_auto()
    ensures forall b: nat, e1: nat :: b > 0 ==> power(b, e1) > 0
    ensures forall b: nat, e1: nat, e2: nat {:trigger power(b, e2 - e1)}
      :: b > 0 && e1 <= e2 ==>
         power(b, e2 - e1) == power(b, e2) / power(b, e1) > 0
  {
    reveal_power();
    lemma_power_positive_auto();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e2 - e1)}
      | b > 0 && e1 <= e2
      ensures power(b, e2 - e1) == power(b, e2) / power(b, e1) > 0
    {
      lemma_power_subtracts(b, e1, e2);
    }
  }

  /* Multiply exponents when finding the power of a power. */
  lemma lemma_power_multiplies(a: int, b: nat, c: nat)
    decreases c
    ensures 0 <= b * c
    ensures power(power(a, b), c) == power(a, b * c)
  {
    lemma_mul_nonnegative(b, c);
    if c == 0 {
      lemma_mul_basics_auto();
      calc {
        power(a, b * c);
          { lemma_power_0(a); }
        1;
          { lemma_power_0(power(a, b)); }
        power(power(a, b), c);
      }
    }
    else {
      calc {
        b * c - b;
          { lemma_mul_basics_auto(); }
        b * c - b * 1;
          { lemma_mul_is_distributive_auto(); }
        b * (c - 1);
      }
      lemma_mul_nonnegative(b, c - 1);
      assert 0 <= b * c - b;

      calc {
        power(a, b * c);
        power(a, b + b * c - b);
          { lemma_power_adds(a, b, b * c - b); }
        power(a, b) * power(a, b * c - b);
        power(a, b) * power(a, b * (c - 1));
          { lemma_power_multiplies(a, b, c - 1); }
        power(a, b) * power(power(a, b), c - 1);
          { reveal_power(); }
        power(power(a, b), c);
      }
    }
  }

  lemma lemma_power_multiplies_auto()
    ensures forall b: nat, c: nat {:trigger b * c} :: 0 <= b * c
    ensures forall a: int, b: nat, c: nat {:trigger power(a, b * c)}
      :: power(power(a, b), c) == power(a, b * c)
  {
    reveal_power();
    lemma_mul_nonnegative_auto();
    forall a: int, b: nat, c: nat {:trigger power(a, b * c)}
      ensures power(power(a, b), c) == power(a, b * c)
    {
      lemma_power_multiplies(a, b, c);
    }
  }

  /* Distribute the power to factors of a product. */
  lemma lemma_power_distributes(a: int, b: int, e: nat)
    decreases e
    ensures power(a * b, e) == power(a, e) * power(b, e)
  {
    reveal_power();
    lemma_mul_basics_auto();
    if e > 0 {
      calc {
        power(a * b, e);
        (a * b) * power(a * b, e - 1);
          { lemma_power_distributes(a, b, e - 1); }
        (a * b) * (power(a, e - 1) * power(b, e - 1));
          { lemma_mul_is_associative_auto(); lemma_mul_is_commutative_auto(); }
        (a * power(a, e - 1)) * (b * power(b, e - 1));
        power(a, e) * power(b, e);
      }
    }
  }

  lemma lemma_power_distributes_auto()
    ensures forall a: int, b: int, e: nat {:trigger power(a * b, e)}
      :: power(a * b, e) == power(a, e) * power(b, e)
  {
    reveal_power();
    forall a: int, b: int, e: nat {:trigger power(a * b, e)}
      ensures power(a * b, e) == power(a, e) * power(b, e)
    {
      lemma_power_distributes(a, b, e);
    }
  }

  /* Group properties of powers. */
  lemma lemma_power_auto()
    ensures forall x: int {:trigger power(x, 0)} :: power(x, 0) == 1
    ensures forall x: int {:trigger power(x, 1)} :: power(x, 1) == x
    ensures forall x: int, y: int {:trigger power(x, y)} :: y == 0 ==> power(x, y) == 1
    ensures forall x: int, y: int {:trigger power(x, y)} :: y == 1 ==> power(x, y) == x
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y ==> x <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 1 < y ==> x < x * y
    ensures forall x: int, y: nat, z: nat {:trigger power(x, y + z)} :: power(x, y + z) == power(x, y) * power(x, z)
    ensures forall x: int, y: nat, z: nat {:trigger power(x, y - z)} :: y >= z ==> power(x, y - z) * power(x, z) == power(x, y)
    ensures forall x: int, y: int, z: nat {:trigger power(x * y, z)} :: power(x * y, z) == power(x, z) * power(y, z)
  {
    reveal_power();

    forall x: int
      ensures power(x, 0) == 1
      ensures power(x, 1) == x
    {
      lemma_power_0(x);
      lemma_power_1(x);
    }

    forall x: int, y: int, z: nat {:trigger power(x * y, z)}
      ensures power(x * y, z) == power(x, z) * power(y, z)
    {
      lemma_power_distributes(x, y, z);
    }

    forall x: int, y: nat, z: nat {:trigger power(x, y + z)}
      ensures power(x, y + z) == power(x, y) * power(x, z)
    {
      lemma_power_adds(x, y, z);
    }

    forall x: int, y: nat, z: nat {:trigger power(x, y - z)} | y >= z
      ensures power(x, y - z) * power(x, z) == power(x, y)
    {
      lemma_power_adds(x, y - z, z);
    }

    forall x: int, y: int {:trigger x * y} | 0 < x && 0 < y
      ensures x <= x * y
    {
      lemma_mul_auto();
      lemma_mul_increases_auto();
      lemma_mul_strictly_increases_auto();
    }

    forall x:int, y:int {:trigger x * y} | 0 < x && 1 < y
      ensures x < x * y
    {
      lemma_mul_auto();
      lemma_mul_increases_auto();
      lemma_mul_strictly_increases_auto();
    }
  }

  /* A positive number raised to a power strictly increases as the power
  strictly increases. */
  lemma lemma_power_strictly_increases(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires e1 < e2
    ensures power(b, e1) < power(b, e2)
  {
    lemma_power_auto();
    var f := e => 0 < e ==> power(b, e1) < power(b, e1 + e);
    forall i {:trigger is_le(0, i)} | is_le(0, i) && f(i)
      ensures f(i + 1)
    {
      calc {
        power(b, e1 + i);
        <= { lemma_power_positive(b, e1 + i);
             lemma_mul_left_inequality(power(b, e1 + i), 1, b); }
          power(b, e1 + i) * b;
        == { lemma_power_1(b); }
          power(b, e1 + i) * power(b, 1);
        == { lemma_power_adds(b, e1 + i, 1); }
          power(b, e1 + i + 1);
      }
    }
    lemma_mul_induction_auto(e2 - e1, f);
  }

  lemma lemma_power_strictly_increases_auto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger power(b, e1),
      power(b, e2)} :: (1 < b && e1 < e2) ==> power(b, e1) < power(b, e2)
  {
    reveal_power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | 1 < b && e1 < e2
      ensures power(b, e1) < power(b, e2)
    {
      lemma_power_strictly_increases(b, e1, e2);
    }
  }

  /* A positive number raised to a power increases as the power increases. */
  lemma lemma_power_increases(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures power(b, e1) <= power(b, e2)
  {
    lemma_power_auto();
    var f := e => 0 <= e ==> power(b, e1) <= power(b, e1 + e);
    forall i {:trigger is_le(0, i)} | is_le(0, i) && f(i)
      ensures f(i + 1)
    {
      calc {
        power(b, e1 + i);
        <= { lemma_power_positive(b, e1 + i);
             lemma_mul_left_inequality(power(b, e1 + i), 1, b); }
          power(b, e1 + i) * b;
        == { lemma_power_1(b); }
          power(b, e1 + i) * power(b, 1);
        == { lemma_power_adds(b, e1 + i, 1); }
          power(b, e1 + i + 1);
      }
    }
    lemma_mul_induction_auto(e2 - e1, f);
  }

  lemma lemma_power_increases_auto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger power(b, e1),
      power(b, e2)} :: (1 < b && e1 <= e2) ==> power(b, e1) <= power(b, e2)
  {
    reveal_power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | 1 < b && e1 <= e2
      ensures power(b, e1) <= power(b, e2)
    {
      lemma_power_increases(b, e1, e2);
    }
  }

  /* A power strictly increases as a positive number raised to the power
  strictly increases. */
  lemma lemma_power_strictly_increases_converse(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires power(b, e1) < power(b, e2)
    ensures e1 < e2
  {
    if e1 >= e2 {
      lemma_power_increases(b, e2, e1);
      assert false;
    }
  }

  lemma lemma_power_strictly_increases_converse_auto()
    ensures forall b: nat, e1: nat, e2: nat
      {:trigger power(b, e1), power(b, e2)}
      :: b > 0 && power(b, e1) < power(b, e2) ==> e1 < e2
  {
    reveal_power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | b > 0 && power(b, e1) < power(b, e2)
      ensures e1 < e2
    {
      lemma_power_strictly_increases_converse(b, e1, e2);
    }
  }

  /* A power increases as a positive number raised to the power increases. */
  lemma lemma_power_increases_converse(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires power(b, e1) <= power(b, e2)
    ensures e1 <= e2
  {
    if e1 > e2 {
      lemma_power_strictly_increases(b, e2, e1);
      assert false;
    }
  }

  lemma lemma_power_increases_converse_auto()
    ensures forall b: nat, e1: nat, e2: nat
      {:trigger power(b, e1), power(b, e2)}
      :: 1 < b && power(b, e1) <= power(b, e2) ==> e1 <= e2
  {
    reveal_power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | 1 < b && power(b, e1) <= power(b, e2)
      ensures e1 <= e2
    {
      lemma_power_increases_converse(b, e1, e2);
    }
  }

  /* (b^xy)^z = (b^x)^yz */
  lemma lemma_pull_out_powers(b: nat, x: nat, y: nat, z: nat)
    requires b > 0
    ensures 0 <= x * y
    ensures 0 <= y * z
    ensures power(power(b, x * y), z) == power(power(b, x), y * z)
  {
    lemma_mul_nonnegative(x, y);
    lemma_mul_nonnegative(y, z);
    lemma_power_positive(b, x);
    calc {
      power(power(b, x * y), z);
        { lemma_power_multiplies(b, x, y); }
      power(power(power(b, x), y), z);
        { lemma_power_multiplies(power(b, x), y, z); }
      power(power(b, x), y * z);
    }
  }

  lemma lemma_pull_out_powers_auto()
    ensures forall y: nat, z: nat {:trigger z * y} :: 0 <= z * y && 0 <= y * z
    ensures forall b: nat, x: nat, y: nat, z: nat
      {:trigger power(power(b, x * y), z)}
      :: b > 0 ==> power(power(b, x * y), z) == power(power(b, x), y * z)
  {
    reveal_power();
    lemma_mul_nonnegative_auto();
    forall b: nat, x: nat, y: nat, z: nat {:trigger power(power(b, x * y), z)}
      | b > 0 ensures power(power(b, x * y), z) == power(power(b, x), y * z)
    {
      lemma_pull_out_powers(b, x, y, z);
    }
  }

  /* Inequality due to smaller numerator, same denominator. */
  lemma lemma_power_division_inequality(x: nat, b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e2 <= e1
    requires x < power(b, e1)
    ensures power(b, e2) > 0
    ensures x / power(b, e2) < power(b, e1 - e2)
  {
    lemma_power_positive_auto();
    calc ==> {
      x / power(b, e2) >= power(b, e1 - e2);
        { lemma_mul_inequality(power(b, e1 - e2), x / power(b, e2), power(b, e2)); }
      x / power(b, e2) * power(b, e2) >= power(b, e1 - e2) * power(b, e2);
        { lemma_fundamental_div_mod(x, power(b, e2));
          lemma_mul_is_commutative_auto(); }
      x - x % power(b, e2) >= power(b, e1 - e2) * power(b, e2);
        { lemma_power_adds(b, e1 - e2, e2); }
      x - x % power(b, e2) >= power(b, e1);
        { lemma_mod_properties_auto(); }
      x >= power(b, e1);
      false;
    }
  }

  lemma lemma_power_division_inequality_auto()
    ensures forall b: nat, e2: nat :: b > 0 ==> power(b, e2) > 0
    ensures forall x: nat, b: nat, e1: nat, e2: nat
      {:trigger x / power(b, e2), power(b, e1 - e2)}
      :: b > 0 && e2 <= e1 && x < power(b, e1) ==>
         x / power(b, e2) < power(b, e1 - e2)
  {
    reveal_power();
    lemma_power_positive_auto();
    forall x: nat, b: nat, e1: nat, e2: nat
      {:trigger x / power(b, e2), power(b, e1 - e2)}
      | b > 0 && e2 <= e1 && x < power(b, e1)
      ensures x / power(b, e2) < power(b, e1 - e2)
    {
      lemma_power_division_inequality(x, b, e1, e2);
    }
  }

  /* b^e % b = 0 */
  lemma lemma_power_mod(b: nat, e: nat) 
    requires b > 0 && e > 0
    ensures power(b, e) % b == 0;
  {
    reveal power();
    calc {
      power(b, e) % b;
      (b * power(b, e - 1)) % b;
        { lemma_mul_is_associative_auto(); }
      (power(b, e - 1) * b) % b;
        {
          lemma_power_positive_auto();
          lemma_mod_multiples_basic(power(b, e-1) , b);
        }
      0;
    }
  }

  lemma lemma_power_mod_auto()
    ensures forall b: nat, e: nat {:trigger power(b, e)}
      :: b > 0 && e > 0 ==> power(b, e) % b == 0
  {
    reveal_power();
    forall b: nat, e: nat {:trigger power(b, e)} | b > 0 && e > 0
      ensures power(b, e) % b == 0
    {
      lemma_power_mod(b, e);
    }
  }

  /* ((b % e)^e) % m = b^e % m */
  lemma lemma_power_mod_noop(b: int, e: nat, m: int)
    decreases e
    requires m > 0
    ensures power(b % m, e) % m == power(b, e) % m
  {
    reveal power();
    lemma_mod_properties_auto();
    if e > 0 {
      calc {
        power(b % m, e) % m;
        ((b % m) * power(b % m, e - 1)) % m;
          { lemma_mul_mod_noop_general(b, power(b % m, e - 1), m); }
        ((b % m) * (power(b % m, e - 1) % m) % m) % m;
          { lemma_power_mod_noop(b, e - 1, m); }
        ((b % m) * (power(b, e - 1) % m) % m) % m;
          { lemma_mul_mod_noop_general(b, power(b, e - 1), m); }
        (b * (power(b, e - 1)) % m) % m;
        (b * (power(b, e - 1))) % m;
        power(b, e) % m;
      }
    }
  }

  lemma lemma_power_mod_noop_auto()
    ensures forall b: nat, e: nat, m: nat {:trigger power(b % m, e)}
      :: m > 0 ==> power(b % m, e) % m == power(b, e) % m
  {
    reveal_power();
    forall b: nat, e: nat, m: nat {:trigger power(b % m, e)}
      | m > 0 ensures power(b % m, e) % m == power(b, e) % m
    {
      lemma_power_mod_noop(b, e, m);
    }
  }

}
