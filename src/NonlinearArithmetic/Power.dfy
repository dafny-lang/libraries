// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/***********************************************************************************
*  Original: Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
************************************************************************************/

/* Every lemma comes in 2 forms: 'lemmaProperty' and 'lemmaPropertyAuto'. The former takes arguments and may 
be more stable and less reliant on Z3 heuristics. The latter includes automation and its use requires less effort */

include "DivMod.dfy"
include "../BasicMath.dfy"
include "Internals/GeneralInternals.dfy"
include "Mul.dfy"
include "Internals/MulInternals.dfy"

module Power {
  import opened DivMod
  import opened BasicMath
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
  lemma lemmaPower0(b: int)
    ensures power(b, 0) == 1
  {
    reveal power();
  }

  lemma lemmaPower0Auto()
    ensures forall b: nat {:trigger power(b, 0)} :: power(b, 0) == 1
  {
    reveal power();
    forall b: nat {:trigger power(b, 0)}
      ensures power(b, 0) == 1
    {
      lemmaPower0(b);
    }
  }

  /* A number raised to the power of 1 equals the number itself. */
  lemma lemmaPower1(b: int)
    ensures power(b, 1) == b
  {
    calc {
      power(b, 1);
        { reveal power(); }
      b * power(b, 0);
        { lemmaPower0(b); }
      b * 1;
        { lemmaMulBasicsAuto(); }
      b;
    }
  }

  lemma lemmaPower1Auto()
    ensures forall b: nat {:trigger power(b, 1)} :: power(b, 1) == b
  {
    reveal power();
    forall b: nat {:trigger power(b, 1)}
      ensures power(b, 1) == b
    {
      lemmaPower1(b);
    }
  }

  /* 0 raised to a positive power equals 0. */
  lemma lemma0Power(e: nat)
    requires e > 0
    ensures power(0, e) == 0
  {
    reveal power();
    lemmaMulBasicsAuto();
    if e != 1 {
      lemma0Power(e - 1);
    }
  }

  lemma lemma0PowerAuto()
    ensures forall e: nat {:trigger power(0, e)} :: e > 0 ==> power(0, e) == 0
  {
    reveal power();
    forall e: nat {:trigger power(0, e)} | e > 0
      ensures power(0, e) == 0
    {
      lemma0Power(e);
    }
  }

  /* 1 raised to any power equals 1. */
  lemma lemma1Power(e: nat)
    ensures power(1, e) == 1
  {
    reveal power();
    lemmaMulBasicsAuto();
    if e != 0 {
      lemma1Power(e - 1);
    }
  }

  lemma lemma1PowerAuto()
    ensures forall e: nat {:trigger power(1, e)} :: power(1, e) == 1
  {
    reveal power();
    forall e: nat {:trigger power(1, e)}
      ensures power(1, e) == 1
    {
      lemma1Power(e);
    }
  }

  /* Squaring a number is equal to raising it to the power of 2. */
  lemma lemmaSquareIsPower2(x: nat)
    ensures power(x, 2) == x * x
  {
    reveal power();
  }

  lemma lemmaSquareIsPower2Auto()
    ensures forall x: nat {:trigger power(x, 2)} :: power(x, 2) == x * x
  {
    reveal power();
    forall x: nat {:trigger power(x, 2)}
      ensures power(x, 2) == x * x
    {}
  }

  /* A positive number raised to any power is positive. */
  lemma lemmaPowerPositive(b: int, e: nat)
    requires b > 0
    ensures 0 < power(b, e)
  {
    lemmaMulIncreasesAuto();
    lemmaMulInductionAuto(e, u => 0 <= u ==> 0 < power(b, u));
  }

  lemma lemmaPowerPositiveAuto()
    ensures forall b: int, e: nat {:trigger power(b, e)}
      :: b > 0 ==> 0 < power(b, e)
  {
    reveal power();
    forall b: int, e: nat {:trigger power(b, e)} | b > 0
      ensures 0 < power(b, e)
    {
      lemmaPowerPositive(b, e);
    }
  }

  /* Add exponents when multiplying powers with the same base. */
  lemma lemmaPowerAdds(b: int, e1: nat, e2: nat)
    decreases e1
    ensures power(b, e1 + e2) == power(b, e1) * power(b, e2)
  {
    if e1 == 0 {
      calc {
        power(b, e1) * power(b, e2);
          { lemmaPower0(b); }
        1 * power(b, e2);
          { lemmaMulBasicsAuto(); }
        power(b, 0 + e2);
      }
    }
    else {
      calc {
        power(b, e1) * power(b, e2);
          { reveal power(); }
        (b * power(b, e1 - 1)) * power(b, e2);
          { lemmaMulIsAssociativeAuto(); }
        b * (power(b, e1 - 1) * power(b, e2));
          { lemmaPowerAdds(b, e1 - 1, e2); }
        b * power(b, e1 - 1 + e2);
          { reveal power(); }
        power(b, e1 + e2);
      }
    }
  }

  lemma lemmaPowerAddsAuto()
    ensures forall b: int, e1: nat, e2: nat {:trigger power(b, e1 + e2)}
      :: power(b, e1 + e2) == power(b, e1) * power(b, e2)
  {
    reveal power();
    forall b: int, e1: nat, e2: nat {:trigger power(b, e1 + e2)}
      ensures power(b, e1 + e2) == power(b, e1) * power(b, e2)
    {
      lemmaPowerAdds(b, e1, e2);
    }
  }

  /* Subtract exponents when dividing powers. */
  lemma lemmaPowerSubtracts(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures power(b, e1) > 0
    ensures power(b, e2 - e1) == power(b, e2) / power(b, e1) > 0
  {
    lemmaPowerPositiveAuto();
    calc {
      power(b, e2) / power(b, e1);
        { lemmaPowerAdds(b, e2 - e1, e1); }
      power(b, e2 - e1) * power(b, e1) / power(b, e1);
        { lemmaDivByMultiple(power(b, e2 - e1), power(b, e1)); }
      power(b, e2 - e1);
    }
  }

  lemma lemmaPowerSubtractsAuto()
    ensures forall b: nat, e1: nat :: b > 0 ==> power(b, e1) > 0
    ensures forall b: nat, e1: nat, e2: nat {:trigger power(b, e2 - e1)}
      :: b > 0 && e1 <= e2 ==>
         power(b, e2 - e1) == power(b, e2) / power(b, e1) > 0
  {
    reveal power();
    lemmaPowerPositiveAuto();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e2 - e1)}
      | b > 0 && e1 <= e2
      ensures power(b, e2 - e1) == power(b, e2) / power(b, e1) > 0
    {
      lemmaPowerSubtracts(b, e1, e2);
    }
  }

  /* Multiply exponents when finding the power of a power. */
  lemma lemmaPowerMultiplies(a: int, b: nat, c: nat)
    decreases c
    ensures 0 <= b * c
    ensures power(power(a, b), c) == power(a, b * c)
  {
    lemmaMulNonnegative(b, c);
    if c == 0 {
      lemmaMulBasicsAuto();
      calc {
        power(a, b * c);
          { lemmaPower0(a); }
        1;
          { lemmaPower0(power(a, b)); }
        power(power(a, b), c);
      }
    }
    else {
      calc {
        b * c - b;
          { lemmaMulBasicsAuto(); }
        b * c - b * 1;
          { lemmaMulIsDistributiveAuto(); }
        b * (c - 1);
      }
      lemmaMulNonnegative(b, c - 1);
      assert 0 <= b * c - b;

      calc {
        power(a, b * c);
        power(a, b + b * c - b);
          { lemmaPowerAdds(a, b, b * c - b); }
        power(a, b) * power(a, b * c - b);
        power(a, b) * power(a, b * (c - 1));
          { lemmaPowerMultiplies(a, b, c - 1); }
        power(a, b) * power(power(a, b), c - 1);
          { reveal power(); }
        power(power(a, b), c);
      }
    }
  }

  lemma lemmaPowerMultipliesAuto()
    ensures forall b: nat, c: nat {:trigger b * c} :: 0 <= b * c
    ensures forall a: int, b: nat, c: nat {:trigger power(a, b * c)}
      :: power(power(a, b), c) == power(a, b * c)
  {
    reveal power();
    lemmaMulNonnegativeAuto();
    forall a: int, b: nat, c: nat {:trigger power(a, b * c)}
      ensures power(power(a, b), c) == power(a, b * c)
    {
      lemmaPowerMultiplies(a, b, c);
    }
  }

  /* Distribute the power to factors of a product. */
  lemma lemmaPowerDistributes(a: int, b: int, e: nat)
    decreases e
    ensures power(a * b, e) == power(a, e) * power(b, e)
  {
    reveal power();
    lemmaMulBasicsAuto();
    if e > 0 {
      calc {
        power(a * b, e);
        (a * b) * power(a * b, e - 1);
          { lemmaPowerDistributes(a, b, e - 1); }
        (a * b) * (power(a, e - 1) * power(b, e - 1));
          { lemmaMulIsAssociativeAuto(); lemmaMulIsCommutativeAuto(); }
        (a * power(a, e - 1)) * (b * power(b, e - 1));
        power(a, e) * power(b, e);
      }
    }
  }

  lemma lemmaPowerDistributesAuto()
    ensures forall a: int, b: int, e: nat {:trigger power(a * b, e)}
      :: power(a * b, e) == power(a, e) * power(b, e)
  {
    reveal power();
    forall a: int, b: int, e: nat {:trigger power(a * b, e)}
      ensures power(a * b, e) == power(a, e) * power(b, e)
    {
      lemmaPowerDistributes(a, b, e);
    }
  }

  /* Group properties of powers. */
  lemma lemmaPowerAuto()
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
    reveal power();

    lemmaPower0Auto();
    lemmaPower1Auto();

    lemmaPowerDistributesAuto();
    lemmaPowerAddsAuto();

    forall x: int, y: nat, z: nat {:trigger power(x, y - z)} | y >= z
      ensures power(x, y - z) * power(x, z) == power(x, y)
    {
      lemmaPowerAdds(x, y - z, z);
    }

    lemmaMulAuto();
    lemmaMulIncreasesAuto();
    lemmaMulStrictlyIncreasesAuto();
  }

  /* A positive number raised to a power strictly increases as the power
  strictly increases. */
  lemma lemmaPowerStrictlyIncreases(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires e1 < e2
    ensures power(b, e1) < power(b, e2)
  {
    lemmaPowerAuto();
    var f := e => 0 < e ==> power(b, e1) < power(b, e1 + e);
    forall i {:trigger isLe(0, i)} | isLe(0, i) && f(i)
      ensures f(i + 1)
    {
      calc {
        power(b, e1 + i);
        <= { lemmaPowerPositive(b, e1 + i);
             lemmaMulLeftInequality(power(b, e1 + i), 1, b); }
          power(b, e1 + i) * b;
        == { lemmaPower1(b); }
          power(b, e1 + i) * power(b, 1);
        == { lemmaPowerAdds(b, e1 + i, 1); }
          power(b, e1 + i + 1);
      }
    }
    lemmaMulInductionAuto(e2 - e1, f);
  }

  lemma lemmaPowerStrictlyIncreasesAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger power(b, e1),
      power(b, e2)} :: (1 < b && e1 < e2) ==> power(b, e1) < power(b, e2)
  {
    reveal power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | 1 < b && e1 < e2
      ensures power(b, e1) < power(b, e2)
    {
      lemmaPowerStrictlyIncreases(b, e1, e2);
    }
  }

  /* A positive number raised to a power increases as the power increases. */
  lemma lemmaPowerIncreases(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e1 <= e2
    ensures power(b, e1) <= power(b, e2)
  {
    lemmaPowerAuto();
    var f := e => 0 <= e ==> power(b, e1) <= power(b, e1 + e);
    forall i {:trigger isLe(0, i)} | isLe(0, i) && f(i)
      ensures f(i + 1)
    {
      calc {
        power(b, e1 + i);
        <= { lemmaPowerPositive(b, e1 + i);
             lemmaMulLeftInequality(power(b, e1 + i), 1, b); }
          power(b, e1 + i) * b;
        == { lemmaPower1(b); }
          power(b, e1 + i) * power(b, 1);
        == { lemmaPowerAdds(b, e1 + i, 1); }
          power(b, e1 + i + 1);
      }
    }
    lemmaMulInductionAuto(e2 - e1, f);
  }

  lemma lemmaPowerIncreasesAuto()
    ensures forall b: nat, e1: nat, e2: nat {:trigger power(b, e1),
      power(b, e2)} :: (1 < b && e1 <= e2) ==> power(b, e1) <= power(b, e2)
  {
    reveal power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | 1 < b && e1 <= e2
      ensures power(b, e1) <= power(b, e2)
    {
      lemmaPowerIncreases(b, e1, e2);
    }
  }

  /* A power strictly increases as a positive number raised to the power
  strictly increases. */
  lemma lemmaPowerStrictlyIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires b > 0
    requires power(b, e1) < power(b, e2)
    ensures e1 < e2
  {
    if e1 >= e2 {
      lemmaPowerIncreases(b, e2, e1);
      assert false;
    }
  }

  lemma lemmaPowerStrictlyIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat
      {:trigger power(b, e1), power(b, e2)}
      :: b > 0 && power(b, e1) < power(b, e2) ==> e1 < e2
  {
    reveal power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | b > 0 && power(b, e1) < power(b, e2)
      ensures e1 < e2
    {
      lemmaPowerStrictlyIncreasesConverse(b, e1, e2);
    }
  }

  /* A power increases as a positive number raised to the power increases. */
  lemma lemmaPowerIncreasesConverse(b: nat, e1: nat, e2: nat)
    requires 1 < b
    requires power(b, e1) <= power(b, e2)
    ensures e1 <= e2
  {
    if e1 > e2 {
      lemmaPowerStrictlyIncreases(b, e2, e1);
      assert false;
    }
  }

  lemma lemmaPowerIncreasesConverseAuto()
    ensures forall b: nat, e1: nat, e2: nat
      {:trigger power(b, e1), power(b, e2)}
      :: 1 < b && power(b, e1) <= power(b, e2) ==> e1 <= e2
  {
    reveal power();
    forall b: nat, e1: nat, e2: nat {:trigger power(b, e1), power(b, e2)}
      | 1 < b && power(b, e1) <= power(b, e2)
      ensures e1 <= e2
    {
      lemmaPowerIncreasesConverse(b, e1, e2);
    }
  }

  /* (b^xy)^z = (b^x)^yz */
  lemma lemmaPullOutPowers(b: nat, x: nat, y: nat, z: nat)
    requires b > 0
    ensures 0 <= x * y
    ensures 0 <= y * z
    ensures power(power(b, x * y), z) == power(power(b, x), y * z)
  {
    lemmaMulNonnegative(x, y);
    lemmaMulNonnegative(y, z);
    lemmaPowerPositive(b, x);
    calc {
      power(power(b, x * y), z);
        { lemmaPowerMultiplies(b, x, y); }
      power(power(power(b, x), y), z);
        { lemmaPowerMultiplies(power(b, x), y, z); }
      power(power(b, x), y * z);
    }
  }

  lemma lemmaPullOutPowersAuto()
    ensures forall y: nat, z: nat {:trigger z * y} :: 0 <= z * y && 0 <= y * z
    ensures forall b: nat, x: nat, y: nat, z: nat
      {:trigger power(power(b, x * y), z)}
      :: b > 0 ==> power(power(b, x * y), z) == power(power(b, x), y * z)
  {
    reveal power();
    lemmaMulNonnegativeAuto();
    forall b: nat, x: nat, y: nat, z: nat {:trigger power(power(b, x * y), z)}
      | b > 0 ensures power(power(b, x * y), z) == power(power(b, x), y * z)
    {
      lemmaPullOutPowers(b, x, y, z);
    }
  }

  /* Inequality due to smaller numerator, same denominator. */
  lemma lemmaPowerDivisionInequality(x: nat, b: nat, e1: nat, e2: nat)
    requires b > 0
    requires e2 <= e1
    requires x < power(b, e1)
    ensures power(b, e2) > 0
    ensures x / power(b, e2) < power(b, e1 - e2)
  {
    lemmaPowerPositiveAuto();
    calc ==> {
      x / power(b, e2) >= power(b, e1 - e2);
        { lemmaMulInequality(power(b, e1 - e2), x / power(b, e2), power(b, e2)); }
      x / power(b, e2) * power(b, e2) >= power(b, e1 - e2) * power(b, e2);
        { lemmaFundamentalDivMod(x, power(b, e2));
          lemmaMulIsCommutativeAuto(); }
      x - x % power(b, e2) >= power(b, e1 - e2) * power(b, e2);
        { lemmaPowerAdds(b, e1 - e2, e2); }
      x - x % power(b, e2) >= power(b, e1);
        { lemmaModPropertiesAuto(); }
      x >= power(b, e1);
      false;
    }
  }

  lemma lemmaPowerDivisionInequalityAuto()
    ensures forall b: nat, e2: nat :: b > 0 ==> power(b, e2) > 0
    ensures forall x: nat, b: nat, e1: nat, e2: nat
      {:trigger x / power(b, e2), power(b, e1 - e2)}
      :: b > 0 && e2 <= e1 && x < power(b, e1) ==>
         x / power(b, e2) < power(b, e1 - e2)
  {
    reveal power();
    lemmaPowerPositiveAuto();
    forall x: nat, b: nat, e1: nat, e2: nat
      {:trigger x / power(b, e2), power(b, e1 - e2)}
      | b > 0 && e2 <= e1 && x < power(b, e1)
      ensures x / power(b, e2) < power(b, e1 - e2)
    {
      lemmaPowerDivisionInequality(x, b, e1, e2);
    }
  }

  /* b^e % b = 0 */
  lemma lemmaPowerMod(b: nat, e: nat) 
    requires b > 0 && e > 0
    ensures power(b, e) % b == 0;
  {
    reveal power();
    calc {
      power(b, e) % b;
      (b * power(b, e - 1)) % b;
        { lemmaMulIsAssociativeAuto(); }
      (power(b, e - 1) * b) % b;
        {
          lemmaPowerPositiveAuto();
          lemmaModMultiplesBasic(power(b, e-1) , b);
        }
      0;
    }
  }

  lemma lemmaPowerModAuto()
    ensures forall b: nat, e: nat {:trigger power(b, e)}
      :: b > 0 && e > 0 ==> power(b, e) % b == 0
  {
    reveal power();
    forall b: nat, e: nat {:trigger power(b, e)} | b > 0 && e > 0
      ensures power(b, e) % b == 0
    {
      lemmaPowerMod(b, e);
    }
  }

  /* ((b % e)^e) % m = b^e % m */
  lemma lemmaPowerModNoop(b: int, e: nat, m: int)
    decreases e
    requires m > 0
    ensures power(b % m, e) % m == power(b, e) % m
  {
    reveal power();
    lemmaModPropertiesAuto();
    if e > 0 {
      calc {
        power(b % m, e) % m;
        ((b % m) * power(b % m, e - 1)) % m;
          { lemmaMulModNoopGeneral(b, power(b % m, e - 1), m); }
        ((b % m) * (power(b % m, e - 1) % m) % m) % m;
          { lemmaPowerModNoop(b, e - 1, m); }
        ((b % m) * (power(b, e - 1) % m) % m) % m;
          { lemmaMulModNoopGeneral(b, power(b, e - 1), m); }
        (b * (power(b, e - 1)) % m) % m;
        (b * (power(b, e - 1))) % m;
        power(b, e) % m;
      }
    }
  }

  lemma lemmaPowerModNoopAuto()
    ensures forall b: nat, e: nat, m: nat {:trigger power(b % m, e)}
      :: m > 0 ==> power(b % m, e) % m == power(b, e) % m
  {
    reveal power();
    forall b: nat, e: nat, m: nat {:trigger power(b % m, e)}
      | m > 0 ensures power(b % m, e) % m == power(b, e) % m
    {
      lemmaPowerModNoop(b, e, m);
    }
  }

}
