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

include "Internals/DivInternalsNonlinear.dfy"
include "Internals/DivInternals.dfy"
include "Internals/GeneralInternals.dfy"

module DivMod {

  import opened DivInternals
  import DivINL = DivInternalsNonlinear
  import opened ModInternals
  import ModINL = ModInternalsNonlinear
  import opened MulInternals
  import opened Mul
  import opened GeneralInternals

  /**************************************************************************************************
  * Division:
  **************************************************************************************************/

  /* the common syntax of division gives the same quotient as performing division through recursion */
  lemma lemmaDivIsDivRecursive(x: int, d: int)
    requires 0 < d
    ensures divRecursive(x, d) == x / d
  {
    reveal divRecursive();
    lemmaDivInductionAuto(d, x, u => divRecursive(u, d) == u / d);
  }

  lemma lemmaDivIsDivRecursiveAuto()
    ensures forall x: int, d: int {:trigger x / d} :: d > 0 ==> divRecursive(x, d) == x / d
  {
    reveal divRecursive();
    forall x: int, d: int | d > 0
      ensures divRecursive(x, d) == x / d
    {
      lemmaDivIsDivRecursive(x, d);
    }
  }

  /* the quotient of an integer divided by itself is 1 */
  lemma lemmaDivBySelf(d: int)
    requires d != 0
    ensures d / d == 1
  { 
    DivINL.lemmaDivBySelf(d);
  }

  /* zero divided by an integer besides 0 is 0 */
  lemma lemmaDivOf0(d: int)
    requires d != 0
    ensures 0 / d == 0
  { 
    DivINL.lemmaDivOf0(d);
  }

  /* ensures the basic propoerties of division: 0 divided by any integer is 0; any integer 
  divided by 1 is itself; any integer divided by itself is 1 */
  lemma lemmaDivBasics(x: int)
    ensures x != 0 ==> 0 / x == 0
    ensures x / 1 == x
    ensures x != 0 ==> x / x == 1
  {
    if (x != 0) {
      lemmaDivBySelf(x);
      lemmaDivOf0(x);
    }
  }
    
  lemma lemmaDivBasicsAuto()
    ensures forall x {:trigger 0 / x} :: x != 0 ==> 0 / x == 0
    ensures forall x {:trigger x / 1} :: x / 1 == x
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y >= 0
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y <= x
  {
    forall x: int
      ensures x != 0 ==> 0 / x == 0
      ensures x / 1 == x
    {
      lemmaDivBasics(x);
    }
    forall x: int, y: int | x >= 0 && y > 0
      ensures x / y >= 0
      ensures x / y <= x
    {
      lemmaDivPosIsPos(x, y);
      lemmaDivIsOrderedByDenominator(x, 1, y);
    }
  }

  /* if a dividend is a whole number and the divisor is a natural number and their
  quotient is 0, this implies that the dividend is smaller than the divisor */
  lemma lemmaSmallDivConverseAuto()
    ensures forall x, d {:trigger x / d } :: 0 <= x && 0 < d && x / d == 0 ==> x < d
  {
    forall x, d | 0 <= x && 0 < d && x / d == 0
      ensures x < d
    {
      lemmaDivInductionAuto(d, x, u => 0 <= u && 0 < d && u / d == 0 ==> u < d);
    }
  }

  /* given two fractions with the same numerator, the order of numbers is determined by 
  the denominators. However, if the numerator is 0, the fractions are equal regardless of 
  the denominators' values */
  lemma lemmaDivIsOrderedByDenominator(x: int, y: int, z: int)
    requires 0 <= x
    requires 1 <= y <= z
    ensures x / y >= x / z
    decreases x
  {
    reveal divRecursive();
    lemmaDivIsDivRecursiveAuto();
    assert forall u: int, d: int {:trigger u / d} {:trigger divRecursive(u, d)} 
      :: d > 0 ==> divRecursive(u, d) == u / d;

    if (x < z)
    {
      lemmaDivIsOrdered(0, x, y);
    }
    else
    {
      lemmaDivIsOrdered(x - z, x - y, y);
      lemmaDivIsOrderedByDenominator(x - z, y, z);
    }
  }

  lemma lemmaDivIsOrderedByDenominatorAuto()
    ensures forall x: int, y: int, z: int {:trigger x / y, x / z} :: 0 <= x && 1 <= y <= z ==> x / y >= x / z
  {
    forall (x: int, y: int, z: int | 0 <= x && 1 <= y <= z)
      ensures x / y >= x / z
    {
      lemmaDivIsOrderedByDenominator(x, y, z);
    }
  }

  /* given two fractions with the same numerator, the order of numbers is strictly determined by 
  the denominators.*/
  lemma lemmaDivIsStrictlyOrderedByDenominator(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d  < x
    decreases x
  {
    lemmaDivInductionAuto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma lemmaDivIsStrictlyOrderedByDenominatorAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall (x: int, d: int | 0 < x && 1 < d )
      ensures x / d < x
    {
      lemmaDivIsStrictlyOrderedByDenominator(x, d);
    }
  }

  /* Rounding is different when multiplying the sum of two integers by a fraction d/d vs. 
  first multiplying each integer by d/d and then adding the quotients */
  lemma lemmaDividingSums(a: int, b: int, d: int, R: int)
    requires 0 < d
    requires R == a % d + b % d - (a + b) % d
    ensures d * ((a + b) / d) - R == d * (a / d) + d * (b / d)
  {
    calc ==> {
      a % d + b % d == R + (a + b) % d;
      (a + b) - (a + b) % d - R == a - (a % d) + b - (b % d);
        {
          lemmaFundamentalDivMod(a + b, d);
          lemmaFundamentalDivMod(a, d);
          lemmaFundamentalDivMod(b, d);
        }
      d * ((a + b) / d) - R == d * (a / d) + d * (b / d);
    }
  }

  lemma lemmaDividingSumsAuto()
    ensures forall a: int, b: int, d: int, R: int {:trigger d * ((a + b) / d) - R, d*(a/d) + d*(b/d)}
        :: 0 < d &&  R == a%d + b%d - (a+b)%d ==> d*((a+b)/d) - R == d*(a/d) + d*(b/d)
  {
    forall (a: int, b: int, d: int, R: int | 0< d &&  R == a%d + b%d - (a+b)%d)
      ensures d*((a+b)/d) - R == d*(a/d) + d*(b/d)
    {
      lemmaDividingSums(a, b, d, R);
    }
  }

  /* dividing a whole number by a natural number will result in a quotient that is 
  greater than or equal to 0 */
  lemma lemmaDivPosIsPos(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x / d
  {
    lemmaDivInductionAuto(d, x, u => 0 <= u ==> u / d >= 0);
  }

  lemma lemmaDivPosIsPosAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> 0 <= x / d
  {
    forall (x: int, d: int | 0 <= x && 0 < d)
      ensures 0 <= x / d
    {
      lemmaDivPosIsPos(x, d);
    }
  }

  /* dividing an integer and then adding 1 to the quotient is the same as adding 
  the divisor and the integer, and then dividing that sum by the divisor */
  lemma lemmaDivPlusOne(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
  {
    lemmaDivAuto(d);
  }

  lemma lemmaDivPlusOneAuto()
    ensures forall x: int, d: int {:trigger 1 + x / d, (d + x) / d} :: 0 < d ==> 1 + x / d == (d + x) / d
  {
    forall (x: int, d: int | 0 < d)
      ensures 1 + x / d == (d + x) / d
    {
      lemmaDivPlusOne(x, d);
    }
  }

  /* dividing an integer and then subtracting 1 from the quotient is the same as subtracting 
  the divisor from the integer, and then dividing that difference by the divisor */
  lemma lemmaDivMinusOne(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
  {
    lemmaDivAuto(d);
  }

  lemma lemmaDivMinusOneAuto()
    ensures forall x: int, d: int {:trigger -1 + x / d, (-d + x) / d} :: 0 < d ==> -1 + x / d == (-d + x) / d
  {
    forall (x: int, d: int | 0 < d)
      ensures -1 + x / d == (-d + x) / d
    {
      lemmaDivMinusOne(x, d);
    }
  }

  /* dividing a smaller integer by a larger integer results in a quotient of 0 */
  lemma lemmaBasicDiv(d: int)
    requires 0 < d
    ensures forall x {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    lemmaDivAuto(d);
  }

  lemma lemmaBasicDivAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    forall (x: int, d: int | 0 <= x < d)
      ensures x / d == 0
    {
      lemmaBasicDiv(d);
    }
  }

  /* numerical order is preserved when dividing two seperate integers by a common positive divisor */
  lemma lemmaDivIsOrdered(x: int, y: int, z: int)
    requires x <= y
    requires 0 < z
    ensures x / z <= y / z
  {
    lemmaDivInductionAuto(z, x - y, xy => xy <= 0 ==> (xy + y) / z <= y / z);
  }

  lemma lemmaDivIsOrderedAuto()
    ensures forall x: int, y: int, z: int {:trigger x / z, y / z} :: x <= y && 0 < z ==> x / z <= y / z
  {
    forall (x: int, y: int, z: int | x <= y && 0 < z)
      ensures x / z <= y / z
    {
      lemmaDivIsOrdered(x, y, z);
    }
  }

  /* dividing an integer by 2 or more results in a quotient that is smaller than the 
  original dividend */
  lemma lemmaDivDecreases(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d  < x
  {
    lemmaDivInductionAuto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma lemmaDivDecreasesAuto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall (x: int, d: int | 0 < x && 1 < d)
      ensures x / d < x
    {
      lemmaDivDecreases(x, d);
    }
  }

  /* dividing an integer by 1 or more results in a quotient that is less than or equal to 
  the original dividend */
  lemma lemmaDivNonincreasing(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x / d  <= x
  {
    lemmaDivInductionAuto(d, x, u => 0 <= u ==> u / d <= u);
  }

  lemma lemmaDivNonincreasingAuto()
    ensures forall x: int, d: int {:trigger x / d } :: 0 <= x && 0 < d ==> x / d <= x
  {
    forall (x: int, d: int | 0 <= x && 0 < d)
      ensures x / d <= x 
    {
      lemmaDivNonincreasing(x, d);
    }
  }

  /* a natural number x divided by a larger natural number gives a remainder equal to x */
  lemma lemmaSmallMod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
  {
    ModINL.lemmaSmallMod(x, m);
  }

  lemma lemmaBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures 0 < y * z
    ensures x % (y * z) ==y * ((x / y) % z) + x % y
  {
    lemmaMulStrictlyPositiveAuto();
    lemmaDivPosIsPos(x, y);
    assert 0 <= x / y;

    calc {
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
        <=    { lemmaPartBound1(x, y, z); }
      y * (z - 1) + (x % y) % (y * z);
        <    { lemmaPartBound2(x, y, z); }
      y * (z - 1) + y;
            { lemmaMulBasicsAuto(); }
      y * (z - 1) + y * 1;
            { lemmaMulIsDistributiveAuto(); }
      y * (z - 1 + 1);
      y * z;
    }

    calc {
      x % (y * z);
            { lemmaFundamentalDivMod(x,y); }
      (y * (x / y) + x % y) % (y * z);
            {
              lemmaModPropertiesAuto();
              assert 0 <= x % y;
              lemmaMulNonnegative(y, x / y);
              assert (y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z;
              lemmaModAdds(y * (x / y), x % y, y * z);
            }
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
            {
              lemmaModPropertiesAuto();
              lemmaMulIncreases(z, y);
              lemmaMulIsCommutativeAuto();
              assert x % y < y <= y * z;
              lemmaSmallMod(x % y, y * z);
              assert (x % y) % (y * z) == x % y;
            }
      (y * (x / y)) % (y * z) + x % y;
            { lemmaTruncateMiddle(x / y, y, z); }
      y * ((x / y) % z) + x % y;
    }
  }

  lemma lemmaBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % (y * z), y * ((x / y) % z) + x % y} 
        :: 0 <= x && 0 < y && 0 < z ==> 0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y
  {
    forall (x: int, y: int, z: int  | 0 <= x && 0 < y && 0 < z)
      ensures 0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y
    {
      lemmaBreakdown(x, y, z);
    }
  }
  
  lemma lemmaRemainderUpper(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x - d < x / d * d
  {
    lemmaMulAuto();
    lemmaDivInductionAuto(d, x, u => 0 <= u ==> u - d < u / d * d);
  }

  lemma lemmaRemainderUpperAuto()
    ensures forall x: int, d: int {:trigger x - d, d * d} :: 0 <= x && 0 < d ==> x - d < x / d * d
  {
    forall (x: int, d: int | 0 <= x && 0 < d)
      ensures x - d < x / d * d
    {
      lemmaRemainderUpper(x, d);
    }
  }
  
  lemma lemmaRemainderLower(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures  x >= x / d * d
  {
    lemmaMulAuto();
    lemmaDivInductionAuto(d, x, u => 0 <= u ==> u >= u / d * d);
  }

  lemma lemmaRemainderLowerAuto()
    ensures forall x: int, d: int {:trigger x / d * d} :: 0 <= x && 0 < d ==> x >= x / d * d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x >= x / d * d
    {
      lemmaRemainderLower(x, d);
    }
  }
  
  lemma lemmaRemainder(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures  0 <= x - (x / d * d) < d
  {
    lemmaMulAuto();
    lemmaDivInductionAuto(d, x, u => 0 <= u - u / d * d < d);
  }

  lemma lemmaRemainderAuto()
    ensures forall x: int, d: int {:trigger x - (x / d * d)} :: 0 <= x && 0 < d ==> 0 <= x - (x / d * d) < d
  {
    forall x: int, d: int | 0 <= x && 0 < d 
      ensures 0 <= x - (x / d * d) < d
    {
      lemmaRemainder(x, d);
    }
  }

 /* describes fundementals of the modulus operator */
  lemma lemmaFundamentalDivMod(x: int, d: int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
  {
    ModINL.lemmaFundamentalDivMod(x, d);
  }

  lemma lemmaFundamentalDivModAuto()
    ensures forall x: int, d: int {:trigger d * (x / d) + (x % d)} :: d != 0 ==> x == d * (x / d) + (x % d) 
  {
    forall x: int, d: int | d != 0
      ensures x == d * (x / d) + (x % d)
    {
      lemmaFundamentalDivMod(x, d);
    }
  }

  /* dividing a fraction by a divisor is equivalent to multiplying the fraction's 
  denominator with the divisor */
  lemma lemmaDivDenominator(x: int,c: nat,d: nat)
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    ensures c * d != 0
    ensures (x / c) / d == x / (c * d)
  {
    lemmaMulStrictlyPositiveAuto();
    var R := x % (c * d);
    lemmaModPropertiesAuto();

    lemmaDivPosIsPos(R, c);
    if (R / c >= d) {
      lemmaFundamentalDivMod(R, c);
      lemmaMulInequality(d, R / c, c);
      lemmaMulIsCommutativeAuto();
      assert false;
    }
    assert R / c < d;

    lemmaMulBasicsAuto();
    lemmaFundamentalDivModConverse(R / c, d, 0, R / c);
    assert (R / c) % d == R / c;

    lemmaFundamentalDivMod(R, c);
    assert c * (R / c) + R % c == R;

    assert c * ((R / c) % d) + R % c == R;

    var k := x / (c * d);
    lemmaFundamentalDivMod(x, c * d);
    assert x == (c * d) * (x / (c * d)) + x % (c * d);
    assert R == x - (c * d) * (x / (c * d));
    assert R == x - (c * d) * k;

    calc {
      c * ((x / c) % d) + x % c;
        { lemmaModMultiplesVanish(-k, x / c, d); lemmaMulIsCommutativeAuto(); }
      c * ((x / c + (-k) * d) % d) + x % c;
        { lemmaHoistOverDenominator(x, (-k)*d, c); }
      c * (((x + (((-k) * d) * c)) / c) % d) + x % c;
        { lemmaMulIsAssociative(-k, d, c); }
      c * (((x + ((-k) * (d * c))) / c) % d) + x % c;
        { lemmaMulUnaryNegation(k, d * c); }
      c * (((x + (-(k * (d * c)))) / c) % d) + x % c;
        { lemmaMulIsAssociative(k, d, c); }
      c * (((x + (-(k * d * c))) / c) % d) + x % c;
      c * (((x - k * d * c) / c) % d) + x % c;
        {
          lemmaMulIsAssociativeAuto();
          lemmaMulIsCommutativeAuto();
        }
      c * ((R / c) % d) + x % c;
      c * (R / c) + x % c;
        { lemmaFundamentalDivMod(R, c);
          assert R == c * (R / c) + R % c;
          lemmaModMod(x, c, d);
          assert R % c == x % c;
        }
      R;
        { lemmaModIsModRecursiveAuto(); }
      R % (c * d);
      (x - (c * d) * k) % (c * d);
        { lemmaMulUnaryNegation(c * d, k); }
      (x + (c * d) * (-k)) % (c * d);
        { lemmaModMultiplesVanish(-k, x, c * d); }
      x % (c * d);
    }
    calc ==> {
      c * (x / c) + x % c - R == c * (x / c) - c * ((x / c) % d);
        { lemmaFundamentalDivMod(x, c); }
      x - R == c * (x / c) - c * ((x / c) % d);
    }
    calc ==> {
      true;
        { lemmaFundamentalDivMod(x / c, d); }
      d * ((x / c) / d) == x / c - ((x / c) % d);
      c * (d * ((x / c) / d)) == c * (x / c - ((x / c) % d));
        { lemmaMulIsAssociativeAuto(); }
      (c * d) * ((x / c) / d) == c * (x / c - ((x / c) % d));
        { lemmaMulIsDistributiveAuto(); }
      (c * d) * ((x / c) / d) == c * (x / c) - c * ((x / c) % d);
      (c * d) * ((x / c) / d) == x - R;
        { lemmaFundamentalDivMod(x, c * d); }
      (c * d) * ((x / c) / d) == (c * d) * (x / (c * d)) + x % (c * d) - R;
      (c * d) * ((x / c) / d) == (c * d) * (x / (c * d));
        { lemmaMulEqualityConverse(c * d, (x / c) / d, x / (c * d)); }
      (x / c) / d == x / (c * d);
    }
  }
  
  lemma lemmaDivDenominatorAuto()
    ensures forall c: nat, d: nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0
    ensures forall x: int, c: nat, d: nat {:trigger (x / c) / d} 
      :: 0 <= x && 0 < c && 0 < d ==> (x / c) / d == x / (c * d)
  {
    lemmaMulNonzeroAuto();
    forall x: int, c: nat, d: nat | 0 <= x && 0 < c && 0 < d
      ensures (x / c) / d == x / (c * d)
    {
      lemmaDivDenominator(x, c, d);
    }
  }

  /* multiplying an integer by a fraction is equivalent to multiplying the integer by the
  fraction's numerator */
  lemma lemmaMulHoistInequality(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < z
    ensures x * (y / z) <= (x * y) / z
  {
    calc {
      (x * y) / z;
        { lemmaFundamentalDivMod(y, z); }
      (x * (z * (y / z) + y % z)) / z;
        { lemmaMulIsDistributiveAuto(); }
      (x * (z * (y / z)) + x * (y % z)) / z;
        >=  {
            lemmaModPropertiesAuto();
            lemmaMulNonnegative(x, y % z);
            lemmaDivIsOrdered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z); }
      (x * (z * (y / z))) / z;
          { lemmaMulIsAssociativeAuto();
            lemmaMulIsCommutativeAuto(); }
      (z * (x * (y / z))) / z;
          { lemmaDivMultiplesVanish(x * (y / z), z); }
      x * (y / z);
    }
  }
  
  lemma lemmaMulHoistInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y / z), (x * y) / z} 
      :: 0 <= x && 0 < z ==> x * (y / z) <= (x * y) / z
  {
    forall (x: int, y: int, z: int | 0 <= x && 0 < z)
      ensures x * (y / z) <= (x * y) / z
    {
      lemmaMulHoistInequality(x, y, z);
    }
  }

  lemma lemmaIndistinguishableQuotients(a: int, b: int, d: int)
    requires 0 < d
    requires 0 <= a - a % d <= b < a + d - a % d
    ensures a / d == b / d
  {
    lemmaDivInductionAuto(d, a - b, ab => var u := ab + b; 0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d);
  }

  lemma lemmaIndistinguishableQuotientsAuto()
    ensures forall a: int, b: int, d: int {:trigger a / d, b / d} 
      :: 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> a / d == b / d
  {
    forall a: int, b: int, d: int | 0 < d && 0 <= a - a % d <= b < a + d - a % d 
      ensures a / d == b / d
    {
      lemmaIndistinguishableQuotients(a, b, d);
    } 
  }

  /* common factors from the dividend and divisor of a modulus operation can be factored out */
  lemma lemmaTruncateMiddle(x: int, b: int, c: int)
    requires 0 <= x
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures (b * x) % (b * c) == b * (x % c)
  {
    lemmaMulStrictlyPositiveAuto();
    lemmaMulNonnegativeAuto();
    calc {
      b * x;
        { lemmaFundamentalDivMod(b * x, b * c); }
      (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c);
        { lemmaDivDenominator(b * x, b, c); }
      (b * c) * (((b * x) / b) / c) + (b * x) % (b * c);
        { lemmaMulIsCommutativeAuto(); lemmaDivByMultiple(x, b); }
      (b * c) * (x / c) + (b * x) % (b * c);
    }
    calc ==> {
      true;
        { lemmaFundamentalDivMod(x, c); }
      x == c * (x / c) + x % c;
      b * x == b * (c * (x / c) + x % c);
        { lemmaMulIsDistributiveAuto(); }
      b * x == b * (c * (x / c)) + b * (x % c);
        { lemmaMulIsAssociativeAuto(); }
      b * x == (b * c) * (x / c) + b * (x % c);
    }
  }

  lemma lemmaTruncateMiddleAuto()
    ensures forall x: int, b: int, c: int {:trigger b * (x % c)} 
      :: 0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c)
  {
    forall x: int, b: int, c: int | 0 <= x && 0 < b && 0 < c && 0 < b * c 
      ensures (b * x) % (b * c) == b * (x % c)
    {
      lemmaTruncateMiddle(x, b, c);
    }
  }

  /* multiplying the numerator and denominator by an integer does not change the quotient */
  lemma lemmaDivMultiplesVanishQuotient(x: int, a: int, d: int)
    requires 0 < x
    requires 0 <= a
    requires 0 < d
    ensures 0 < x * d
    ensures a / d == (x * a) / (x * d)
  {
    lemmaMulStrictlyPositive(x,d);
    calc {
      (x * a) / (x * d);
        {
          lemmaMulNonnegative(x, a);
          lemmaDivDenominator(x * a, x, d); }
      ((x * a) / x) / d;
        { lemmaDivMultiplesVanish(a, x); }
      a / d;
    }
  }

  lemma lemmaDivMultiplesVanishQuotientAuto()
    ensures forall x: int, a: int, d: int {:trigger a / d, x * d, x * a} 
      :: 0 < x && 0 <= a && 0 < d ==> 0 < x * d  &&  a / d == (x * a) / (x * d)
  {
    forall x: int, a: int, d: int | 0 < x && 0 <= a && 0 < d
      ensures 0 < x * d  &&  a / d == (x * a) / (x * d)
    {
      lemmaDivMultiplesVanishQuotient(x, a, d);
    }
  }

  /* rounds down when adding an integer r to the dividend a that is smaller than the divisor d, and then
  multiplying by d */
  lemma lemmaRoundDown(a: int, r: int, d: int)
    requires 0 < d
    requires a % d == 0
    requires 0 <= r < d
    ensures a == d * ((a + r) / d)
  {
    lemmaMulAuto();
    lemmaDivInductionAuto(d, a, u => u % d == 0 ==> u == d * ((u + r) / d));
  }

  lemma lemmaRoundDownAuto()
    ensures forall a: int, r: int, d: int {:trigger d * ((a + r) / d)} 
      :: 0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d)
  {
    forall a: int, r: int, d: int | 0 < d && a % d == 0 && 0 <= r < d
      ensures a == d * ((a + r) / d)
    {
      lemmaRoundDown(a, r, d);
    }
  }

  /* this is the same as writing x + (b/d) == x when b is less than d; this is true because (b/d) == 0 */
  lemma lemmaDivMultiplesVanishFancy(x: int, b: int, d: int)
    requires 0 < d
    requires 0 <= b < d
    ensures (d * x + b) / d == x
  {
    lemmaDivAuto(d);
    var f := u => (d * u + b) / d == u;
    lemmaMulInductionAuto(x, f);
    assert f(x);
  }

  lemma lemmaDivMultiplesVanishFancyAuto()
    ensures forall x: int, b: int, d: int {:trigger (d * x + b) / d}
      :: 0 < d && 0 <= b < d ==> (d * x + b) / d == x
  {
    forall x: int, b: int, d: int | 0 < d && 0 <= b < d 
      ensures (d * x + b) / d == x
    {
      lemmaDivMultiplesVanishFancy(x, b, d);
    }
  }

  /* multiplying an integer by a common numerator and denominator results in the original integer */
  lemma lemmaDivMultiplesVanish(x: int, d: int)
    requires 0 < d
    ensures (d * x) / d == x
  {
    lemmaDivMultiplesVanishFancy(x, 0, d);
  }

  lemma lemmaDivMultiplesVanishAuto()
    ensures forall x: int, d: int {:trigger (d * x) / d} :: 0 < d ==> (d * x) / d == x
  {
    forall x: int, d: int | 0 < d 
      ensures (d * x) / d == x
    {
      lemmaDivMultiplesVanish(x, d);
    }
  }

  /* multiplying a whole number by a common numerator and denominator results in the original integer */
  lemma lemmaDivByMultiple(b: int, d: int)
    requires 0 <= b
    requires 0 < d
    ensures  (b * d) / d == b
  {   
    lemmaDivMultiplesVanish(b,d);
  }

  lemma lemmaDivByMultipleAuto()
    ensures forall b: int, d: int {:trigger (b * d) / d} :: 0 <= b && 0 < d ==> (b * d) / d == b
  {
    forall b: int, d: int | 0 <= b && 0 < d
      ensures (b * d) / d == b
    {
      lemmaDivByMultiple(b, d);
    }
  } 

  /* a dividend y that is a positive multiple of the divisor z will always yield a greater quotient 
  than a dividend x that is less than y */
  lemma lemmaDivByMultipleIsStronglyOrdered(x: int, y: int, m: int, z: int)
    requires x < y
    requires y == m * z
    requires 0 < z
    ensures  x / z < y / z
  {
    lemmaModMultiplesBasic(m, z);
    lemmaDivInductionAuto(z, y - x, yx => var u := yx + x; x < u && u % z == 0 ==> x / z < u / z);
  }

  lemma lemmaDivByMultipleIsStronglyOrderedAuto()
    ensures forall x: int, y: int, m: int, z: int {:trigger x / z, m * z, y / z} 
      :: x < y && y == m * z && 0 < z ==> x / z < y / z
  {
    forall x: int, y: int, m: int, z: int | x < y && y == m * z && 0 < z
      ensures x / z < y / z
    {
      lemmaDivByMultipleIsStronglyOrdered(x, y, m, z);
    }
  } 

  /* if an integer a is less than or equal to the product of two other integers b and c, then the 
  quotient of a/b will be less than or equal to c */
  lemma lemmaMultiplyDivideLe(a: int, b: int, c: int)
    requires 0 < b
    requires a <= b * c
    ensures  a / b <= c
  {
    lemmaModMultiplesBasic(c, b);
    lemmaDivInductionAuto(b, b * c - a, i => 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b);
    lemmaDivMultiplesVanish(c, b);
  }

  lemma lemmaMultiplyDivideLeAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b , b * c} :: 0 < b && a <= b * c ==> a / b <= c
  {
    forall a: int, b: int, c: int | 0 < b && a <= b * c
      ensures a / b <= c
    {
      lemmaMultiplyDivideLe(a, b, c);
    }
  }

  /* if an integer a is less than the product of two other integers b and c, then the quotient 
  of a/b will be less than c */
  lemma lemmaMultiplyDivideLt(a: int, b: int, c: int)
    requires 0 < b
    requires a < b * c
    ensures  a / b < c
  {
    lemmaModMultiplesBasic(c, b);
    lemmaDivInductionAuto(b, b * c - a, i => 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b);
    lemmaDivMultiplesVanish(c, b);
  }

  lemma lemmaMultiplyDivideLtAuto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a < b * c ==> a / b < c
  {
    forall a: int, b: int, c: int | 0 < b && a < b * c
      ensures a / b < c
    {
      lemmaMultiplyDivideLt(a, b, c);
    }
  }

  /* expresses the equality of giving fractions common denominators and then adding them together */
  lemma lemmaHoistOverDenominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d + j == (x + j * d) / d
  {
    lemmaDivAuto(d);
    lemmaMulInductionAuto(j, u => x / d  + u == (x + u * d) / d);
  }

  lemma lemmaHoistOverDenominatorAuto()
    ensures forall x: int, j: int, d: nat {:trigger  x / d + j} :: 0 < d ==> x / d + j == (x + j * d) / d
  {
    forall x: int, j: int, d: nat | 0 < d
      ensures x / d + j == (x + j * d) / d
    {
      lemmaHoistOverDenominator(x, j, d);
    }
  }

  lemma lemmaPartBound1(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures (b * (a / b) % (b * c)) <= b * (c - 1)
  {
    lemmaMulStrictlyPositiveAuto();
    calc {
      b * (a / b) % (b * c);
        { lemmaFundamentalDivMod(b * (a / b), b * c); }
      b * (a / b) - (b * c) * ((b * (a / b)) / (b * c));
        { lemmaMulIsAssociativeAuto(); }
      b * (a / b) - b * (c * ((b * (a / b)) / (b * c)));
        { lemmaMulIsDistributiveAuto(); }
      b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }

    calc ==> {
      true;
        { lemmaModPropertiesAuto(); }
      b * (a / b) % (b * c) < b * c;
      b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) < b * c;
        { lemmaMulIsCommutativeAuto(); lemmaMulStrictInequalityConverseAuto(); }
      ((a / b) - (c * ((b * (a / b)) / (b * c)))) < c;
      ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= c - 1;
        { lemmaMulIsCommutativeAuto(); lemmaMulInequalityAuto(); }
      b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= b * (c - 1);
      b * (a / b) % (b * c) <= b * (c - 1);
    }
  }

  lemma lemmaPartBound1Auto()
    ensures forall a: int, b: int, c: int {:trigger b * (a / b) % (b * c)} 
      :: 0 <= a && 0 < b && 0 < c ==> 0 < b * c && (b * (a / b) % (b * c)) <= b * (c - 1)
  {
    forall a: int, b: int, c: int | 0 <= a && 0 < b && 0 < c
      ensures 0 < b * c && (b * (a / b) % (b * c)) <= b * (c - 1)
    {
      lemmaPartBound1(a, b, c);
    }
  }


/*********************************************************************************************************
* Modulus:
**********************************************************************************************************/
 
  /* the common syntax of the modulus operation results in the same remainder as recursively
  calculating the modulus */
  lemma lemmaModIsModRecursive(x: int, m: int)
    requires m > 0
    ensures modRecursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
    reveal modRecursive();
    if x < 0 { 
      calc { 
        modRecursive(x, m);
        modRecursive(x + m, m);
          { lemmaModIsModRecursive(x + m, m); }
        (x + m) % m;
          { lemmaAddModNoop(x, m, m); } 
        ((x % m) + (m % m)) % m;
          { lemmaModBasicsAuto(); }
        (x % m) % m;
          { lemmaModBasicsAuto(); }
        x % m;
      }
    } else if x < m { 
      lemmaSmallMod(x, m);
    } else {
      calc { 
        modRecursive(x, m);
        modRecursive(x - m, m);
          { lemmaModIsModRecursive(x - m, m); }
        (x - m) % m;
          { lemmaSubModNoop(x, m, m); } 
        ((x % m) - (m % m)) % m;
          { lemmaModBasicsAuto(); }
        (x % m) % m;
          { lemmaModBasicsAuto(); }
        x % m;
      }
    }
  }

  lemma lemmaModIsModRecursiveAuto()
    ensures forall x: int, d: int {:trigger x % d}:: d > 0 ==> modRecursive(x, d) == x % d
  {
    reveal modRecursive();
    forall x: int, d: int | d > 0
      ensures modRecursive(x, d) == x % d
    {
      lemmaModIsModRecursive(x, d);
    }
  }

  /* proves basic properties of the modulus operation: any integer divided by itself does not have a
  remainder; performing (x % m) % m gives the same result as simply perfoming x % m  */
  lemma lemmaModBasicsAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger (x % m) % m} :: m > 0 ==> (x % m) % m == x % m
  {
    forall m: int | m > 0
      ensures m % m == 0
    {
      lemmaModAuto(m);
    }
    forall x: int, m: int | m > 0
      ensures (x % m) % m == x % m
    {
      lemmaModAuto(m);
    }
  }

  /* describes the properties of the modulus operation including those described in lemmaModBasicsAuto. 
  This lemma also states that the remainder of any division will be less than the divisor's value  */
  lemma lemmaModPropertiesAuto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger (x % m) % m} :: m > 0 ==> (x % m) % m == x % m
    ensures forall x: int, m: int {:trigger x % m} :: m > 0 ==> 0 <= x % m < m
  {
    lemmaModBasicsAuto();

    forall x: int, m: int | m > 0
      ensures m > 0 ==> 0 <= x % m < m
    {
      lemmaModAuto(m);
    }
  }

  /* the remainder of a natural number x divided by a natural number d will be less
  than or equal to x */
  lemma lemmaModDecreases(x: nat, d: nat)
    requires 0 < d
    ensures x % d <= x
  {
    lemmaModAuto(d);
  }

  lemma lemmaModDecreasesAuto()
    ensures forall x: nat, d: nat {:trigger x % d} :: 0 < d ==> x % d <= x
  {
    forall x: nat, d: nat | 0 < d 
      ensures 0 < d ==> x % d <= x
    {
      lemmaModDecreases(x, d);
    }
  }
  
  /* a dividend that is any multiple of the divisor will result in a remainder of 0 */
  lemma lemmaModMultiplesBasic(x: int, m: int)
    requires m > 0
    ensures (x * m) % m == 0
  {
    lemmaModAuto(m);
    lemmaMulInductionAuto(x, u => (u * m) % m == 0);
  }

  lemma lemmaModMultiplesBasicAuto()
    ensures forall x: int, m: int {:trigger (x * m) % m} :: m > 0 ==> (x * m) % m == 0
  {
    forall x: int, m: int | m > 0
      ensures (x * m) % m == 0
    {
      lemmaModMultiplesBasic(x, m);
    }
  }

  /* the remainder of adding the divisor m to the dividend b will be the same
  as simply performing b % m */
  lemma lemmaModAddMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
  {
    lemmaModAuto(m);
  }

  lemma lemmaModAddMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m 
      ensures (m + b) % m == b % m
    {
      lemmaModAddMultiplesVanish(b, m);
    }
  }

  /* the remainder of subtracting the divisor m from the dividend b will be the same
  as simply performing b % m */
  lemma lemmaModSubMultiplesVanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
  {
    lemmaModAuto(m);
  }

  lemma lemmaModSubMultiplesVanishAuto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (-m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m 
      ensures (-m + b) % m == b % m
    {
      lemmaModSubMultiplesVanish(b, m);
    }
  }

  /* the remainder of adding any multiple of the divisor m to the dividend b will be the same
  as simply performing b % m */ 
  lemma lemmaModMultiplesVanish(a: int, b: int, m: int)
    decreases if a > 0 then a else -a
    requires 0 < m
    ensures (m * a + b) % m == b % m
  {
    lemmaModAuto(m);
    lemmaMulInductionAuto(a, u => (m * u + b) % m == b % m);
  }

  lemma lemmaModMultiplesVanishAuto()
    ensures forall a: int, b: int, m: int {:trigger (m * a + b) % m} :: 0 < m ==> (m * a + b) % m == b % m
  {
    forall a: int, b: int, m: int | 0 < m
      ensures (m * a + b) % m == b % m
    {
      lemmaModMultiplesVanish(a, b, m);
    }
  }

  /* true if x%n and y%n are equal */
  predicate isModEquivalent(x: int, y: int, m: int)
    requires m > 0
  {
    (x - y) % m == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
  }
  
  /* proves modulus equivalence in two forms */
  lemma lemmaModEquivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
  {
    lemmaModAuto(m);
  }

  lemma lemmaModEquivalenceAuto()
    ensures forall x: int, y: int, m: int {:trigger  x % m , y % m} 
      :: 0 < m && x % m == y % m <==> 0 < m && (x - y) % m == 0
  {
    forall x: int, y: int, m: int | 0 < m 
      ensures x % m == y % m <==> 0 < m && (x - y) % m == 0
    {
      lemmaModEquivalence(x, y, m);
    }
  }

  /* proves equivalent forms of modulus subtraction */
  lemma lemmaModSubtraction(x: nat, s: nat, d: nat)
    requires 0 < d
    requires 0 <= s <= x % d
    ensures x % d - s % d == (x - s) % d
  {
    lemmaModAuto(d);
  }

  lemma lemmaModSubtractionAuto()
    ensures forall x: nat, s: nat, d: nat {:trigger (x - s) % d}
      :: 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d
  {
    forall x: nat, s: nat, d: nat | 0 < d && 0 <= s <= x % d
      ensures x % d - s % d == (x - s) % d
    {
      lemmaModSubtraction(x, s, d);
    }
  }
  
  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma lemmaAddModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) + (y % m)) % m == (x + y) % m
  {
    lemmaModAuto(m);
  }

  lemma lemmaAddModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m}
      :: 0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m
  {
    forall x: int, y: int, m: int | 0 < m 
      ensures ((x % m) + (y % m)) % m == (x + y) % m
    {
      lemmaAddModNoop(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma lemmaAddModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + (y % m)) % m == (x + y) % m
  {
    lemmaModAuto(m);
  }

  lemma lemmaAddModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m}
      :: 0 < m ==> (x + (y % m)) % m == (x + y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x + (y % m)) % m == (x + y) % m
    {
      lemmaAddModNoopRight(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma lemmaSubModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) - (y % m)) % m == (x - y) % m
  {
    lemmaModAuto(m);
  }

  lemma lemmaSubModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} 
      :: 0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures ((x % m) - (y % m)) % m == (x - y) % m
    {
      lemmaSubModNoop(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma lemmaSubModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - (y % m)) % m == (x - y) % m
  {
    lemmaModAuto(m);
  }

  lemma lemmaSubModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} 
      :: 0 < m ==> (x - (y % m)) % m == (x - y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x - (y % m)) % m == (x - y) % m
    {
      lemmaSubModNoopRight(x, y, m);
    }
  }

  /* proves equivalent forms of modulus addition */
  lemma lemmaModAdds(a: int, b: int, d: int)
    requires 0 < d
    ensures a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)
    ensures (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
  {
    lemmaMulAuto();
    lemmaDivAuto(d);
  }

  lemma lemmaModAddsAuto()
    ensures forall a: int, b: int, d: int {:trigger (a + b) % d} 
      :: 0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d) 
      && (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
  {
    forall a: int, b: int, d: int | 0 < d
      ensures a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d) 
      && (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
    {
      lemmaModAdds(a, b, d);
    }
  }

  lemma {:timeLimitMultiplier 2} lemmaModNegNeg(x: int, d: int)
    requires 0 < d
    ensures x % d == (x * (1 - d)) % d
  {
    forall ensures (x - x * d) % d == x % d
    {
      lemmaModAuto(d);
      var f := i => (x - i * d) % d == x % d;
      assert  mulAuto() ==> && f(0)
                            && (forall i {:trigger isLe(0, i)} :: isLe(0, i) && f(i) ==> f(i + 1))
                            && (forall i {:trigger isLe(i, 0)} :: isLe(i, 0) && f(i) ==> f(i - 1));
      lemmaMulInductionAuto(x, f);
    }
    lemmaMulAuto();
  }
  
  /* proves the validity of the quotient and remainder */
  lemma {:timeLimitMultiplier 5} lemmaFundamentalDivModConverse(x: int, d: int, q: int, r: int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x / d 
    ensures r == x % d
  {
    lemmaDivAuto(d);
    lemmaMulInductionAuto(q, u => u == (u * d + r) / d);
    lemmaMulInductionAuto(q, u => r == (u * d + r) % d);
  }

  lemma {:timeLimitMultiplier 5} lemmaFundamentalDivModConverseAuto()
    ensures forall x: int, d: int, q: int, r: int {:trigger q * d + r, x % d}
      :: d != 0 && 0 <= r < d && x == q * d + r ==> q == x / d && r == x % d
  {
    forall x: int, d: int, q: int, r: int | d != 0 && 0 <= r < d && x == q * d + r
      ensures q == x / d && r == x % d
    {
      lemmaFundamentalDivModConverse(x, d, q, r);
    }
  }


  /* the remainder of any natural number x divided by a positive integer m is always less than m */
  lemma lemmaModPosBound(x: int, m: int)
    decreases x
    requires 0 <= x
    requires 0 < m
    ensures  0 <= x % m < m
  {
    lemmaModAuto(m);
  }

  lemma lemmaModPosBoundAuto()
    ensures forall x: int, m: int {:trigger x % m} :: 0 <= x && 0 < m ==> 0 <= x % m < m
  {
    forall x: int, m: int | 0 <= x && 0 < m 
      ensures 0 <= x % m < m
    {
      lemmaModPosBound(x, m);
    }
  }
  
  lemma lemmaMulModNoopLeft(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * y % m == x * y % m
  {
    lemmaModAuto(m);
    lemmaMulInductionAuto(y, u => (x % m) * u % m == x * u % m);
  }

  lemma lemmaMulModNoopLeftAuto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> (x % m) * y % m == x * y % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m) * y % m == x * y % m
    {
      lemmaMulModNoopLeft(x, y, m);
    }
  }
  
  lemma lemmaMulModNoopRight(x: int, y: int, m: int)
    requires 0 < m
    ensures x * (y % m) % m == (x * y) % m
  {
    lemmaModAuto(m);
    lemmaMulInductionAuto(x, u => u * (y % m) % m == (u * y) % m);
  }

  lemma lemmaMulModNoopRightAuto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m} 
      :: 0 < m ==> x * (y % m) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m 
      ensures x * (y % m) % m == (x * y) % m
    {
      lemmaMulModNoopRight(x, y, m);
    }
  }
  
  /* combines previous no-op mod lemmas into a general, overarching lemma */
  lemma lemmaMulModNoopGeneral(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) * y      ) % m == (x * y) % m
    ensures ( x      * (y % m)) % m == (x * y) % m
    ensures ((x % m) * (y % m)) % m == (x * y) % m
  {
    lemmaModPropertiesAuto();
    lemmaMulModNoopLeft(x, y, m);
    lemmaMulModNoopRight(x, y, m);
    lemmaMulModNoopRight(x % m, y, m);
  }

  lemma lemmaMulModNoopGeneralAuto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m}
      :: 0 < m ==> ((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures ((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == (x * y) % m
    {
      lemmaMulModNoopGeneral(x, y, m);
    }
  }
  
  lemma lemmaMulModNoop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * (y % m) % m == (x * y) % m
  {
    lemmaMulModNoopGeneral(x, y, m);
  }

  lemma lemmaMulModNoopAuto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m} 
      :: 0 < m ==> (x % m) * (y % m) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m) * (y % m) % m == (x * y) % m
    {
      lemmaMulModNoop(x, y, m);
    }
  }

  /* the remainder can increase with a larger divisor */
  lemma lemmaModOrdering(x: int, k: int, d: int)
    requires 1 < d
    requires 0 < k
    ensures 0 < d * k
    ensures x % d <= x % (d * k)
  {
    lemmaMulStrictlyIncreases(d,k);
    calc {
      x % d + d * (x / d);
        { lemmaFundamentalDivMod(x, d); }
      x;
        { lemmaFundamentalDivMod(x, d * k); }
      x % (d * k) + (d * k) * (x / (d * k));
        { lemmaMulIsAssociativeAuto(); }
      x % (d * k) + d * (k * (x / (d * k)));
    }
    calc {
      x % d;
        { lemmaModPropertiesAuto(); }
      (x % d) % d;
        { lemmaModMultiplesVanish(x / d  - k * (x / (d * k)), x % d, d); }
      (x % d + d * (x / d  - k * (x / (d * k)))) % d;
        { lemmaMulIsDistributiveSubAuto(); }
      (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d;
      (x % (d * k)) % d;
        <= { lemmaModPropertiesAuto();
            lemmaModDecreases(x % (d * k), d); }
      x % (d * k);
    }
  }

  lemma lemmaModOrderingAuto()
    ensures forall x: int, k: int, d: int {:trigger x % (d * k)}  
      :: 1 < d && 0 < k ==> 0 < d * k && x % d <= x % (d * k)
  {
    forall x: int, k: int, d: int | 1 < d && 0 < k
      ensures d * k > 0 && x % d <= x % (d * k)
    {
      lemmaModOrdering(x, k, d);
    }
  }
  
  lemma lemmaModMod(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    ensures 0 < a * b
    ensures (x % (a * b)) % a == x % a
  {
    lemmaMulStrictlyPositiveAuto();
    calc {
      x;
        { lemmaFundamentalDivMod(x, a * b); }
      (a * b) * (x / (a * b)) + x % (a * b);
        { lemmaMulIsAssociativeAuto(); }
      a * (b * (x / (a * b))) + x % (a * b);
        { lemmaFundamentalDivMod(x % (a * b), a); }
      a * (b * (x / (a * b))) + a * (x % (a * b) / a) + (x % (a * b)) % a;
        { lemmaMulIsDistributiveAuto(); }
      a * (b * (x / (a * b)) + x % (a * b) / a) + (x % (a * b)) % a;
    }
    lemmaModPropertiesAuto();
    lemmaMulIsCommutativeAuto();
    lemmaFundamentalDivModConverse(x, a, b * (x / (a * b)) + x % (a * b) / a, (x % (a * b)) % a);
  }

  lemma lemmaModModAuto()
    ensures forall x: int, a: int, b: int {:trigger a * b, x % a} 
      :: 0 < a && 0 < b ==> 0 < a * b && (x % (a * b)) % a == x % a
  {
    forall x: int, a: int, b: int | 0 < a && 0 < b  
      ensures 0 < a * b && (x % (a * b)) % a == x % a
    {
      lemmaModMod(x, a, b);
    }
  }

  lemma lemmaPartBound2(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures (x % y) % (y * z) < y
  {
    lemmaMulStrictlyPositiveAuto();
    lemmaModPropertiesAuto();
    assert x % y < y;
    lemmaMulIncreasesAuto();
    lemmaMulIsCommutativeAuto();
    assert y <= y * z;
    assert 0 <= x % y < y * z;
    lemmaModPropertiesAuto();
    lemmaSmallMod(x % y, y * z);
    assert (x % y) % (y * z) == x % y;
  }

  lemma lemmaPartBound2Auto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % y}
      :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && (x % y) % (y * z) < y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z
      ensures y * z > 0 && (x % y) % (y * z) < y
    {
      lemmaPartBound2(x, y, z);
    }
  }

  /* ensures the validity of an expanded form of the modulus operation,
   as expressed in the pre and post conditions */
  lemma lemmaModBreakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % (y * z) == y * ((x / y) % z) + x % y
  {
    lemmaMulStrictlyPositiveAuto();
    lemmaDivPosIsPos(x, y);
    assert 0 <= x / y;

    calc {
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
        <=    { lemmaPartBound1(x, y, z); }
      y * (z - 1) + (x % y) % (y * z);
        <    { lemmaPartBound2(x, y, z); }
      y * (z - 1) + y;
            { lemmaMulBasicsAuto(); }
      y * (z - 1) + y * 1;
            { lemmaMulIsDistributiveAuto(); }
      y * (z - 1 + 1);
      y * z;
    }

    calc {
      x % (y * z);
            { lemmaFundamentalDivMod(x, y); }
    (y * (x / y) + x%  y) % (y * z);
            {
              lemmaModPropertiesAuto();
              assert 0 <= x % y;
              lemmaMulNonnegative(y, x / y);
              assert (y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z;
              lemmaModAdds(y * (x / y), x % y, y * z);
            }
    (y * (x / y)) % (y * z) + (x % y) % (y * z);
            {
              lemmaModPropertiesAuto();
              lemmaMulIncreases(z, y);
              lemmaMulIsCommutativeAuto();
              assert x % y < y <= y * z;
              lemmaSmallMod(x % y, y * z);
              assert (x % y) % (y * z) == x % y;
            }
    (y * (x / y)) % (y * z) + x % y;
            { lemmaTruncateMiddle(x / y, y, z); }
    y * ((x / y) % z) + x % y;
    }
  }

  lemma lemmaModBreakdownAuto()
    ensures forall x: int, y: int, z: int {:trigger x % (y * z)}
      :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && x % (y * z) == y * ((x / y) % z) + x % y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z 
      ensures y * z > 0 && x % (y * z) == y * ((x / y) % z) + x % y
    {
      lemmaModBreakdown(x, y, z);
    }
  }

}