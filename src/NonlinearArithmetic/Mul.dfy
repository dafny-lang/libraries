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

include "Internals/MulInternalsNonlinear.dfy"
include "Internals/MulInternals.dfy"

module Mul {

  import MulINL = MulInternalsNonlinear
  import opened MulInternals

  /* the built-in syntax of multiplication results in the same product as multiplication 
  through recursive addition */
  lemma lemmaMulIsMulRecursive(x: int, y: int)
    ensures x * y == mulRecursive(x, y)
  {
    if (x >= 0) { lemmaMulIsMulPos(x, y); }
    if (x <= 0) { lemmaMulIsMulPos(-x, y); }
    lemmaMulAuto();
  }

  lemma lemmaMulIsMulRecursiveAuto()
    ensures forall x: int, y: int :: x * y == mulRecursive(x, y)
  {
    forall x: int, y: int
      ensures x * y == mulRecursive(x, y)
    {
      lemmaMulIsMulRecursive(x, y);
    }
  }

  /* the built-in syntax of multiplying two positive integers results in the same product as 
  mulPos, which is achieved by recursive addition */ 
  lemma lemmaMulIsMulPos(x: int, y: int)
    requires x >= 0
    ensures x * y == mulPos(x, y)
  {
    reveal mulPos();
    lemmaMulInductionAuto(x, u => u >= 0 ==> u * y == mulPos(u, y));
  }

  /* ensures that the basic properties of multiplication, including the identity and zero properties */
  lemma lemmaMulBasics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
  {
  }

  lemma lemmaMulBasicsAuto()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

 /* multiplying two nonzero integers will never result in 0 as the poduct */
  lemma lemmaMulNonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
  {
    MulINL.lemmaMulNonzero(x, y);
  }

  /* multiplying any two nonzero integers will never result in 0 as the poduct */
  lemma lemmaMulNonzeroAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
    forall (x: int, y: int)
      ensures x * y != 0 <==> x != 0 && y != 0;
    {
      lemmaMulNonzero(x, y);
    }
  }
  
  /* any integer multiplied by 0 results in a product of 0 */
  lemma lemmaMulByZeroIsZeroAuto()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x == 0
  {
    forall x: int {:trigger 0 * x} {:trigger x * 0}
      ensures x * 0 == 0 * x == 0
    {
      lemmaMulBasics(x);
    }
  }

  /* multiplication is associative */
  lemma lemmaMulIsAssociative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
  {
    MulINL.lemmaMulIsAssociative(x, y, z);
  }

  /* multiplication is always associative for all integers*/
  lemma lemmaMulIsAssociativeAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y * z)} {:trigger (x * y) * z} 
        :: x * (y * z) == (x * y) * z
  {
    forall (x: int, y: int, z: int)
      ensures x * (y * z) == (x * y) * z
    {
      lemmaMulIsAssociative(x, y, z);
    }
  }

  /* multiplication is commutative */
  lemma lemmaMulIsCommutative(x: int, y: int)
    ensures x * y == y * x
  {
  }

  /* multiplication is always commutative for all integers */
  lemma lemmaMulIsCommutativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  /* the product of two integers is greater than the value of each individual integer */ 
  lemma lemmaMulOrdering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
  {
    MulINL.lemmaMulOrdering(x, y);
  }

  /* the product of two positive integers is always greater than the individual value of either 
  multiplied integer */
  lemma lemmaMulOrderingAuto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 != x && 0 != y && x * y >= 0) ==> x * y >= x && x * y >= y
  {
    forall x: int, y: int | 0 != x && 0 != y && x * y >= 0
        ensures x * y >= x && x * y >= y
    {
      lemmaMulOrdering(x, y);
    }
  }

  lemma lemmaMulEquality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
  {}

  lemma lemmaMulEqualityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z } :: x == y ==> x * z == y * z
  {
    forall (x: int, y: int, z: int | x == y) 
      ensures x * z == y * z
    {
      lemmaMulEquality(x, y, z);
    }
  }

  /* two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemmaMulInequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures  x * z <= y * z
  {
    lemmaMulInductionAuto(z, u => u >= 0 ==> x * u <= y * u);
  }

  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemmaMulInequalityAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
    forall (x: int, y: int, z: int | x <= y && z >= 0)
      ensures x * z <= y * z
    {
      lemmaMulInequality(x, y, z);
    }
  }

  /* multiplying by a positive integer preserves inequality */
  lemma lemmaMulStrictInequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures  x * z < y * z
  {
    MulINL.lemmaMulStrictInequality(x, y, z);
  }

  /* multiplying by a positive integer preserves inequality for all integers*/
  lemma lemmaMulStrictInequalityAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
    forall (x: int, y: int, z: int | x < y && z > 0)
      ensures x * z < y * z
    {
      lemmaMulStrictInequality(x, y, z);
    }
  }

  /* the product of two bounded integers is less than or equal to the product of their upper bounds */
  lemma lemmaMulUpperBound(x: int, xBound: int, y: int, yBound: int)
    requires x <= xBound
    requires y <= yBound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= xBound * yBound
  {
    lemmaMulInequality(x, xBound, y);
    lemmaMulInequality(y, yBound, xBound);
  }

  lemma lemmaMulUpperBoundAuto()
    ensures forall x: int, xBound: int, y: int, yBound: int {:trigger x * y, xBound * yBound}
        :: x <= xBound && y <= yBound && 0 <= x && 0 <= y ==> x * y <= xBound * yBound
  {
    forall (x: int, xBound: int, y: int, yBound: int | x <= xBound && y <= yBound && 0 <= x && 0 <= y)
      ensures x * y <= xBound * yBound
    {
      lemmaMulUpperBound(x, xBound, y, yBound);
    }
  }

  /* the product of two strictly upper bounded integers is less than the product of their upper bounds */
  lemma lemmaMulStrictUpperBound(x: int, xBound: int, y: int, yBound: int)
    requires x < xBound 
    requires y < yBound 
    requires 0 < x
    requires 0 < y
    ensures x * y <= (xBound - 1) * (yBound - 1)
  {
    lemmaMulInequality(x, xBound - 1, y);
    lemmaMulInequality(y, yBound - 1, xBound - 1);
  }

  lemma lemmaMulStrictUpperBoundAuto()
    ensures forall x: int, xBound: int, y: int, yBound: int {:trigger x * y, (xBound - 1) * (yBound - 1)} 
        :: x < xBound && y < yBound && 0 < x && 0 < y ==> x * y <= (xBound - 1) * (yBound - 1)
  {
    forall (x: int, xBound: int, y: int, yBound: int | x < xBound && y < yBound && 0 < x && 0 < y)
      ensures x * y <= (xBound - 1) * (yBound - 1)
    {
      lemmaMulStrictUpperBound(x, xBound, y, yBound);
    }
  }

  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemmaMulLeftInequality(x: int, y: int, z: int)
    requires 0 < x
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
  {
    lemmaMulInductionAuto(x, u => u > 0 ==> y <= z ==> u * y <= u * z);
    lemmaMulInductionAuto(x, u => u > 0 ==> y < z ==> u * y < u * z);
  }

  lemma lemmaMulLeftInequalityAuto()
    ensures forall x: int, y: int, z: int {:trigger x * y, x * z}
        :: x > 0 ==> (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
  {
    forall (x: int, y: int, z: int | (y <= z || y < z) && 0 < x)
      ensures (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
    {
      lemmaMulLeftInequality(x, y, z);
    }
  }

/* if two seperate integers are each multiplied by a common integer and the products are equal, the 
  two original integers are equal */
  lemma lemmaMulEqualityConverse(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
  {
    lemmaMulInductionAuto(m, u => x > y && 0 < u ==> x * u > y * u);
    lemmaMulInductionAuto(m, u => x > y && 0 > u ==> x * u < y * u);
    lemmaMulInductionAuto(m, u => x < y && 0 < u ==> x * u < y * u);
    lemmaMulInductionAuto(m, u => x < y && 0 > u ==> x * u > y * u);
  }
  
  /* if any two seperate integers are each multiplied by a common integer and the products are equal, the 
  two original integers are equal */
  lemma lemmaMulEqualityConverseAuto()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: (m != 0 && m * x == m * y) ==> x == y
  {
    forall (m: int, x: int, y: int | m != 0 && m * x == m * y)
      ensures x == y
    {
      lemmaMulEqualityConverse(m, x, y);
    }
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z */
  lemma lemmaMulInequalityConverse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures  x <= y
  {
    lemmaMulInductionAuto(z, u => x * u <= y * u && u > 0 ==> x <= y);
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z 
  for all valid values of x, y, and z*/
  lemma lemmaMulInequalityConverseAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
    forall (x: int, y: int, z: int | x * z <= y * z && z > 0)
      ensures x <= y
    {
      lemmaMulInequalityConverse(x, y, z);
    }
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z */
  lemma lemmaMulStrictInequalityConverse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures  x < y
  {
    lemmaMulInductionAuto(z, u => x * u < y * u && u >= 0 ==> x < y);
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z 
  for all valid values of x, y, and z*/
  lemma lemmaMulStrictInequalityConverseAuto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
      forall (x: int, y: int, z: int | x * z < y * z && z >= 0)
          ensures x < y;
      {
          lemmaMulStrictInequalityConverse(x, y, z);
      }
  }

  /* multiplication is distributive */
  lemma lemmaMulIsDistributiveAdd(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  {
    MulINL.lemmaMulIsDistributiveAdd(x, y, z);
  }

  /* for all integers, multiplication is distributive with addition in the form x * (y + z) */
  lemma lemmaMulIsDistributiveAddAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
    forall (x: int, y: int, z: int)
      ensures x * (y + z) == x * y + x * z
    {
      lemmaMulIsDistributiveAdd(x, y, z);
    }
  }

  /* for all integers, multiplication is distributive with addition in the form (y + z) * x */
  lemma lemmaMulIsDistributiveAddOtherWay(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
  {
    lemmaMulAuto();
  }

  lemma lemmaMulIsDistributiveAddOtherWayAuto()
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
  {
    forall (x: int, y: int, z: int)
      ensures (y+z) * x == y * x + z * x
    {
      lemmaMulIsDistributiveAddOtherWay(x, y, z);
    }
  }

  /* multiplication is distributive with subtraction */
  lemma lemmaMulIsDistributiveSub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
  {
    lemmaMulAuto();
  }

  /* for all integers, multiplication is distributive with subtraction */
  lemma lemmaMulIsDistributiveSubAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
    forall (x: int, y: int, z: int)
      ensures x * (y - z) == x * y - x * z;
    {
      lemmaMulIsDistributiveSub(x, y, z);
    }
  }

  /* proves the overall distributive nature of multiplication*/
  lemma lemmaMulIsDistributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
  {
    lemmaMulAuto();
  }

  /* for all integers, multiplication is distributive */
  lemma lemmaMulIsDistributiveAuto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
    lemmaMulIsDistributiveAddAuto();
    lemmaMulIsDistributiveSubAuto();
    lemmaMulIsCommutativeAuto();
  }

  /* multiplying two positive integers will result in a positive integer */
  lemma lemmaMulStrictlyPositive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
  {
    MulINL.lemmaMulStrictlyPositive(x, y);
  }

  /* multiplying any two positive integers will result in a positive integer */
  lemma lemmaMulStrictlyPositiveAuto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (0 < x * y)
  {
    forall (x: int, y: int | 0 < x && 0 < y)
      ensures 0 < x * y
    {
      lemmaMulStrictlyPositive(x,y);
    }
  }

  /* multiplying a positive integer by an integer greater than 1 will result in a product that 
  is greater than the original integer */
  lemma lemmaMulStrictlyIncreases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
  {
    lemmaMulInductionAuto(x, u => 1 < u ==> y < u * y);
  }

  /* multiplying any positive integer by any integer greater than 1 will result in a product that 
  is greater than the original integer */
  lemma lemmaMulStrictlyIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y  ==> y < x * y
  {
    forall (x: int, y: int | 1 < x && 0 < y)
      ensures y < x * y
    {
      lemmaMulStrictlyIncreases(x, y);
    }
  }

  /* multiplying an integer by a positive integer will result in a product that is greater than or
  equal to the original integer */
  lemma lemmaMulIncreases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
  {
    lemmaMulInductionAuto(x, u => 0 < u ==> y <= u * y);
  }

  /* multiplying any integer by any positive integer will result in a product that is greater than or
  equal to the original integer */
  lemma lemmaMulIncreasesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (y <= x * y)
  {
    forall (x: int, y: int | 0 < x && 0 < y)
      ensures y <= x * y
    {
      lemmaMulIncreases(x, y);
    }
  }

  /* multiplying two positive numbers will result in a positive product */
  lemma lemmaMulNonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures  0 <= x * y
  {
    lemmaMulInductionAuto(x, u => 0 <= u ==> 0 <= u * y);
  }
  
  /* multiplying any two positive numbers will result in a positive product */
  lemma lemmaMulNonnegativeAuto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
    forall (x: int, y: int | 0 <= x && 0 <= y)
      ensures 0 <= x * y
    {
      lemmaMulNonnegative(x, y);
    }
  }

  /* shows the equivalent forms of using the unary negation operator */
  lemma lemmaMulUnaryNegation(x: int, y: int)
    ensures (-x) * y == -(x * y) == x * (-y)
  {
    lemmaMulInductionAuto(x, u => (-u) * y == -(u * y) == u * (-y));
  }

  /* shows the equivalent forms of using the unary negation operator for any integers*/
  lemma lemmaMulUnaryNegationAuto()
    ensures forall x: int, y: int {:trigger (-x) * y} {:trigger x * (-y)} :: (-x) * y == -(x * y) == x * (-y)
  {
    forall (x: int, y: int) 
      ensures (-x) * y == -(x * y) == x * (-y)
    {
      lemmaMulUnaryNegation(x, y);
    }
  }

  /* multiplying two negative integers, -x and -y, is equivalent to multiplying x and y */
  lemma lemmaMulCancelsNegatives(x: int, y: int)
    ensures x * y == (-x) * (-y)
  {
    lemmaMulUnaryNegationAuto();
  }

  /* multiplying two negative integers, -x and -y, is equivalent to multiplying x and y */
  lemma lemmaMulCancelsNegativesAuto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == (-x) * (-y)
  {
    forall x: int, y: int 
      ensures x * y == (-x) * (-y)
    {
      lemmaMulCancelsNegatives(x, y);
    }
  }

  /* includes all properties of multiplication */
  lemma lemmaMulProperties()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
    ensures forall x: int {:trigger x * 1}{:trigger 1 * x} :: x * 1 == 1 * x == x
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
    ensures forall x: int, y: int, z: int {:trigger x * (y * z)}{:trigger (x * y) * z} :: x * (y * z) == (x * y) * z
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: 0 < x && 0 < y && 0 <= x * y ==> x <= x * y && y <= x * y
    ensures forall x: int, y: int {:trigger x * y} :: (1 < x && 0 < y) ==> (y < x * y)
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (y <= x * y)
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (0 < x * y)
  {
    lemmaMulStrictInequalityAuto();
    lemmaMulInequalityAuto();
    lemmaMulIsDistributiveAuto();
    lemmaMulIsAssociativeAuto();
    lemmaMulOrderingAuto();
    lemmaMulNonzeroAuto();
    lemmaMulNonnegativeAuto();
    lemmaMulStrictlyIncreasesAuto();
    lemmaMulIncreasesAuto();
  }

} 