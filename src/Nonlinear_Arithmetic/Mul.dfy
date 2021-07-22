// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* Every lemma comes in 2 forms: 'lemma_property' and 'lemma_property_auto'. The former takes arguments and may 
be more stable and less reliant on Z3 heuristics. The latter includes automation and its use requires less effort */

include "Internals/MulInternalsNonlinear.dfy"
include "Internals/MulInternals.dfy"

module Mul {

  import MulINL = MulInternalsNonlinear
  import opened MulInternals

  /* the common syntax of multiplication results in the same product as multiplication 
  through recursive addition */
  lemma lemma_mul_is_mul_recursive(x: int, y: int)
    ensures x * y == mul_recursive(x, y)
  {
    if (x >= 0) { lemma_mul_is_mul_pos(x, y); }
    if (x <= 0) { lemma_mul_is_mul_pos(-x, y); }
    lemma_mul_auto();
  }

  lemma lemma_mul_is_mul_recursive_auto()
    ensures forall x: int, y: int :: x * y == mul_recursive(x, y)
  {
    forall x: int, y: int
      ensures x * y == mul_recursive(x, y)
    {
      lemma_mul_is_mul_recursive(x, y);
    }
  }

  /* the common syntax of multiplying two positive integers results in the same product as 
  mul_pos, which is achieved by recursive addition */ 
  lemma lemma_mul_is_mul_pos(x: int, y: int)
    requires x >= 0
    ensures x * y == mul_pos(x, y)
  {
    reveal_mul_pos();
    lemma_mul_induction_auto(x, u => u >= 0 ==> u * y == mul_pos(u, y));
  }

  /* ensures that the basic properties of multiplication, including the identity and zero properties */
  lemma lemma_mul_basics(x: int)
    ensures 0 * x == 0
    ensures x * 0 == 0
    ensures 1 * x == x
    ensures x * 1 == x
  {
  }

  lemma lemma_mul_basics_auto()
    ensures forall x: int {:trigger 0 * x} :: 0 * x == 0
    ensures forall x: int {:trigger x * 0} :: x * 0 == 0
    ensures forall x: int {:trigger 1 * x} :: 1 * x == x
    ensures forall x: int {:trigger x * 1} :: x * 1 == x
  {
  }

 /* multiplying two nonzero integers will never result in 0 as the poduct */
  lemma lemma_mul_nonzero(x: int, y: int)
    ensures x * y != 0 <==> x != 0 && y != 0
  {
    MulINL.lemma_mul_nonzero(x, y);
  }

  /* multiplying any two nonzero integers will never result in 0 as the poduct */
  lemma lemma_mul_nonzero_auto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y != 0 <==> x != 0 && y != 0
  {
    forall (x: int, y: int)
      ensures x * y != 0 <==> x != 0 && y != 0;
    {
      lemma_mul_nonzero(x, y);
    }
  }
  
  /* any integer multiplied by 0 results in a product of 0 */
  lemma lemma_mul_by_zero_is_zero_auto()
    ensures forall x: int {:trigger 0 * x} {:trigger x * 0} :: x * 0 == 0 * x == 0
  {
    forall x: int {:trigger 0 * x} {:trigger x * 0}
      ensures x * 0 == 0 * x == 0
    {
      lemma_mul_basics(x);
    }
  }

  /* multiplication is associative */
  lemma lemma_mul_is_associative(x: int, y: int, z: int)
    ensures x * (y * z) == (x * y) * z
  {
    MulINL.lemma_mul_is_associative(x, y, z);
  }

  /* multiplication is always associative for all integers*/
  lemma lemma_mul_is_associative_auto()
    ensures forall x: int, y: int, z: int {:trigger x * (y * z)} {:trigger (x * y) * z} 
        :: x * (y * z) == (x * y) * z
  {
    forall (x: int, y: int, z: int)
      ensures x * (y * z) == (x * y) * z
    {
      lemma_mul_is_associative(x, y, z);
    }
  }

  /* multiplcation is commutative */
  lemma lemma_mul_is_commutative(x: int, y: int)
    ensures x * y == y * x
  {
  }

  /* multiplication is always commutative for all integers */
  lemma lemma_mul_is_commutative_auto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == y * x
  {
  }

  /* the product of two integers is greater than the value of each individual integer */ 
  lemma lemma_mul_ordering(x: int, y: int)
    requires x != 0
    requires y != 0
    requires 0 <= x * y
    ensures x * y >= x && x * y >= y
  {
    MulINL.lemma_mul_ordering(x, y);
  }

  /* the product of two positive integers is always greater than the individual value of either 
  multiplied integer */
  lemma lemma_mul_ordering_auto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 != x && 0 != y && x * y >= 0) ==> x * y >= x && x * y >= y
  {
    forall x: int, y: int | 0 != x && 0 != y && x * y >= 0
        ensures x * y >= x && x * y >= y
    {
      lemma_mul_ordering(x, y);
    }
  }

  lemma lemma_mul_equality(x: int, y: int, z: int)
    requires x == y
    ensures x * z == y * z
  {}

  lemma lemma_mul_equality_auto()
    ensures forall x: int, y: int, z: int {:trigger x * z, y * z } :: x == y ==> x * z == y * z
  {
    forall (x: int, y: int, z: int | x == y) 
      ensures x * z == y * z
    {
      lemma_mul_equality(x, y, z);
    }
  }

  /* two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemma_mul_inequality(x: int, y: int, z: int)
    requires x <= y
    requires z >= 0
    ensures  x * z <= y * z
  {
    lemma_mul_induction_auto(z, u => u >= 0 ==> x * u <= y * u);
  }

  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemma_mul_inequality_auto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x <= y && z >= 0 ==> x * z <= y * z
  {
    forall (x: int, y: int, z: int | x <= y && z >= 0)
      ensures x * z <= y * z
    {
      lemma_mul_inequality(x, y, z);
    }
  }

  /* multiplying by a positive integer preserves inequality */
  lemma lemma_mul_strict_inequality(x: int, y: int, z: int)
    requires x < y
    requires z > 0
    ensures  x * z < y * z
  {
    MulINL.lemma_mul_strict_inequality(x, y, z);
  }

  /* multiplying by a positive integer preserves inequality for all integers*/
  lemma lemma_mul_strict_inequality_auto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x < y && z > 0 ==> x * z < y * z
  {
    forall (x: int, y: int, z: int | x < y && z > 0)
      ensures x * z < y * z
    {
      lemma_mul_strict_inequality(x, y, z);
    }
  }

  /* the product of two bounded integers is less than or equal to the product of their upper bounds */
  lemma lemma_mul_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
    requires x <= x_bound
    requires y <= y_bound
    requires 0 <= x
    requires 0 <= y
    ensures x * y <= x_bound * y_bound
  {
    lemma_mul_inequality(x, x_bound, y);
    lemma_mul_inequality(y, y_bound, x_bound);
  }

  lemma lemma_mul_upper_bound_auto()
    ensures forall x: int, x_bound: int, y: int, y_bound: int {:trigger x * y, x_bound * y_bound}
        :: x <= x_bound && y <= y_bound && 0 <= x && 0 <= y ==> x * y <= x_bound * y_bound
  {
    forall (x: int, x_bound: int, y: int, y_bound: int | x <= x_bound && y <= y_bound && 0 <= x && 0 <= y)
      ensures x * y <= x_bound * y_bound
    {
      lemma_mul_upper_bound(x, x_bound, y, y_bound);
    }
  }

  /* the product of two strictly upper bounded integers is less than the product of their upper bounds */
  lemma lemma_mul_strict_upper_bound(x: int, x_bound: int, y: int, y_bound: int)
    requires x < x_bound 
    requires y < y_bound 
    requires 0 < x
    requires 0 < y
    ensures x * y <= (x_bound - 1) * (y_bound - 1)
  {
    lemma_mul_inequality(x, x_bound - 1, y);
    lemma_mul_inequality(y, y_bound - 1, x_bound - 1);
  }

  lemma lemma_mul_strict_upper_bound_auto()
    ensures forall x: int, x_bound: int, y: int, y_bound: int {:trigger x * y, (x_bound - 1) * (y_bound - 1)} 
        :: x < x_bound && y < y_bound && 0 < x && 0 < y ==> x * y <= (x_bound - 1) * (y_bound - 1)
  {
    forall (x: int, x_bound: int, y: int, y_bound: int | x < x_bound && y < y_bound && 0 < x && 0 < y)
      ensures x * y <= (x_bound - 1) * (y_bound - 1)
    {
      lemma_mul_strict_upper_bound(x, x_bound, y, y_bound);
    }
  }

  /* any two integers that are multiplied by a positive number will maintain their numerical order */
  lemma lemma_mul_left_inequality(x: int, y: int, z: int)
    requires 0 < x
    ensures y <= z ==> x * y <= x * z
    ensures y < z ==> x * y < x * z
  {
    lemma_mul_induction_auto(x, u => u > 0 ==> y <= z ==> u * y <= u * z);
    lemma_mul_induction_auto(x, u => u > 0 ==> y < z ==> u * y < u * z);
  }

  lemma lemma_mul_left_inequality_auto()
    ensures forall x: int, y: int, z: int {:trigger x * y, x * z}
        :: x > 0 ==> (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
  {
    forall (x: int, y: int, z: int | (y <= z || y < z) && 0 < x)
      ensures (y <= z ==> x * y <= x * z) && (y < z ==> x * y < x * z)
    {
      lemma_mul_left_inequality(x, y, z);
    }
  }

/* if two seperate integers are each multiplied by a common integer and the products are equal, the 
  two original integers are equal */
  lemma lemma_mul_equality_converse(m: int, x: int, y: int)
    requires m != 0
    requires m * x == m * y
    ensures x == y
  {
    lemma_mul_induction_auto(m, u => x > y && 0 < u ==> x * u > y * u);
    lemma_mul_induction_auto(m, u => x > y && 0 > u ==> x * u < y * u);
    lemma_mul_induction_auto(m, u => x < y && 0 < u ==> x * u < y * u);
    lemma_mul_induction_auto(m, u => x < y && 0 > u ==> x * u > y * u);
  }
  
  /* if any two seperate integers are each multiplied by a common integer and the products are equal, the 
  two original integers are equal */
  lemma lemma_mul_equality_converse_auto()
    ensures forall m: int, x: int, y: int {:trigger m * x, m * y} :: (m != 0 && m * x == m * y) ==> x == y
  {
    forall (m: int, x: int, y: int | m != 0 && m * x == m * y)
      ensures x == y
    {
      lemma_mul_equality_converse(m, x, y);
    }
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z */
  lemma lemma_mul_inequality_converse(x: int, y: int, z: int)
    requires x * z <= y * z
    requires z > 0
    ensures  x <= y
  {
    lemma_mul_induction_auto(z, u => x * u <= y * u && u > 0 ==> x <= y);
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x <= z then the x*z <= y*z 
  for all valid values of x, y, and z*/
  lemma lemma_mul_inequality_converse_auto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z <= y * z && z > 0 ==> x <= y
  {
    forall (x: int, y: int, z: int | x * z <= y * z && z > 0)
      ensures x <= y
    {
      lemma_mul_inequality_converse(x, y, z);
    }
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z */
  lemma lemma_mul_strict_inequality_converse(x: int, y: int, z: int)
    requires x * z < y * z
    requires z >= 0
    ensures  x < y
  {
    lemma_mul_induction_auto(z, u => x * u < y * u && u >= 0 ==> x < y);
  }

  /* when two integers, x and y, are each multiplied by a positive integer, z, if x < z then the x*z < y*z 
  for all valid values of x, y, and z*/
  lemma lemma_mul_strict_inequality_converse_auto()
    ensures  forall x: int, y: int, z: int {:trigger x * z, y * z} :: x * z < y * z && z >= 0 ==> x < y
  {
      forall (x: int, y: int, z: int | x * z < y * z && z >= 0)
          ensures x < y;
      {
          lemma_mul_strict_inequality_converse(x, y, z);
      }
  }

  /* multiplication is distributive */
  lemma lemma_mul_is_distributive_add(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
  {
    MulINL.lemma_mul_is_distributive_add(x, y, z);
  }

  /* for all integers, multiplication is distributive with addition in the form x * (y + z) */
  lemma lemma_mul_is_distributive_add_auto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
  {
    forall (x: int, y: int, z: int)
      ensures x * (y + z) == x * y + x * z
    {
      lemma_mul_is_distributive_add(x, y, z);
    }
  }

  /* for all integers, multiplication is distributive with addition in the form (y + z) * x */
  lemma lemma_mul_is_distributive_add_other_way(x: int, y: int, z: int)
    ensures (y + z) * x == y * x + z * x
  {
    lemma_mul_auto();
  }

  lemma lemma_mul_is_distributive_add_other_way_auto()
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
  {
    forall (x: int, y: int, z: int)
      ensures (y+z) * x == y * x + z * x
    {
      lemma_mul_is_distributive_add_other_way(x, y, z);
    }
  }

  /* multiplication is distributive with subtraction */
  lemma lemma_mul_is_distributive_sub(x: int, y: int, z: int)
    ensures x * (y - z) == x * y - x * z
  {
    lemma_mul_auto();
  }

  /* for all integers, multiplication is distributive with subtraction */
  lemma lemma_mul_is_distributive_sub_auto()
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
  {
    forall (x: int, y: int, z: int)
      ensures x * (y - z) == x * y - x * z;
    {
      lemma_mul_is_distributive_sub(x, y, z);
    }
  }

  /* proves the overall distributive nature of multiplication*/
  lemma lemma_mul_is_distributive(x: int, y: int, z: int)
    ensures x * (y + z) == x * y + x * z
    ensures x * (y - z) == x * y - x * z
    ensures (y + z) * x == y * x + z * x
    ensures (y - z) * x == y * x - z * x
    ensures x * (y + z) == (y + z) * x
    ensures x * (y - z) == (y - z) * x
    ensures x * y == y * x
    ensures x * z == z * x
  {
    lemma_mul_auto();
  }

  /* for all integers, multiplication is distributive */
  lemma lemma_mul_is_distributive_auto()
    ensures forall x: int, y: int, z: int {:trigger x * (y + z)} :: x * (y + z) == x * y + x * z
    ensures forall x: int, y: int, z: int {:trigger x * (y - z)} :: x * (y - z) == x * y - x * z
    ensures forall x: int, y: int, z: int {:trigger (y + z) * x} :: (y + z) * x == y * x + z * x
    ensures forall x: int, y: int, z: int {:trigger (y - z) * x} :: (y - z) * x == y * x - z * x
  {
    lemma_mul_is_distributive_add_auto();
    lemma_mul_is_distributive_sub_auto();
    lemma_mul_is_commutative_auto();
  }

  /* multiplying two positive integers will result in a positive integer */
  lemma lemma_mul_strictly_positive(x: int, y: int)
    ensures (0 < x && 0 < y) ==> (0 < x * y)
  {
    MulINL.lemma_mul_strictly_positive(x, y);
  }

  /* multiplying any two positive integers will result in a positive integer */
  lemma lemma_mul_strictly_positive_auto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (0 < x * y)
  {
    forall (x: int, y: int | 0 < x && 0 < y)
      ensures 0 < x * y
    {
      lemma_mul_strictly_positive(x,y);
    }
  }

  /* multiplying a positive integer by an integer greater than 1 will result in a product that 
  is greater than the original integer */
  lemma lemma_mul_strictly_increases(x: int, y: int)
    requires 1 < x
    requires 0 < y
    ensures y < x * y
  {
    lemma_mul_induction_auto(x, u => 1 < u ==> y < u * y);
  }

  /* multiplying any positive integer by any integer greater than 1 will result in a product that 
  is greater than the original integer */
  lemma lemma_mul_strictly_increases_auto()
    ensures forall x: int, y: int {:trigger x * y} :: 1 < x && 0 < y  ==> y < x * y
  {
    forall (x: int, y: int | 1 < x && 0 < y)
      ensures y < x * y
    {
      lemma_mul_strictly_increases(x, y);
    }
  }

  /* multiplying an integer by a positive integer will result in a product that is greater than or
  equal to the original integer */
  lemma lemma_mul_increases(x: int, y: int)
    requires 0 < x
    requires 0 < y
    ensures y <= x * y
  {
    lemma_mul_induction_auto(x, u => 0 < u ==> y <= u * y);
  }

  /* multiplying any integer by any positive integer will result in a product that is greater than or
  equal to the original integer */
  lemma lemma_mul_increases_auto()
    ensures forall x: int, y: int {:trigger x * y} :: (0 < x && 0 < y) ==> (y <= x * y)
  {
    forall (x: int, y: int | 0 < x && 0 < y)
      ensures y <= x * y
    {
      lemma_mul_increases(x, y);
    }
  }

  /* multiplying two positive numbers will result in a positive product */
  lemma lemma_mul_nonnegative(x: int, y: int)
    requires 0 <= x
    requires 0 <= y
    ensures  0 <= x * y
  {
    lemma_mul_induction_auto(x, u => 0 <= u ==> 0 <= u * y);
  }
  
  /* multiplying any two positive numbers will result in a positive product */
  lemma lemma_mul_nonnegative_auto()
    ensures forall x: int, y: int {:trigger x * y} :: 0 <= x && 0 <= y ==> 0 <= x * y
  {
    forall (x: int, y: int | 0 <= x && 0 <= y)
      ensures 0 <= x * y
    {
      lemma_mul_nonnegative(x, y);
    }
  }

  /* shows the equivalent forms of using the unary negation operator */
  lemma lemma_mul_unary_negation(x: int, y: int)
    ensures (-x) * y == -(x * y) == x * (-y)
  {
    lemma_mul_induction_auto(x, u => (-u) * y == -(u * y) == u * (-y));
  }

  /* shows the equivalent forms of using the unary negation operator for any integers*/
  lemma lemma_mul_unary_negation_auto()
    ensures forall x: int, y: int {:trigger (-x) * y} {:trigger x * (-y)} :: (-x) * y == -(x * y) == x * (-y)
  {
    forall (x: int, y: int) 
      ensures (-x) * y == -(x * y) == x * (-y)
    {
      lemma_mul_unary_negation(x, y);
    }
  }

  /* multiplying two negative integers, -x and -y, is equivalent to multiplying x and y */
  lemma lemma_mul_cancels_negatives(x: int, y: int)
    ensures x * y == (-x) * (-y)
  {
    lemma_mul_unary_negation_auto();
  }

  /* multiplying two negative integers, -x and -y, is equivalent to multiplying x and y */
  lemma lemma_mul_cancels_negatives_auto()
    ensures forall x: int, y: int {:trigger x * y} :: x * y == (-x) * (-y)
  {
    forall x: int, y: int 
      ensures x * y == (-x) * (-y)
    {
      lemma_mul_cancels_negatives(x, y);
    }
  }

  /* includes all properties of multiplication */
  lemma lemma_mul_properties()
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
    lemma_mul_strict_inequality_auto();
    lemma_mul_inequality_auto();
    lemma_mul_is_distributive_auto();
    lemma_mul_is_associative_auto();
    lemma_mul_ordering_auto();
    lemma_mul_nonzero_auto();
    lemma_mul_nonnegative_auto();
    lemma_mul_strictly_increases_auto();
    lemma_mul_increases_auto();
  }

} 