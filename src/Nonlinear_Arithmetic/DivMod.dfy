// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/* Every lemma comes in 2 forms: 'lemma_property' and 'lemma_property_auto'. The former takes arguments and may 
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
  lemma lemma_div_is_div_recursive(x: int, d: int)
    requires 0 < d
    ensures div_recursive(x, d) == x / d
  {
    reveal_div_recursive();
    lemma_div_induction_auto(d, x, u => div_recursive(u, d) == u / d);
  }

  lemma lemma_div_is_div_recursive_auto()
    ensures forall x: int, d: int {:trigger x / d} :: d > 0 ==> div_recursive(x, d) == x / d
  {
    reveal_div_recursive();
    forall x: int, d: int | d > 0
      ensures div_recursive(x, d) == x / d
    {
      lemma_div_is_div_recursive(x, d);
    }
  }

  /* the quotient of an integer divided by itself is 1 */
  lemma lemma_div_by_self(d: int)
    requires d != 0
    ensures d / d == 1
  { 
    DivINL.lemma_div_by_self(d);
  }

  /* zero divided by an integer besides 0 is 0 */
  lemma {:opaque} lemma_div_of_0(d: int)
    requires d != 0
    ensures 0 / d == 0
  { 
    DivINL.lemma_div_of_0(d);
  }

  /* ensures the basic propoerties of division: 0 divided by any integer is 0; any integer 
  divided by 1 is itself; any integer divided by itself is 1 */
  lemma lemma_div_basics(x: int)
    ensures x != 0 ==> 0 / x == 0
    ensures x / 1 == x
    ensures x != 0 ==> x / x == 1
  {
    if (x != 0) {
      lemma_div_by_self(x);
      lemma_div_of_0(x);
    }
  }
    
  lemma lemma_div_basics_auto()
    ensures forall x {:trigger 0 / x} :: x != 0 ==> 0 / x == 0
    ensures forall x {:trigger x / 1} :: x / 1 == x
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y >= 0
    ensures forall x, y {:trigger x / y} :: x >= 0 && y > 0 ==> x / y <= x
  {
    forall x: int
      ensures x != 0 ==> 0 / x == 0
      ensures x / 1 == x
    {
      lemma_div_basics(x);
    }
    forall x: int, y: int | x >= 0 && y > 0
      ensures x / y >= 0
      ensures x / y <= x
    {
      lemma_div_pos_is_pos(x, y);
      lemma_div_is_ordered_by_denominator(x, 1, y);
    }
  }

  /* if a dividend is a whole number and the divisor is a natural number and their
  quotient is 0, this implies that the dividend is smaller than the divisor */
  lemma lemma_small_div_converse_auto()
    ensures forall x, d {:trigger x / d } :: 0 <= x && 0 < d && x / d == 0 ==> x < d
  {
    forall x, d | 0 <= x && 0 < d && x / d == 0
      ensures x < d
    {
      lemma_div_induction_auto(d, x, u => 0 <= u && 0 < d && u / d == 0 ==> u < d);
    }
  }

  /* given two fractions with the same numerator, the order of numbers is determined by 
  the denominators. However, if the numerator is 0, the fractions are equal regardless of 
  the denominators' values */
  lemma lemma_div_is_ordered_by_denominator(x: int, y: int, z: int)
    requires 0 <= x
    requires 1 <= y <= z
    ensures x / y >= x / z
    decreases x
  {
    reveal_div_recursive();
    lemma_div_is_div_recursive_auto();
    assert forall u: int, d: int {:trigger u / d} {:trigger div_recursive(u, d)} 
      :: d > 0 ==> div_recursive(u, d) == u / d;

    if (x < z)
    {
      lemma_div_is_ordered(0, x, y);
    }
    else
    {
      lemma_div_is_ordered(x - z, x - y, y);
      lemma_div_is_ordered_by_denominator(x - z, y, z);
    }
  }

  lemma lemma_div_is_ordered_by_denominator_auto()
    ensures forall x: int, y: int, z: int {:trigger x / y, x / z} :: 0 <= x && 1 <= y <= z ==> x / y >= x / z
  {
    forall (x: int, y: int, z: int | 0 <= x && 1 <= y <= z)
      ensures x / y >= x / z
    {
      lemma_div_is_ordered_by_denominator(x, y, z);
    }
  }

  /* given two fractions with the same numerator, the order of numbers is strictly determined by 
  the denominators.*/
  lemma lemma_div_is_strictly_ordered_by_denominator(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d  < x
    decreases x
  {
    lemma_div_induction_auto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma lemma_div_is_strictly_ordered_by_denominator_auto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall (x: int, d: int | 0 < x && 1 < d )
      ensures x / d < x
    {
      lemma_div_is_strictly_ordered_by_denominator(x, d);
    }
  }

  /* Rounding is different when multiplying the sum of two integers by a fraction d/d vs. 
  first multiplying by each integer by d/d and then adding the quotients */
  lemma lemma_dividing_sums(a: int, b: int, d: int, R: int)
    requires 0 < d
    requires R == a % d + b % d - (a + b) % d
    ensures d * ((a + b) / d) - R == d * (a / d) + d * (b / d)
  {
    calc ==> {
      a % d + b % d == R + (a + b) % d;
      (a + b) - (a + b) % d - R == a - (a % d) + b - (b % d);
        {
          lemma_fundamental_div_mod(a + b, d);
          lemma_fundamental_div_mod(a, d);
          lemma_fundamental_div_mod(b, d);
        }
      d * ((a + b) / d) - R == d * (a / d) + d * (b / d);
    }
  }

  lemma lemma_dividing_sums_auto()
    ensures forall a: int, b: int, d: int, R: int {:trigger d * ((a + b) / d) - R, d*(a/d) + d*(b/d)}
        :: 0 < d &&  R == a%d + b%d - (a+b)%d ==> d*((a+b)/d) - R == d*(a/d) + d*(b/d)
  {
    forall (a: int, b: int, d: int, R: int | 0< d &&  R == a%d + b%d - (a+b)%d)
      ensures d*((a+b)/d) - R == d*(a/d) + d*(b/d)
    {
      lemma_dividing_sums(a, b, d, R);
    }
  }

  /* dividing a whole number by a natural number will result in a quotient that is 
  greater than or equal to 0 */
  lemma lemma_div_pos_is_pos(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures 0 <= x / d
  {
    lemma_div_induction_auto(d, x, u => 0 <= u ==> u / d >= 0);
  }

  lemma lemma_div_pos_is_pos_auto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x && 0 < d ==> 0 <= x / d
  {
    forall (x: int, d: int | 0 <= x && 0 < d)
      ensures 0 <= x / d
    {
      lemma_div_pos_is_pos(x, d);
    }
  }

  /* dividing an integer and then adding 1 to the quotient is the same as adding 
  the divisor and the integer, and then dividing that sum by the divisor */
  lemma lemma_div_plus_one(x: int, d: int)
    requires 0 < d
    ensures 1 + x / d == (d + x) / d
  {
    lemma_div_auto(d);
  }

  lemma lemma_div_plus_one_auto()
    ensures forall x: int, d: int {:trigger 1 + x / d, (d + x) / d} :: 0 < d ==> 1 + x / d == (d + x) / d
  {
    forall (x: int, d: int | 0 < d)
      ensures 1 + x / d == (d + x) / d
    {
      lemma_div_plus_one(x, d);
    }
  }

  /* dividing an integer and then subtracting 1 from the quotient is the same as subtracting 
  the divisor from the integer, and then dividing that difference by the divisor */
  lemma lemma_div_minus_one(x: int, d: int)
    requires 0 < d
    ensures -1 + x / d == (-d + x) / d
  {
    lemma_div_auto(d);
  }

  lemma lemma_div_minus_one_auto()
    ensures forall x: int, d: int {:trigger -1 + x / d, (-d + x) / d} :: 0 < d ==> -1 + x / d == (-d + x) / d
  {
    forall (x: int, d: int | 0 < d)
      ensures -1 + x / d == (-d + x) / d
    {
      lemma_div_minus_one(x, d);
    }
  }

  /* dividing a smaller integer by a larger integer results in a quotient of 0 */
  lemma lemma_basic_div(d: int)
    requires 0 < d
    ensures forall x {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    lemma_div_auto(d);
  }

  lemma lemma_basic_div_auto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 <= x < d ==> x / d == 0
  {
    forall (x: int, d: int | 0 <= x < d)
      ensures x / d == 0
    {
      lemma_basic_div(d);
    }
  }

  /* numerical order is preserved when dividing two seperate integers by a common positive divisor */
  lemma lemma_div_is_ordered(x: int, y: int, z: int)
    requires x <= y
    requires 0 < z
    ensures x / z <= y / z
  {
    lemma_div_induction_auto(z, x - y, xy => xy <= 0 ==> (xy + y) / z <= y / z);
  }

  lemma lemma_div_is_ordered_auto()
    ensures forall x: int, y: int, z: int {:trigger x / z, y / z} :: x <= y && 0 < z ==> x / z <= y / z
  {
    forall (x: int, y: int, z: int | x <= y && 0 < z)
      ensures x / z <= y / z
    {
      lemma_div_is_ordered(x, y, z);
    }
  }

  /* dividing an integer by 2 or more results in a quotient that is smaller than the 
  original dividend */
  lemma lemma_div_decreases(x: int, d: int)
    requires 0 < x
    requires 1 < d
    ensures x / d  < x
  {
    lemma_div_induction_auto(d, x, u => 0 < u ==> u / d < u);
  }

  lemma lemma_div_decreases_auto()
    ensures forall x: int, d: int {:trigger x / d} :: 0 < x && 1 < d ==> x / d < x
  {
    forall (x: int, d: int | 0 < x && 1 < d)
      ensures x / d < x
    {
      lemma_div_decreases(x, d);
    }
  }

  /* dividing an integer by 1 or more results in a quotient that is less than or equal to 
  the original dividend */
  lemma lemma_div_nonincreasing(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x / d  <= x
  {
    lemma_div_induction_auto(d, x, u => 0 <= u ==> u / d <= u);
  }

  lemma lemma_div_nonincreasing_auto()
    ensures forall x: int, d: int {:trigger x / d } :: 0 <= x && 0 < d ==> x / d <= x
  {
    forall (x: int, d: int | 0 <= x && 0 < d)
      ensures x / d <= x 
    {
      lemma_div_nonincreasing(x, d);
    }
  }

  /* a natural number x divided by a larger natural number gives a remainder equal to x */
  lemma lemma_small_mod(x: nat, m: nat)
    requires x < m
    requires 0 < m
    ensures x % m == x
  {
    ModINL.lemma_small_mod(x, m);
  }

  lemma lemma_breakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures 0 < y * z
    ensures x % (y * z) ==y * ((x / y) % z) + x % y
  {
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);
    assert 0 <= x / y;

    calc {
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
        <=    { lemma_part_bound1(x, y, z); }
      y * (z - 1) + (x % y) % (y * z);
        <    { lemma_part_bound2(x, y, z); }
      y * (z - 1) + y;
            { lemma_mul_basics_auto(); }
      y * (z - 1) + y * 1;
            { lemma_mul_is_distributive_auto(); }
      y * (z - 1 + 1);
      y * z;
    }

    calc {
      x % (y * z);
            { lemma_fundamental_div_mod(x,y); }
      (y * (x / y) + x % y) % (y * z);
            {
              lemma_mod_properties_auto();
              assert 0 <= x % y;
              lemma_mul_nonnegative(y, x / y);
              assert (y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z;
              lemma_mod_adds(y * (x / y), x % y, y * z);
            }
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
            {
              lemma_mod_properties_auto();
              lemma_mul_increases(z, y);
              lemma_mul_is_commutative_auto();
              assert x % y < y <= y * z;
              lemma_small_mod(x % y, y * z);
              assert (x % y) % (y * z) == x % y;
            }
      (y * (x / y)) % (y * z) + x % y;
            { lemma_truncate_middle(x / y, y, z); }
      y * ((x / y) % z) + x % y;
    }
  }

  lemma lemma_breakdown_auto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % (y * z), y * ((x / y) % z) + x % y} 
        :: 0 <= x && 0 < y && 0 < z ==> 0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y
  {
    forall (x: int, y: int, z: int  | 0 <= x && 0 < y && 0 < z)
      ensures 0 < y * z && x % (y * z) == y * ((x / y) % z) + x % y
    {
      lemma_breakdown(x, y, z);
    }
  }
  
  lemma lemma_remainder_upper(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures x - d < x / d * d
  {
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, u => 0 <= u ==> u - d < u / d * d);
  }

  lemma lemma_remainder_upper_auto()
    ensures forall x: int, d: int {:trigger x - d, d * d} :: 0 <= x && 0 < d ==> x - d < x / d * d
  {
    forall (x: int, d: int | 0 <= x && 0 < d)
      ensures x - d < x / d * d
    {
      lemma_remainder_upper(x, d);
    }
  }
  
  lemma lemma_remainder_lower(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures  x >= x / d * d
  {
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, u => 0 <= u ==> u >= u / d * d);
  }

  lemma lemma_remainder_lower_auto()
    ensures forall x: int, d: int {:trigger x / d * d} :: 0 <= x && 0 < d ==> x >= x / d * d
  {
    forall x: int, d: int | 0 <= x && 0 < d
      ensures x >= x / d * d
    {
      lemma_remainder_lower(x, d);
    }
  }
  
  lemma lemma_remainder(x: int, d: int)
    requires 0 <= x
    requires 0 < d
    ensures  0 <= x - (x / d * d) < d
  {
    lemma_mul_auto();
    lemma_div_induction_auto(d, x, u => 0 <= u - u / d * d < d);
  }

  lemma lemma_remainder_auto()
    ensures forall x: int, d: int {:trigger x - (x / d * d)} :: 0 <= x && 0 < d ==> 0 <= x - (x / d * d) < d
  {
    forall x: int, d: int | 0 <= x && 0 < d 
      ensures 0 <= x - (x / d * d) < d
    {
      lemma_remainder(x, d);
    }
  }

 /* describes fundementals of the modulus operator */
  lemma lemma_fundamental_div_mod(x: int, d: int)
    requires d != 0
    ensures x == d * (x / d) + (x % d)
  {
    ModINL.lemma_fundamental_div_mod(x, d);
  }

  lemma lemma_fundamental_div_mod_auto()
    ensures forall x: int, d: int {:trigger d * (x / d) + (x % d)} :: d != 0 ==> x == d * (x / d) + (x % d) 
  {
    forall x: int, d: int | d != 0
      ensures x == d * (x / d) + (x % d)
    {
      lemma_fundamental_div_mod(x, d);
    }
  }

  /* dividing a fraction by a divisor is equivalent to multiplying the fraction's 
  denominator with the divisor */
  lemma lemma_div_denominator(x: int,c: nat,d: nat)
    requires 0 <= x
    requires 0 < c
    requires 0 < d
    ensures c * d != 0
    ensures (x / c) / d == x / (c * d)
  {
    lemma_mul_strictly_positive_auto();
    var R := x % (c * d);
    lemma_mod_properties_auto();

    lemma_div_pos_is_pos(R, c);
    if (R / c >= d) {
      lemma_fundamental_div_mod(R, c);
      lemma_mul_inequality(d, R / c, c);
      lemma_mul_is_commutative_auto();
      assert false;
    }
    assert R / c < d;

    lemma_mul_basics_auto();
    lemma_fundamental_div_mod_converse(R / c, d, 0, R / c);
    assert (R / c) % d == R / c;

    lemma_fundamental_div_mod(R, c);
    assert c * (R / c) + R % c == R;

    assert c * ((R / c) % d) + R % c == R;

    var k := x / (c * d);
    lemma_fundamental_div_mod(x, c * d);
    assert x == (c * d) * (x / (c * d)) + x % (c * d);
    assert R == x - (c * d) * (x / (c * d));
    assert R == x - (c * d) * k;

    calc {
      c * ((x / c) % d) + x % c;
        { lemma_mod_multiples_vanish(-k, x / c, d); lemma_mul_is_commutative_auto(); }
      c * ((x / c + (-k) * d) % d) + x % c;
        { lemma_hoist_over_denominator(x, (-k)*d, c); }
      c * (((x + (((-k) * d) * c)) / c) % d) + x % c;
        { lemma_mul_is_associative(-k, d, c); }
      c * (((x + ((-k) * (d * c))) / c) % d) + x % c;
        { lemma_mul_unary_negation(k, d * c); }
      c * (((x + (-(k * (d * c)))) / c) % d) + x % c;
        { lemma_mul_is_associative(k, d, c); }
      c * (((x + (-(k * d * c))) / c) % d) + x % c;
      c * (((x - k * d * c) / c) % d) + x % c;
        {
          lemma_mul_is_associative_auto();
          lemma_mul_is_commutative_auto();
        }
      c * ((R / c) % d) + x % c;
      c * (R / c) + x % c;
        { lemma_fundamental_div_mod(R, c);
          assert R == c * (R / c) + R % c;
          lemma_mod_mod(x, c, d);
          assert R % c == x % c;
        }
      R;
        { lemma_mod_is_mod_recursive_auto(); }
      R % (c * d);
      (x - (c * d) * k) % (c * d);
        { lemma_mul_unary_negation(c * d, k); }
      (x + (c * d) * (-k)) % (c * d);
        { lemma_mod_multiples_vanish(-k, x, c * d); }
      x % (c * d);
    }
    calc ==> {
      c * (x / c) + x % c - R == c * (x / c) - c * ((x / c) % d);
        { lemma_fundamental_div_mod(x, c); }
      x - R == c * (x / c) - c * ((x / c) % d);
    }
    calc ==> {
      true;
        { lemma_fundamental_div_mod(x / c, d); }
      d * ((x / c) / d) == x / c - ((x / c) % d);
      c * (d * ((x / c) / d)) == c * (x / c - ((x / c) % d));
        { lemma_mul_is_associative_auto(); }
      (c * d) * ((x / c) / d) == c * (x / c - ((x / c) % d));
        { lemma_mul_is_distributive_auto(); }
      (c * d) * ((x / c) / d) == c * (x / c) - c * ((x / c) % d);
      (c * d) * ((x / c) / d) == x - R;
        { lemma_fundamental_div_mod(x, c * d); }
      (c * d) * ((x / c) / d) == (c * d) * (x / (c * d)) + x % (c * d) - R;
      (c * d) * ((x / c) / d) == (c * d) * (x / (c * d));
        { lemma_mul_equality_converse(c * d, (x / c) / d, x / (c * d)); }
      (x / c) / d == x / (c * d);
    }
  }
  
  lemma lemma_div_denominator_auto()
    ensures forall c: nat, d: nat {:trigger c * d} :: 0 < c && 0 < d ==> c * d != 0
    ensures forall x: int, c: nat, d: nat {:trigger (x / c) / d} 
      :: 0 <= x && 0 < c && 0 < d ==> (x / c) / d == x / (c * d)
  {
    lemma_mul_nonzero_auto();
    forall x: int, c: nat, d: nat | 0 <= x && 0 < c && 0 < d
      ensures (x / c) / d == x / (c * d)
    {
      lemma_div_denominator(x, c, d);
    }
  }

  /* mutltiplying an integer by a fraction is equivalent to multiplying the integer by the
  fraction's numerator */
  lemma lemma_mul_hoist_inequality(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < z
    ensures x * (y / z) <= (x * y) / z
  {
    calc {
      (x * y) / z;
        { lemma_fundamental_div_mod(y, z); }
      (x * (z * (y / z) + y % z)) / z;
        { lemma_mul_is_distributive_auto(); }
      (x * (z * (y / z)) + x * (y % z)) / z;
        >=  {
            lemma_mod_properties_auto();
            lemma_mul_nonnegative(x, y % z);
            lemma_div_is_ordered(x * (z * (y / z)), x * (z * (y / z)) + x * (y % z), z); }
      (x * (z * (y / z))) / z;
          { lemma_mul_is_associative_auto();
            lemma_mul_is_commutative_auto(); }
      (z * (x * (y / z))) / z;
          { lemma_div_multiples_vanish(x * (y / z), z); }
      x * (y / z);
    }
  }
  
  lemma lemma_mul_hoist_inequality_auto()
    ensures forall x: int, y: int, z: int {:trigger x * (y / z), (x * y) / z} 
      :: 0 <= x && 0 < z ==> x * (y / z) <= (x * y) / z
  {
    forall (x: int, y: int, z: int | 0 <= x && 0 < z)
      ensures x * (y / z) <= (x * y) / z
    {
      lemma_mul_hoist_inequality(x, y, z);
    }
  }

  lemma lemma_indistinguishable_quotients(a: int, b: int, d: int)
    requires 0 < d
    requires 0 <= a - a % d <= b < a + d - a % d
    ensures a / d == b / d
  {
    lemma_div_induction_auto(d, a - b, ab => var u := ab + b; 0 <= u - u % d <= b < u + d - u % d ==> u / d == b / d);
  }

  lemma lemma_indistinguishable_quotients_auto()
    ensures forall a: int, b: int, d: int {:trigger a / d, b / d} 
      :: 0 < d && 0 <= a - a % d <= b < a + d - a % d ==> a / d == b / d
  {
    forall a: int, b: int, d: int | 0 < d && 0 <= a - a % d <= b < a + d - a % d 
      ensures a / d == b / d
    {
      lemma_indistinguishable_quotients(a, b, d);
    } 
  }

  /* common factors from the dividend and divisor of a modulus operation can be factored out */
  lemma lemma_truncate_middle(x: int, b: int, c: int)
    requires 0 <= x
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures (b * x) % (b * c) == b * (x % c)
  {
    lemma_mul_strictly_positive_auto();
    lemma_mul_nonnegative_auto();
    calc {
      b * x;
        { lemma_fundamental_div_mod(b * x, b * c); }
      (b * c) * ((b * x) / (b * c)) + (b * x) % (b * c);
        { lemma_div_denominator(b * x, b, c); }
      (b * c) * (((b * x) / b) / c) + (b * x) % (b * c);
        { lemma_mul_is_commutative_auto(); lemma_div_by_multiple(x, b); }
      (b * c) * (x / c) + (b * x) % (b * c);
    }
    calc ==> {
      true;
        { lemma_fundamental_div_mod(x, c); }
      x == c * (x / c) + x % c;
      b * x == b * (c * (x / c) + x % c);
        { lemma_mul_is_distributive_auto(); }
      b * x == b * (c * (x / c)) + b * (x % c);
        { lemma_mul_is_associative_auto(); }
      b * x == (b * c) * (x / c) + b * (x % c);
    }
  }

  lemma lemma_truncate_middle_auto()
    ensures forall x: int, b: int, c: int {:trigger b * (x % c)} 
      :: 0 <= x && 0 < b && 0 < c && 0 < b * c ==> (b * x) % (b * c) == b * (x % c)
  {
    forall x: int, b: int, c: int | 0 <= x && 0 < b && 0 < c && 0 < b * c 
      ensures (b * x) % (b * c) == b * (x % c)
    {
      lemma_truncate_middle(x, b, c);
    }
  }

  /* multiplying the numerator and denominator by an integer does not change the quotient */
  lemma lemma_div_multiples_vanish_quotient(x: int, a: int, d: int)
    requires 0 < x
    requires 0 <= a
    requires 0 < d
    ensures 0 < x * d
    ensures a / d == (x * a) / (x * d)
  {
    lemma_mul_strictly_positive(x,d);
    calc {
      (x * a) / (x * d);
        {
          lemma_mul_nonnegative(x, a);
          lemma_div_denominator(x * a, x, d); }
      ((x * a) / x) / d;
        { lemma_div_multiples_vanish(a, x); }
      a / d;
    }
  }

  lemma lemma_div_multiples_vanish_quotient_auto()
    ensures forall x: int, a: int, d: int {:trigger a / d, x * d, x * a} 
      :: 0 < x && 0 <= a && 0 < d ==> 0 < x * d  &&  a / d == (x * a) / (x * d)
  {
    forall x: int, a: int, d: int | 0 < x && 0 <= a && 0 < d
      ensures 0 < x * d  &&  a / d == (x * a) / (x * d)
    {
      lemma_div_multiples_vanish_quotient(x, a, d);
    }
  }

  /* rounds down when adding an integer r to the dividend a that is smaller than the divisor d, and then
  multiplying by d */
  lemma lemma_round_down(a: int, r: int, d: int)
    requires 0 < d
    requires a % d == 0
    requires 0 <= r < d
    ensures a == d * ((a + r) / d)
  {
    lemma_mul_auto();
    lemma_div_induction_auto(d, a, u => u % d == 0 ==> u == d * ((u + r) / d));
  }

  lemma lemma_round_down_auto()
    ensures forall a: int, r: int, d: int {:trigger d * ((a + r) / d)} 
      :: 0 < d && a % d == 0 && 0 <= r < d ==> a == d * ((a + r) / d)
  {
    forall a: int, r: int, d: int | 0 < d && a % d == 0 && 0 <= r < d
      ensures a == d * ((a + r) / d)
    {
      lemma_round_down(a, r, d);
    }
  }

  /* this is the same as writing x + (b/d) == x when b is less than d; this is true because (b/d) == 0 */
  lemma lemma_div_multiples_vanish_fancy(x: int, b: int, d: int)
    requires 0 < d
    requires 0 <= b < d
    ensures (d * x + b) / d == x
  {
    lemma_div_auto(d);
    var f := u => (d * u + b) / d == u;
    lemma_mul_induction_auto(x, f);
    assert f(x);
  }

  lemma lemma_div_multiples_vanish_fancy_auto()
    ensures forall x: int, b: int, d: int {:trigger (d * x + b) / d}
      :: 0 < d && 0 <= b < d ==> (d * x + b) / d == x
  {
    forall x: int, b: int, d: int | 0 < d && 0 <= b < d 
      ensures (d * x + b) / d == x
    {
      lemma_div_multiples_vanish_fancy(x, b, d);
    }
  }

  /* multiplying an integer by a common numerator and denominator results in the original integer */
  lemma lemma_div_multiples_vanish(x: int, d: int)
    requires 0 < d
    ensures (d * x) / d == x
  {
    lemma_div_multiples_vanish_fancy(x, 0, d);
  }

  lemma lemma_div_multiples_vanish_auto()
    ensures forall x: int, d: int {:trigger (d * x) / d} :: 0 < d ==> (d * x) / d == x
  {
    forall x: int, d: int | 0 < d 
      ensures (d * x) / d == x
    {
      lemma_div_multiples_vanish(x, d);
    }
  }

  /* multiplying a whole number by a common numerator and denominator results in the original integer */
  lemma lemma_div_by_multiple(b: int, d: int)
    requires 0 <= b
    requires 0 < d
    ensures  (b * d) / d == b
  {   
    lemma_div_multiples_vanish(b,d);
  }

  lemma lemma_div_by_multiple_auto()
    ensures forall b: int, d: int {:trigger (b * d) / d} :: 0 <= b && 0 < d ==> (b * d) / d == b
  {
    forall b: int, d: int | 0 <= b && 0 < d
      ensures (b * d) / d == b
    {
      lemma_div_by_multiple(b, d);
    }
  } 

  /* a dividend y that is a positive multiple of the divisor z will always yield a greater quotient 
  than a dividend x that is less than y */
  lemma lemma_div_by_multiple_is_strongly_ordered(x: int, y: int, m: int, z: int)
    requires x < y
    requires y == m * z
    requires 0 < z
    ensures  x / z < y / z
  {
    lemma_mod_multiples_basic(m, z);
    lemma_div_induction_auto(z, y - x, yx => var u := yx + x; x < u && u % z == 0 ==> x / z < u / z);
  }

  lemma lemma_div_by_multiple_is_strongly_ordered_auto()
    ensures forall x: int, y: int, m: int, z: int {:trigger x / z, m * z, y / z} 
      :: x < y && y == m * z && 0 < z ==> x / z < y / z
  {
    forall x: int, y: int, m: int, z: int | x < y && y == m * z && 0 < z
      ensures x / z < y / z
    {
      lemma_div_by_multiple_is_strongly_ordered(x, y, m, z);
    }
  } 

  /* if an integer a is less than or equal to the product of two other integers b and c, then the 
  quotient of a/b will be less than or equal to c */
  lemma lemma_multiply_divide_le(a: int, b: int, c: int)
    requires 0 < b
    requires a <= b * c
    ensures  a / b <= c
  {
    lemma_mod_multiples_basic(c, b);
    lemma_div_induction_auto(b, b * c - a, i => 0 <= i && (i + a) % b == 0 ==> a / b <= (i + a) / b);
    lemma_div_multiples_vanish(c, b);
  }

  lemma lemma_multiply_divide_le_auto()
    ensures forall a: int, b: int, c: int {:trigger a / b , b * c} :: 0 < b && a <= b * c ==> a / b <= c
  {
    forall a: int, b: int, c: int | 0 < b && a <= b * c
      ensures a / b <= c
    {
      lemma_multiply_divide_le(a, b, c);
    }
  }

  /* if an integer a is less than the product of two other integers b and c, then the quotient 
  of a/b will be less than c */
  lemma lemma_multiply_divide_lt(a: int, b: int, c: int)
    requires 0 < b
    requires a < b * c
    ensures  a / b < c
  {
    lemma_mod_multiples_basic(c, b);
    lemma_div_induction_auto(b, b * c - a, i => 0 < i && (i + a) % b == 0 ==> a / b < (i + a) / b);
    lemma_div_multiples_vanish(c, b);
  }

  lemma lemma_multiply_divide_lt_auto()
    ensures forall a: int, b: int, c: int {:trigger a / b, b * c} :: 0 < b && a < b * c ==> a / b < c
  {
    forall a: int, b: int, c: int | 0 < b && a < b * c
      ensures a / b < c
    {
      lemma_multiply_divide_lt(a, b, c);
    }
  }

  /* expresses the equality of giving fractions common denominators and then adding them together */
  lemma lemma_hoist_over_denominator(x: int, j: int, d: nat)
    requires 0 < d
    ensures x / d + j == (x + j * d) / d
  {
    lemma_div_auto(d);
    lemma_mul_induction_auto(j, u => x / d  + u == (x + u * d) / d);
  }

  lemma lemma_hoist_over_denominator_auto()
    ensures forall x: int, j: int, d: nat {:trigger  x / d + j} :: 0 < d ==> x / d + j == (x + j * d) / d
  {
    forall x: int, j: int, d: nat | 0 < d
      ensures x / d + j == (x + j * d) / d
    {
      lemma_hoist_over_denominator(x, j, d);
    }
  }

  lemma lemma_part_bound1(a: int, b: int, c: int)
    requires 0 <= a
    requires 0 < b
    requires 0 < c
    ensures 0 < b * c
    ensures (b * (a / b) % (b * c)) <= b * (c - 1)
  {
    lemma_mul_strictly_positive_auto();
    calc {
      b * (a / b) % (b * c);
        { lemma_fundamental_div_mod(b * (a / b), b * c); }
      b * (a / b) - (b * c) * ((b * (a / b)) / (b * c));
        { lemma_mul_is_associative_auto(); }
      b * (a / b) - b * (c * ((b * (a / b)) / (b * c)));
        { lemma_mul_is_distributive_auto(); }
      b * ((a / b) - (c * ((b * (a / b)) / (b * c))));
    }

    calc ==> {
      true;
        { lemma_mod_properties_auto(); }
      b * (a / b) % (b * c) < b * c;
      b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) < b * c;
        { lemma_mul_is_commutative_auto(); lemma_mul_strict_inequality_converse_auto(); }
      ((a / b) - (c * ((b * (a / b)) / (b * c)))) < c;
      ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= c - 1;
        { lemma_mul_is_commutative_auto(); lemma_mul_inequality_auto(); }
      b * ((a / b) - (c * ((b * (a / b)) / (b * c)))) <= b * (c - 1);
      b * (a / b) % (b * c) <= b * (c - 1);
    }
  }

  lemma lemma_part_bound1_auto()
    ensures forall a: int, b: int, c: int {:trigger b * (a / b) % (b * c)} 
      :: 0 <= a && 0 < b && 0 < c ==> 0 < b * c && (b * (a / b) % (b * c)) <= b * (c - 1)
  {
    forall a: int, b: int, c: int | 0 <= a && 0 < b && 0 < c
      ensures 0 < b * c && (b * (a / b) % (b * c)) <= b * (c - 1)
    {
      lemma_part_bound1(a, b, c);
    }
  }


/*********************************************************************************************************
* Modulus:
**********************************************************************************************************/
 
  /* the common syntax of the modulus operation results in the same remainder as recursively
  calculating the modulus */
  lemma lemma_mod_is_mod_recursive(x: int, m: int)
    requires m > 0
    ensures mod_recursive(x, m) == x % m
    decreases if x < 0 then -x + m else x
  {
    reveal_mod_recursive();
    if x < 0 { 
      calc { 
        mod_recursive(x, m);
        mod_recursive(x + m, m);
          { lemma_mod_is_mod_recursive(x + m, m); }
        (x + m) % m;
          { lemma_add_mod_noop(x, m, m); } 
        ((x % m) + (m % m)) % m;
          { lemma_mod_basics_auto(); }
        (x % m) % m;
          { lemma_mod_basics_auto(); }
        x % m;
      }
    } else if x < m { 
      lemma_small_mod(x, m);
    } else {
      calc { 
        mod_recursive(x, m);
        mod_recursive(x - m, m);
          { lemma_mod_is_mod_recursive(x - m, m); }
        (x - m) % m;
          { lemma_sub_mod_noop(x, m, m); } 
        ((x % m) - (m % m)) % m;
          { lemma_mod_basics_auto(); }
        (x % m) % m;
          { lemma_mod_basics_auto(); }
        x % m;
      }
    }
  }

  lemma lemma_mod_is_mod_recursive_auto()
    ensures forall x: int, d: int {:trigger x % d}:: d > 0 ==> mod_recursive(x, d) == x % d
  {
    reveal_mod_recursive();
    forall x: int, d: int | d > 0
      ensures mod_recursive(x, d) == x % d
    {
      lemma_mod_is_mod_recursive(x, d);
    }
  }

  /* proves basic properties of the modulus operation: any integer divided by itself does not have a
  remainder; performing (x % m) % m gives the same result as simply perfoming x % m  */
  lemma lemma_mod_basics_auto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger (x % m) % m} :: m > 0 ==> (x % m) % m == x % m
  {
    forall m: int | m > 0
      ensures m % m == 0
    {
      lemma_mod_auto(m);
    }
    forall x: int, m: int | m > 0
      ensures (x % m) % m == x % m
    {
      lemma_mod_auto(m);
    }
  }

  /* describes the properties of the modulus operation including those described in lemma_mod_basics_auto. 
  This lemma also states that the remainder of any division will be less than the divisor's value  */
  lemma lemma_mod_properties_auto()
    ensures forall m: int {:trigger m % m} :: m > 0 ==> m % m == 0
    ensures forall x: int, m: int {:trigger (x % m) % m} :: m > 0 ==> (x % m) % m == x % m
    ensures forall x: int, m: int {:trigger x % m} :: m > 0 ==> 0 <= x % m < m
  {
    lemma_mod_basics_auto();

    forall x: int, m: int | m > 0
      ensures m > 0 ==> 0 <= x % m < m
    {
      lemma_mod_auto(m);
    }
  }

  /* the remainder of a natural number x divided by a natural number d will be less
  than or equal to x */
  lemma lemma_mod_decreases(x: nat, d: nat)
    requires 0 < d
    ensures x % d <= x
  {
    lemma_mod_auto(d);
  }

  lemma lemma_mod_decreases_auto()
    ensures forall x: nat, d: nat {:trigger x % d} :: 0 < d ==> x % d <= x
  {
    forall x: nat, d: nat | 0 < d 
      ensures 0 < d ==> x % d <= x
    {
      lemma_mod_decreases(x, d);
    }
  }
  
  /* a dividend that is any multiple of the divisor will result in a remainder of 0 */
  lemma lemma_mod_multiples_basic(x: int, m: int)
    requires m > 0
    ensures (x * m) % m == 0
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, u => (u * m) % m == 0);
  }

  lemma lemma_mod_multiples_basic_auto()
    ensures forall x: int, m: int {:trigger (x * m) % m} :: m > 0 ==> (x * m) % m == 0
  {
    forall x: int, m: int | m > 0
      ensures (x * m) % m == 0
    {
      lemma_mod_multiples_basic(x, m);
    }
  }

  /* the remainder of adding the divisor m to the dividend b will be the same
  as simply performing b % m */
  lemma lemma_mod_add_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (m + b) % m == b % m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_mod_add_multiples_vanish_auto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m 
      ensures (m + b) % m == b % m
    {
      lemma_mod_add_multiples_vanish(b, m);
    }
  }

  /* the remainder of subtracting the divisor m from the dividend b will be the same
  as simply performing b % m */
  lemma lemma_mod_sub_multiples_vanish(b: int, m: int)
    requires 0 < m
    ensures (-m + b) % m == b % m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_mod_sub_multiples_vanish_auto()
    ensures forall b: int, m: int {:trigger b % m} :: 0 < m ==> (-m + b) % m == b % m
  {
    forall b: int, m: int | 0 < m 
      ensures (-m + b) % m == b % m
    {
      lemma_mod_sub_multiples_vanish(b, m);
    }
  }

  /* the remainder of adding any multiple of the divisor m to the dividend b will be the same
  as simply performing b % m */ 
  lemma lemma_mod_multiples_vanish(a: int, b: int, m: int)
    decreases if a > 0 then a else -a
    requires 0 < m
    ensures (m * a + b) % m == b % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(a, u => (m * u + b) % m == b % m);
  }

  lemma lemma_mod_multiples_vanish_auto()
    ensures forall a: int, b: int, m: int {:trigger (m * a + b) % m} :: 0 < m ==> (m * a + b) % m == b % m
  {
    forall a: int, b: int, m: int | 0 < m
      ensures (m * a + b) % m == b % m
    {
      lemma_mod_multiples_vanish(a, b, m);
    }
  }

  /* true if x%n and y%n are equal */
  predicate is_mod_equivalent(x: int, y: int, m: int)
    requires m > 0
  {
    (x - y) % m == 0 // same as x % n == y % n, but easier to do induction on x - y than x and y separately
  }
  
  /* proves modulus equivalence in two forms */
  lemma lemma_mod_equivalence(x: int, y: int, m: int)
    requires 0 < m
    ensures x % m == y % m <==> (x - y) % m == 0
  {
    lemma_mod_auto(m);
  }

  lemma lemma_mod_equivalence_auto()
    ensures forall x: int, y: int, m: int {:trigger  x % m , y % m} 
      :: 0 < m && x % m == y % m <==> 0 < m && (x - y) % m == 0
  {
    forall x: int, y: int, m: int | 0 < m 
      ensures x % m == y % m <==> 0 < m && (x - y) % m == 0
    {
      lemma_mod_equivalence(x, y, m);
    }
  }

  /* proves equivalent forms of modulus subtraction */
  lemma lemma_mod_subtraction(x: nat, s: nat, d: nat)
    requires 0 < d
    requires 0 <= s <= x % d
    ensures x % d - s % d == (x - s) % d
  {
    lemma_mod_auto(d);
  }

  lemma lemma_mod_subtraction_auto()
    ensures forall x: nat, s: nat, d: nat {:trigger (x - s) % d}
      :: 0 < d && 0 <= s <= x % d ==> x % d - s % d == (x - s) % d
  {
    forall x: nat, s: nat, d: nat | 0 < d && 0 <= s <= x % d
      ensures x % d - s % d == (x - s) % d
    {
      lemma_mod_subtraction(x, s, d);
    }
  }
  
  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma lemma_add_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) + (y % m)) % m == (x + y) % m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_add_mod_noop_auto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m}
      :: 0 < m ==> ((x % m) + (y % m)) % m == (x + y) % m
  {
    forall x: int, y: int, m: int | 0 < m 
      ensures ((x % m) + (y % m)) % m == (x + y) % m
    {
      lemma_add_mod_noop(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to addition (read "ensures") */
  lemma lemma_add_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x + (y % m)) % m == (x + y) % m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_add_mod_noop_right_auto()
    ensures forall x: int, y: int, m: int {:trigger (x + y) % m}
      :: 0 < m ==> (x + (y % m)) % m == (x + y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x + (y % m)) % m == (x + y) % m
    {
      lemma_add_mod_noop_right(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma lemma_sub_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) - (y % m)) % m == (x - y) % m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_sub_mod_noop_auto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} 
      :: 0 < m ==> ((x % m) - (y % m)) % m == (x - y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures ((x % m) - (y % m)) % m == (x - y) % m
    {
      lemma_sub_mod_noop(x, y, m);
    }
  }

  /* describes expanded and succinct version of modulus operator in relation to subtraction (read "ensures") */
  lemma lemma_sub_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures (x - (y % m)) % m == (x - y) % m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_sub_mod_noop_right_auto()
    ensures forall x: int, y: int, m: int {:trigger (x - y) % m} 
      :: 0 < m ==> (x - (y % m)) % m == (x - y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x - (y % m)) % m == (x - y) % m
    {
      lemma_sub_mod_noop_right(x, y, m);
    }
  }

  /* proves equivalent forms of modulus addition */
  lemma lemma_mod_adds(a: int, b: int, d: int)
    requires 0 < d
    ensures a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d)
    ensures (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
  {
    lemma_mul_auto();
    lemma_div_auto(d);
  }

  lemma lemma_mod_adds_auto()
    ensures forall a: int, b: int, d: int {:trigger (a + b) % d} 
      :: 0 < d ==> a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d) 
      && (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
  {
    forall a: int, b: int, d: int | 0 < d
      ensures a % d + b % d == (a + b) % d + d * ((a % d + b % d) / d) 
      && (a % d + b % d) < d ==> a % d + b % d == (a + b) % d
    {
      lemma_mod_adds(a, b, d);
    }
  }

  lemma {:timeLimitMultiplier 2} lemma_mod_neg_neg(x: int, d: int)
    requires 0 < d
    ensures x % d == (x * (1 - d)) % d
  {
    forall ensures (x - x * d) % d == x % d
    {
      lemma_mod_auto(d);
      var f := i => (x - i * d) % d == x % d;
      assert  mul_auto() ==> && f(0)
                            && (forall i {:trigger is_le(0, i)} :: is_le(0, i) && f(i) ==> f(i + 1))
                            && (forall i {:trigger is_le(i, 0)} :: is_le(i, 0) && f(i) ==> f(i - 1));
      lemma_mul_induction_auto(x, f);
    }
    lemma_mul_auto();
  }
  
  /* proves the validity of the quotient and remainder */
  lemma {:timeLimitMultiplier 5} lemma_fundamental_div_mod_converse(x: int, d: int, q: int, r: int)
    requires d != 0
    requires 0 <= r < d
    requires x == q * d + r
    ensures q == x / d 
    ensures r == x % d
  {
    lemma_div_auto(d);
    lemma_mul_induction_auto(q, u => u == (u * d + r) / d);
    lemma_mul_induction_auto(q, u => r == (u * d + r) % d);
  }

  lemma {:timeLimitMultiplier 5} lemma_fundamental_div_mod_converse_auto()
    ensures forall x: int, d: int, q: int, r: int {:trigger q * d + r, x % d}
      :: d != 0 && 0 <= r < d && x == q * d + r ==> q == x / d && r == x % d
  {
    forall x: int, d: int, q: int, r: int | d != 0 && 0 <= r < d && x == q * d + r
      ensures q == x / d && r == x % d
    {
      lemma_fundamental_div_mod_converse(x, d, q, r);
    }
  }


  /* the remainder of any natural number x divided by a positive integer m is always less than m */
  lemma lemma_mod_pos_bound(x: int, m: int)
    decreases x
    requires 0 <= x
    requires 0 < m
    ensures  0 <= x % m < m
  {
    lemma_mod_auto(m);
  }

  lemma lemma_mod_pos_bound_auto()
    ensures forall x: int, m: int {:trigger x % m} :: 0 <= x && 0 < m ==> 0 <= x % m < m
  {
    forall x: int, m: int | 0 <= x && 0 < m 
      ensures 0 <= x % m < m
    {
      lemma_mod_pos_bound(x, m);
    }
  }
  
  /* ensures easier to follow than a comment would be */
  lemma lemma_mul_mod_noop_left(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * y % m == x * y % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(y, u => (x % m) * u % m == x * u % m);
  }

  lemma lemma_mul_mod_noop_left_auto()
    ensures forall x: int, y: int, m: int {:trigger x * y % m} :: 0 < m ==> (x % m) * y % m == x * y % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m) * y % m == x * y % m
    {
      lemma_mul_mod_noop_left(x, y, m);
    }
  }
  
  /* ensures easier to follow than a comment would be */
  lemma lemma_mul_mod_noop_right(x: int, y: int, m: int)
    requires 0 < m
    ensures x * (y % m) % m == (x * y) % m
  {
    lemma_mod_auto(m);
    lemma_mul_induction_auto(x, u => u * (y % m) % m == (u * y) % m);
  }

  lemma lemma_mul_mod_noop_right_auto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m} 
      :: 0 < m ==> x * (y % m) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m 
      ensures x * (y % m) % m == (x * y) % m
    {
      lemma_mul_mod_noop_right(x, y, m);
    }
  }
  
  /* combines previous no-op mod lemmas into a general, overarching lemma */
  lemma lemma_mul_mod_noop_general(x: int, y: int, m: int)
    requires 0 < m
    ensures ((x % m) * y      ) % m == (x * y) % m
    ensures ( x      * (y % m)) % m == (x * y) % m
    ensures ((x % m) * (y % m)) % m == (x * y) % m
  {
    lemma_mod_properties_auto();
    lemma_mul_mod_noop_left(x, y, m);
    lemma_mul_mod_noop_right(x, y, m);
    lemma_mul_mod_noop_right(x % m, y, m);
  }

  lemma lemma_mul_mod_noop_general_auto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m}
      :: 0 < m ==> ((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures ((x % m) * y) % m == (x * (y % m)) % m == ((x % m) * (y % m)) % m == (x * y) % m
    {
      lemma_mul_mod_noop_general(x, y, m);
    }
  }
  
  lemma lemma_mul_mod_noop(x: int, y: int, m: int)
    requires 0 < m
    ensures (x % m) * (y % m) % m == (x * y) % m
  {
    lemma_mul_mod_noop_general(x, y, m);
  }

  lemma lemma_mul_mod_noop_auto()
    ensures forall x: int, y: int, m: int {:trigger (x * y) % m} 
      :: 0 < m ==> (x % m) * (y % m) % m == (x * y) % m
  {
    forall x: int, y: int, m: int | 0 < m
      ensures (x % m) * (y % m) % m == (x * y) % m
    {
      lemma_mul_mod_noop(x, y, m);
    }
  }

  /* the remainder can increase with a larger divisor */
  lemma lemma_mod_ordering(x: int, k: int, d: int)
    requires 1 < d
    requires 0 < k
    ensures 0 < d * k
    ensures x % d <= x % (d * k)
  {
    lemma_mul_strictly_increases(d,k);
    calc {
      x % d + d * (x / d);
        { lemma_fundamental_div_mod(x, d); }
      x;
        { lemma_fundamental_div_mod(x, d * k); }
      x % (d * k) + (d * k) * (x / (d * k));
        { lemma_mul_is_associative_auto(); }
      x % (d * k) + d * (k * (x / (d * k)));
    }
    calc {
      x % d;
        { lemma_mod_properties_auto(); }
      (x % d) % d;
        { lemma_mod_multiples_vanish(x / d  - k * (x / (d * k)), x % d, d); }
      (x % d + d * (x / d  - k * (x / (d * k)))) % d;
        { lemma_mul_is_distributive_sub_auto(); }
      (x % d + d * (x / d) - d * (k * (x / (d * k)))) % d;
      (x % (d * k)) % d;
        <= { lemma_mod_properties_auto();
            lemma_mod_decreases(x % (d * k), d); }
      x % (d * k);
    }
  }

  lemma lemma_mod_ordering_auto()
    ensures forall x: int, k: int, d: int {:trigger x % (d * k)}  
      :: 1 < d && 0 < k ==> 0 < d * k && x % d <= x % (d * k)
  {
    forall x: int, k: int, d: int | 1 < d && 0 < k
      ensures d * k > 0 && x % d <= x % (d * k)
    {
      lemma_mod_ordering(x, k, d);
    }
  }
  
  lemma lemma_mod_mod(x: int, a: int, b: int)
    requires 0 < a
    requires 0 < b
    ensures 0 < a * b
    ensures (x % (a * b)) % a == x % a
  {
    lemma_mul_strictly_positive_auto();
    calc {
      x;
        { lemma_fundamental_div_mod(x, a * b); }
      (a * b) * (x / (a * b)) + x % (a * b);
        { lemma_mul_is_associative_auto(); }
      a * (b * (x / (a * b))) + x % (a * b);
        { lemma_fundamental_div_mod(x % (a * b), a); }
      a * (b * (x / (a * b))) + a * (x % (a * b) / a) + (x % (a * b)) % a;
        { lemma_mul_is_distributive_auto(); }
      a * (b * (x / (a * b)) + x % (a * b) / a) + (x % (a * b)) % a;
    }
    lemma_mod_properties_auto();
    lemma_mul_is_commutative_auto();
    lemma_fundamental_div_mod_converse(x, a, b * (x / (a * b)) + x % (a * b) / a, (x % (a * b)) % a);
  }

  lemma lemma_mod_mod_auto()
    ensures forall x: int, a: int, b: int {:trigger a * b, x % a} 
      :: 0 < a && 0 < b ==> 0 < a * b && (x % (a * b)) % a == x % a
  {
    forall x: int, a: int, b: int | 0 < a && 0 < b  
      ensures 0 < a * b && (x % (a * b)) % a == x % a
    {
      lemma_mod_mod(x, a, b);
    }
  }

  lemma lemma_part_bound2(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures (x % y) % (y * z) < y
  {
    lemma_mul_strictly_positive_auto();
    lemma_mod_properties_auto();
    assert x % y < y;
    lemma_mul_increases_auto();
    lemma_mul_is_commutative_auto();
    assert y <= y * z;
    assert 0 <= x % y < y * z;
    lemma_mod_properties_auto();
    lemma_small_mod(x % y, y * z);
    assert (x % y) % (y * z) == x % y;
  }

  lemma lemma_part_bound2_auto()
    ensures forall x: int, y: int, z: int {:trigger y * z, x % y}
      :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && (x % y) % (y * z) < y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z
      ensures y * z > 0 && (x % y) % (y * z) < y
    {
      lemma_part_bound2(x, y, z);
    }
  }

  /* ensures the validity of an expanded form of the modulus operation,
   as expressed in the pre and post conditions */
  lemma lemma_mod_breakdown(x: int, y: int, z: int)
    requires 0 <= x
    requires 0 < y
    requires 0 < z
    ensures y * z > 0
    ensures x % (y * z) == y * ((x / y) % z) + x % y
  {
    lemma_mul_strictly_positive_auto();
    lemma_div_pos_is_pos(x, y);
    assert 0 <= x / y;

    calc {
      (y * (x / y)) % (y * z) + (x % y) % (y * z);
        <=    { lemma_part_bound1(x, y, z); }
      y * (z - 1) + (x % y) % (y * z);
        <    { lemma_part_bound2(x, y, z); }
      y * (z - 1) + y;
            { lemma_mul_basics_auto(); }
      y * (z - 1) + y * 1;
            { lemma_mul_is_distributive_auto(); }
      y * (z - 1 + 1);
      y * z;
    }

    calc {
      x % (y * z);
            { lemma_fundamental_div_mod(x, y); }
    (y * (x / y) + x%  y) % (y * z);
            {
              lemma_mod_properties_auto();
              assert 0 <= x % y;
              lemma_mul_nonnegative(y, x / y);
              assert (y * (x / y)) % (y * z) + (x % y) % (y * z) < y * z;
              lemma_mod_adds(y * (x / y), x % y, y * z);
            }
    (y * (x / y)) % (y * z) + (x % y) % (y * z);
            {
              lemma_mod_properties_auto();
              lemma_mul_increases(z, y);
              lemma_mul_is_commutative_auto();
              assert x % y < y <= y * z;
              lemma_small_mod(x % y, y * z);
              assert (x % y) % (y * z) == x % y;
            }
    (y * (x / y)) % (y * z) + x % y;
            { lemma_truncate_middle(x / y, y, z); }
    y * ((x / y) % z) + x % y;
    }
  }

  lemma lemma_mod_breakdown_auto()
    ensures forall x: int, y: int, z: int {:trigger x % (y * z)}
      :: 0 <= x && 0 < y && 0 < z ==> y * z > 0 && x % (y * z) == y * ((x / y) % z) + x % y
  {
    forall x: int, y: int, z: int | 0 <= x && 0 < y && 0 < z 
      ensures y * z > 0 && x % (y * z) == y * ((x / y) % z) + x % y
    {
      lemma_mod_breakdown(x, y, z);
    }
  }

}