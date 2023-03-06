// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module {:options "-functionSyntax:4"} BinaryOperations {

  ghost predicate Associative<T(!new)>(bop: (T, T) -> T) {
    forall x, y, z :: bop(bop(x, y), z) == bop(x, bop(y, z))
  }

  ghost predicate UnitalLeft<T(!new)>(bop: (T, T) -> T, unit: T) {
    forall x :: bop(unit, x) == x
  }

  ghost predicate UnitalRight<T(!new)>(bop: (T, T) -> T, unit: T) {
    forall x :: bop(x, unit) == x
  }

  ghost predicate Unital<T(!new)>(bop: (T, T) -> T, unit: T) {
    && UnitalLeft(bop, unit)
    && UnitalRight(bop, unit)
  }

  ghost predicate InverseLeft<T(!new)>(bop: (T, T) -> T, inverse: T --> T, unit: T)
  {
    forall x | inverse.requires(x) :: bop(inverse(x), x) == unit
  }

  ghost predicate InverseRight<T(!new)>(bop: (T, T) -> T, inverse: T --> T, unit: T)
  {
    forall x | inverse.requires(x) :: bop(x, inverse(x)) == unit
  }

  ghost predicate Inverse<T(!new)>(bop: (T, T) -> T, inverse: T --> T, unit: T)
  {
    && InverseLeft(bop, inverse, unit) 
    && InverseRight(bop, inverse, unit)
  }
  
  ghost predicate Abelian<T(!new)>(bop: (T, T) -> T) {
    forall x, y :: bop(x, y) == bop(y, x)
  }

  ghost predicate DistributiveRight<T(!new)>(bop1: (T, T) -> T, bop2: (T, T) -> T) {
    forall x, y, z :: bop2(bop1(x, y), z) == bop1(bop2(x, z), bop2(y, z))
  }

  ghost predicate DistributiveLeft<T(!new)>(bop1: (T, T) -> T, bop2: (T, T) -> T) {
    forall x, y, z :: bop2(x, bop1(y, z)) == bop1(bop2(x, y), bop2(x, z))
  }

  ghost predicate Distributive<T(!new)>(bop1: (T, T) -> T, bop2: (T, T) -> T) {
    && DistributiveLeft(bop1, bop2)
    && DistributiveRight(bop1, bop2)
  }

  ghost predicate Monoid<T(!new)>(bop: (T, T) -> T, unit: T) {
    && Associative(bop) 
    && Unital(bop, unit)
  }

  ghost predicate Group<T(!new)>(bop: (T, T) -> T, inverse: T --> T, unit: T) {
    && Monoid(bop, unit) 
    && Inverse(bop, inverse, unit)
  }

  ghost predicate AbelianGroup<T(!new)>(bop: (T, T) -> T, inverse: T --> T, unit: T) {
    && Group(bop, inverse, unit)
    && Abelian(bop)
  }

  ghost predicate Ring<T(!new)>(add: (T, T) -> T, minus: T -> T, zero: T, mult: (T, T) -> T, one: T) {
    && AbelianGroup(add, minus, zero)
    && Monoid(mult, one)
    && Distributive(add, mult)
  }

  ghost predicate Field<T(!new)>(add: (T, T) -> T, minus: T -> T, zero: T, mult: (T, T) -> T, div: T --> T, one: T) 
    requires forall t :: (t != zero) ==> div.requires(t) 
  {
    && AbelianGroup(add, minus, zero)
    && AbelianGroup(mult, div, one)
    && DistributiveLeft(add, mult)
  }

}
