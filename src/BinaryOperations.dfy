// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

module {:options "-functionSyntax:4"} BinaryOperations {

  ghost predicate Associative<T(!new)>(bop: (T, T) -> T) {
    forall x, y, z :: bop(bop(x, y), z) == bop(x, bop(y, z))
  }

  ghost predicate UnitalLeft<T(!new)>(bop: (T, T) -> T, e: T) {
    forall x :: bop(e, x) == x
  }

  ghost predicate UnitalRight<T(!new)>(bop: (T, T) -> T, e: T) {
    forall x :: bop(x, e) == x
  }

  ghost predicate Unital<T(!new)>(bop: (T, T) -> T, e: T) {
    && UnitalLeft(bop, e)
    && UnitalRight(bop, e)
  }

  ghost predicate InverseLeft<T(!new)>(bop: (T, T) -> T, inv: T --> T, e: T)
  {
    forall x | inv.requires(x) :: bop(inv(x), x) == e
  }

  ghost predicate InverseRight<T(!new)>(bop: (T, T) -> T, inv: T --> T, e: T)
  {
    forall x | inv.requires(x) :: bop(x, inv(x)) == e
  }

  ghost predicate Inverse<T(!new)>(bop: (T, T) -> T, inv: T --> T, e: T)
  {
    && InverseLeft(bop, inv, e) 
    && InverseRight(bop, inv, e)
  }
  
  ghost predicate Abelian<T(!new)>(bop: (T, T) -> T) {
    forall x, y :: bop(x, y) == bop(y, x)
  }

  ghost predicate DistributiveLeft<T(!new)>(bop1: (T, T) -> T, bop2: (T, T) -> T) {
    forall x, y, z :: bop2(bop1(x, y), z) == bop1(bop2(x, z), bop2(y, z))
  }

  ghost predicate DistributiveRight<T(!new)>(bop1: (T, T) -> T, bop2: (T, T) -> T) {
    forall x, y, z :: bop2(x, bop1(y, z)) == bop1(bop2(x, y), bop2(x, z))
  }

  ghost predicate Distributive<T(!new)>(bop1: (T, T) -> T, bop2: (T, T) -> T) {
    && DistributiveLeft(bop1, bop2)
    && DistributiveRight(bop1, bop2)
  }

  ghost predicate Monoid<T(!new)>(bop: (T, T) -> T, e: T) {
    && Associative(bop) 
    && Unital(bop, e)
  }

  ghost predicate Group<T(!new)>(bop: (T, T) -> T, inv: T --> T, e: T) {
    && Monoid(bop, e) 
    && Inverse(bop, inv, e)
  }

  ghost predicate AbelianGroup<T(!new)>(bop: (T, T) -> T, inv: T --> T, e: T) {
    && Group(bop, inv, e)
    && Abelian(bop)
  }

  ghost predicate Field<T(!new)>(plus: (T, T) -> T, minus: T -> T, zero: T, mult: (T, T) -> T, div: T --> T, one: T) 
    requires forall t :: (t != zero) ==> div.requires(t) 
  {
    && AbelianGroup(plus, minus, zero)
    && AbelianGroup(mult, div, one)
    && DistributiveLeft(plus, mult)
  }

}
