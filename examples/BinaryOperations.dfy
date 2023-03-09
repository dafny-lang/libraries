// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../src/dafny/BinaryOperations.dfy"

module {:options "-functionSyntax:4"} IntegersExample {

  import opened BinaryOperations

  ghost function add(x: int, y: int): int {
    x + y
  }

  ghost function minus(x: int): int {
    -x
  }

  ghost function mult(x: int, y: int): int {
    x * y
  }

  lemma IntegersAreAssociative()
    ensures Associative(add)
    ensures Associative(mult)
  {}

  lemma IntegersAreMonoid()
    ensures Monoid(add, 0)
    ensures Monoid(mult, 1)
  {}

  lemma IntegersHaveUnit()
    ensures UnitalLeft(add, 0)
    ensures UnitalRight(add, 0)
    ensures Unital(add, 0)
    ensures UnitalLeft(mult, 1)
    ensures UnitalRight(mult, 1)
    ensures Unital(mult, 1)
  {}

  lemma IntegersAreAbelian()
    ensures Abelian(add)
    ensures Abelian(mult)
  {}
  
  lemma IntegersAreAdditiveGroup()
    ensures Group(add, minus, 0)
  {}

  lemma IntegersAreAdditiveAbelianGroup()
    ensures AbelianGroup(add, minus, 0)
  {}

  lemma IntegersHaveAdditiveInverse()
    ensures Inverse(add, minus, 0)
  {}

  lemma IntegersAreDistributive()
    ensures DistributiveLeft(add, mult)
    ensures DistributiveRight(add, mult)
    ensures Distributive(add, mult)
  {}

  lemma IntegersAreRing()
    ensures Ring(add, minus, 0, mult, 1)
  {}

}

module {:options "-functionSyntax:4"} RealsExample {

  import opened BinaryOperations

  ghost function add(x: real, y: real): real {
    x + y
  }

  ghost function minus(x: real): real {
    -x
  }

  ghost function mult(x: real, y: real): real {
    x * y
  }

  ghost function div(x: real): real
    requires x != 0.0
  {
    1.0 / x
  }

  lemma RealsAreAssociative()
    ensures Associative(add)
    ensures Associative(mult)
  {}

  lemma RealsAreMonoid()
    ensures Monoid(add, 0.0)
    ensures Monoid(mult, 1.0)
  {}

  lemma RealsHaveUnit()
    ensures UnitalLeft(add, 0.0)
    ensures UnitalRight(add, 0.0)
    ensures Unital(add, 0.0)
    ensures UnitalLeft(mult, 1.0)
    ensures UnitalRight(mult, 1.0)
    ensures Unital(mult, 1.0)
  {}

  lemma RealsAreAbelian()
    ensures Abelian(add)
    ensures Abelian(mult)
  {}

  lemma RealsAreAdditiveGroup()
    ensures Group(add, minus, 0.0)
  {}

  lemma RealsAreAdditiveAbelianGroup()
    ensures AbelianGroup(add, minus, 0.0)
  {}

  lemma NonZeroRealsAreMultiplicativeGroup()
    ensures Group(mult, div, 1.0)
  {}

  lemma NonZeroRealsAreMultiplicativeAbelianGroup()
    ensures AbelianGroup(mult, div, 1.0)
  {}

  lemma RealsHaveAdditiveInverse()
    ensures Inverse(add, minus, 0.0)
  {}

  lemma RealsAreDistributive()
    ensures DistributiveLeft(add, mult)
    ensures DistributiveRight(add, mult)
    ensures Distributive(add, mult)
  {}

  lemma RealsAreRing()
    ensures AbelianGroup(add, minus, 0.0)
    ensures Monoid(mult, 1.0)
    ensures Distributive(add, mult)
    ensures Ring(add, minus, 0.0, mult, 1.0)
  {}

  lemma RealsAreField()
    ensures Field(add, minus, 0.0, mult, div, 1.0)
  {}

}
