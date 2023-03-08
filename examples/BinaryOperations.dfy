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

  lemma IntegersAreAbelian()
    ensures Abelian(add)
    ensures Abelian(mult)

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

  lemma RealsAreAbelianGroup()
    ensures AbelianGroup(add, minus, 0.0)
  {}

  lemma RealsArePartlyAbelianGroup()
    ensures AbelianGroup(mult, div, 1.0)
  {}

  lemma RealsAreDistributive()
    ensures Distributive(add, mult) 
  {}

  lemma RealsAreRing()
    ensures Ring(add, minus, 0.0, mult, 1.0)
  {}

  lemma RealsAreField()
    ensures Field(add, minus, 0.0, mult, div, 1.0)
  {}

}
