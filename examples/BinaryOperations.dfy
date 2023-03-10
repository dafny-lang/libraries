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
    ensures IsAssociative(add)
    ensures IsAssociative(mult)
  {}

  lemma IntegersAreMonoid()
    ensures IsMonoid(add, 0)
    ensures IsMonoid(mult, 1)
  {}

  lemma IntegersHaveUnit()
    ensures IsLeftUnital(add, 0)
    ensures IsRightUnital(add, 0)
    ensures IsUnital(add, 0)
    ensures IsLeftUnital(mult, 1)
    ensures IsRightUnital(mult, 1)
    ensures IsUnital(mult, 1)
  {}

  lemma IntegersAreAbelian()
    ensures IsAbelian(add)
    ensures IsAbelian(mult)
  {}

  lemma IntegersAreAdditiveGroup()
    ensures IsGroup(add, minus, 0)
  {}

  lemma IntegersAreAdditiveAbelianGroup()
    ensures IsAbelianGroup(add, minus, 0)
  {}

  lemma IntegersHaveAdditiveInverse()
    ensures IsInverse(add, minus, 0)
  {}

  lemma IntegersAreDistributive()
    ensures IsLeftDistributive(add, mult)
    ensures IsRightDistributive(add, mult)
    ensures IsDistributive(add, mult)
  {}

  lemma IntegersAreRing()
    ensures IsRing(add, minus, 0, mult, 1)
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
    ensures IsAssociative(add)
    ensures IsAssociative(mult)
  {}

  lemma RealsAreMonoid()
    ensures IsMonoid(add, 0.0)
    ensures IsMonoid(mult, 1.0)
  {}

  lemma RealsHaveUnit()
    ensures IsLeftUnital(add, 0.0)
    ensures IsRightUnital(add, 0.0)
    ensures IsUnital(add, 0.0)
    ensures IsLeftUnital(mult, 1.0)
    ensures IsRightUnital(mult, 1.0)
    ensures IsUnital(mult, 1.0)
  {}

  lemma RealsAreAbelian()
    ensures IsAbelian(add)
    ensures IsAbelian(mult)
  {}

  lemma RealsAreAdditiveGroup()
    ensures IsGroup(add, minus, 0.0)
  {}

  lemma RealsAreAdditiveAbelianGroup()
    ensures IsAbelianGroup(add, minus, 0.0)
  {}

  lemma NonZeroRealsAreMultiplicativeGroup()
    ensures IsGroup(mult, div, 1.0)
  {}

  lemma NonZeroRealsAreMultiplicativeAbelianGroup()
    ensures IsAbelianGroup(mult, div, 1.0)
  {}

  lemma RealsHaveAdditiveInverse()
    ensures IsInverse(add, minus, 0.0)
  {}

  lemma RealsAreDistributive()
    ensures IsLeftDistributive(add, mult)
    ensures IsRightDistributive(add, mult)
    ensures IsDistributive(add, mult)
  {}

  lemma RealsAreRing()
    ensures IsRing(add, minus, 0.0, mult, 1.0)
  {
    assert IsDistributive(add, mult);
  }

  lemma RealsAreField()
    ensures IsField(add, minus, 0.0, mult, div, 1.0)
  {}

}
