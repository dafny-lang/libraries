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

  lemma IsAbelianGroup()
    ensures AbelianGroup(add, minus, 0)
  {}

  lemma IsMonoid()
    ensures Monoid(mult, 1)
  {}

  lemma IsDistributive()
    ensures Distributive(add, mult)
  {}

  lemma IsRing()
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

  lemma IsAdditiveAbelianGroup()
    ensures AbelianGroup(add, minus, 0.0)
  {}

  lemma IsPartlyMultiplicativeAbelianGroup()
    ensures AbelianGroup(mult, div, 1.0)
  {}

  lemma IsDistributive()
    ensures Distributive(add, mult) 
  {}

  lemma IsRing()
    ensures Ring(add, minus, 0.0, mult, 1.0)
  {}

  lemma IsField()
    ensures Field(add, minus, 0.0, mult, div, 1.0)
  {}

}
