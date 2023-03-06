// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT
 *******************************************************************************/

include "../src/BinaryOperations.dfy"

module {:options "-functionSyntax:4"} RealsAsFieldExample {

  ghost function plus(x: real, y: real): real {
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

  lemma IsField()
    ensures Field(plus, minus, 0.0, mult, div, 1.0)
  {}

}
