// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*********************************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
**********************************************************************************************/

module BasicMath {
  function method Min(a: int, b: int): int
  {
    if a < b
      then a
    else
      b
  }

  function method Max(a: int, b: int): int
  {
    if a < b
      then b
    else
      a
  }

  predicate Injective<X(!new), Y>(f: X-->Y)
    reads f.reads
    requires forall x :: f.requires(x)
  {
    forall x1, x2 :: f(x1) == f(x2) ==> x1 == x2
  }
}
