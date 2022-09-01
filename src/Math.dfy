// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module Math {
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

  function method Abs(a: int): (a': int)
    ensures a' >= 0
  {
    if a >= 0 then a else -a
  }

  function method {:opaque} IntPow(x: int, n: nat) : int {
    if n == 0 then 1
    else x * IntPow(x, n - 1)
  }
}
