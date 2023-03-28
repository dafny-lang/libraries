// RUN: %verify "%s"

/*******************************************************************************
 *  Copyright by the contributors to the Dafny Project
 *  SPDX-License-Identifier: MIT 
 *******************************************************************************/

/** Defines various integer-math functions */
module {:options "-functionSyntax:4"} Dafny.Math {
  function Min(a: int, b: int): int
  {
    if a < b
    then a
    else b
  }

  function Min3(a: int, b: int, c: int): int
  {
    Min(a, Min(b, c))
  }

  function Max(a: int, b: int): int
  {
    if a < b
    then b
    else a
  }

  function Max3(a: int, b: int, c: int): int
  {
    Max(a, Max(b, c))
  }

  function Abs(a: int): int
  {
    if a < 0
    then -a
    else a
  }
}
