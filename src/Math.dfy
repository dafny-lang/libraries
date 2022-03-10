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

}
