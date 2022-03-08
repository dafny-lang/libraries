// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Original: Copyright (c) 2020 Secure Foundations Lab
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module Action {

  trait {:termination false} Action<A, R>
  {
    method Invoke(a: A)
      returns (r: R)
      requires Requires(a)
      ensures Ensures(a, r)

    predicate Requires(a: A)
    predicate Ensures(a: A, r: R)
  }

  trait {:termination false} NothingToRequire<A>
  {
    predicate Requires(a: A){
      true
    }
  }

}
