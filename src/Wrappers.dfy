// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module Wrappers {
  
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string> {
      match this
      case Some(v) => Success(v)
      case None() => Failure("Option is None")
    }
    
    function method UnwrapOr(default: T): T {
      match this
      case Some(v) => v
      case None() => default
    }

    predicate method IsFailure() {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
    {
      None
    }

    function method Extract(): T
      requires Some?
    {
      value
    }
  }

  datatype Result<+T, +R> = | Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T> 
    {
      match this
      case Success(s) => Some(s)
      case Failure(e) => None()
    }

    function method UnwrapOr(default: T): T 
    {
      match this
      case Success(s) => s
      case Failure(e) => default
    }

    predicate method IsFailure() {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
    {
      Failure(this.error)
    }

    function method MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
    {
      match this
      case Success(s) => Success(s)
      case Failure(e) => Failure(reWrap(e))
    }

    function method Extract(): T
      requires Success?
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E)
  {
    predicate method IsFailure() {
      Fail?
    }
    // Note: PropagateFailure returns a Result, not an Outcome.
    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
    {
      Failure(this.error)
    }
    // Note: no Extract method
  }

  // A helper function to ensure a requirement is true at runtime
  // :- Need(5 == |mySet|, "The set MUST have 5 elements.")
  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
  {
    if condition then Pass else Fail(error)
  }
}
