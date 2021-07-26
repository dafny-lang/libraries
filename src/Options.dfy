// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*********************************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
**********************************************************************************************/

module Options {
  
  datatype Option<T> = None | Some(value: T) {
    function method to_result(): Result<T> 
    {
      match this
      case Some(v) => Success(v)
      case None() => Failure("Option is None")
    }
    
    function method unwrap_or(default: T): T 
    {
      match this
      case Some(v) => v
      case None => default
    }
  }
  
  datatype Result<T> = | Success(value: T) | Failure(error: string) {
    function method to_option(): Option<T> 
    {
      match this
      case Success(s) => Some(s)
      case Failure(e) => None()
    }
    function method unwrap_pr(default: T): T 
    {
      match this
      case Success(s) => s
      case Failure(e) => default
    }
  }
  
} 