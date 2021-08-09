// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*********************************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
**********************************************************************************************/

module OptionAndResult {
  
  datatype Option<T, R> = None | Some(value: T) {
    function method to_result(error: R): Result<T, R> 
    {
      match this
      case Some(v) => Success(v)
      case None => Failure(error)
    }
    
    function method unwrap_or(default: T): T 
    {
      match this
      case Some(v) => v
      case None => default
    }
  }
  
  datatype Result<T, R> = | Success(value: T) | Failure(error: R) {
    function method to_option(): Option<T, R> 
    {
      match this
      case Success(s) => Some(s)
      case Failure(e) => None()
    }
    function method unwrap_or(default: T): T 
    {
      match this
      case Success(s) => s
      case Failure(e) => default
    }
  }
  
} 