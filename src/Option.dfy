// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module {:options "-functionSyntax:4"} Option {

  datatype Option<+T> = None | Some(value: T)

  function Some<T>(v: T): Option<T> {
    Option.Some(v)
  }

  function Bind<S,T>(o: Option<S>, f: S -> Option<T>): Option<T> {
    match o 
    case None => None
    case Some(v) => f(v)
  }

  predicate IsNone<T>(o: Option<T>) {
    o.None?
  }

  predicate IsSome<T>(o: Option<T>) {
    o.Some?
  }

  function Get<T>(o: Option<T>): (v: T) 
    requires o.Some?
    ensures o.value == v
  {
    o.value
  }
 
  function Join<T>(oo: Option<Option<T>>): Option<T> {
    match oo
    case None => None
    case Some(o) => o
  }

  function Map<S,T>(f: S -> T, o: Option<S>): (o2: Option<T>)
  {
    match o 
    case None => None
    case Some(v) => Some(f(v))
  }

  function Equal<T>(eq: (T, T) -> bool): (Option<T>, Option<T>) -> bool {
    (o1: Option<T>, o2: Option<T>) =>
      match (o1, o2)
      case (Some(v1), Some(v2)) => eq(v1, v2)
      case (None, None) => true
      case _ => false
  }
  
  function Compare<T>(cmp: (T, T) -> int): (Option<T>, Option<T>) -> int {
    (o1: Option<T>, o2: Option<T>) =>
      match (o1, o2)
      case (Some(v1), Some(v2)) => cmp(v1, v2)
      case (None, None) => 0
      case (None, Some(_)) => -1
      case (Some(_), None) => 1
  }

  function ToSeq<T>(o: Option<T>): seq<T> {
    match o 
    case None => []
    case Some(v) => [v]
  }

  function ToSet<T>(o: Option<T>): set<T> {
    match o
    case None => {}
    case Some(v) => {v}
  }

}
