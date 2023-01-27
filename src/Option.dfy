// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/
include "Wrappers.dfy"

module {:options "-functionSyntax:4"} Option {

  import opened Wrappers

  datatype Option<+T> = None | Some(value: T)

  function Some<T>(v: T): Option<T> {
    Option.Some(v)
  }

  function Bind<S,T>(o: Option<S>, f: S -> Option<T>): Option<T> {
    match o 
    case None => Option<T>.None
    case Some(v) => f(v)
  }

  predicate IsNone<T>(o: Option<T>) {
    o.None?
  }

  predicate IsSome<T>(o: Option<T>) {
    o.Some?
  }

  function GetValue<T>(o: Option<T>): T
    requires o.Some?
  {
    o.value
  }

  function GetValueDefault<T>(o: Option<T>, default: T): T {
    match o
    case None => default
    case Some(v) => v
  }

  function Join<T>(oo: Option<Option<T>>): Option<T> {
    match oo
    case None => Option<T>.None
    case Some(o) => o
  }

  function Map<S,T>(f: S -> T): Option<S> -> Option<T>
  {
    (o: Option<S>) =>
      match o 
      case None => Option<T>.None
      case Some(v) => Some(f(v))
  }

  function Fold<T,U>(u: U, f: T -> U): Option<T> -> U {
    (o: Option<T>) =>
      match o 
      case None => u
      case Some(v) => f(v)
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

  function Composition<S,T,U>(f: S -> Option<T>, g: T-> Option<U>): S -> Option<U> {
    x => Bind(f(x), g)
  }

  function ToResult<T,E>(e: E): Option<T> -> Result<T,E> {
    (o: Option<T>) =>
      match o 
      case Some(v) => Success(v)
      case None => Failure(e)
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

  lemma LemmaUnitalityJoin<T>(o: Option<T>)
    ensures Join(Map(Some<T>)(o)) == o == Join(Some<Option<T>>(o))
  {
  }

  lemma LemmaAssociativityJoin<T>(ooo: Option<Option<Option<T>>>) 
    ensures Join(Map(Join<T>)(ooo)) == Join(Join<Option<T>>(ooo))
  {
  }  

  lemma LemmaLeftUnitalityBind<S,T>(v: S, f: S -> Option<T>)
    ensures Bind(Some(v), f) == f(v)
  {
  }

  lemma LemmaRightUnitalityBind<T>(o: Option<T>)
    ensures Bind(o, Some) == o
  {
  }

  lemma LemmaAssociativityBind<S,T,U>(o: Option<S>, f: S -> Option<T>, g: T -> Option<U>)
    ensures Bind(Bind(o, f), g) == Bind(o, Composition(f, g))
  {
  }






}
