// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Wrappers.dfy"

module {:options "-functionSyntax:4"} Either {

  import opened Wrappers 

  datatype Either<+S,+T> = Left(left: S) | Right(right: T) 

  /**********************************************************
  *
  *  Get and set
  *
  ***********************************************************/

  function Left<S,T>(v: S): Either<S,T> {
    Either.Left(v)
  }

  function Right<S,T>(v: T): Either<S,T> {
    Either.Right(v)
  }

  predicate IsLeft<S,T>(e: Either<S,T>) {
    e.Left?
  }

  predicate IsRight<S,T>(e: Either<S,T>) {
    e.Right?
  }

  /**********************************************************
  *
  *  Conversion to other datatypes
  *
  ***********************************************************/

  function FindLeft<S,T>(e: Either<S,T>): Option<S> {
    match e 
    case Left(v) => Some(v)
    case Right(v) => None
  }

  function FindRight<S,T>(e: Either<S,T>): Option<T> {
    match e 
    case Left(v) => None
    case Right(v) => Some(v)
  }

  /**********************************************************
  *
  *  Map
  *
  ***********************************************************/

  function MapLeft<S,T,U>(f: S -> T): Either<S,U> -> Either<T,U> {
    (e: Either<S,U>) =>
     match e 
     case Left(v) => Either<T,U>.Left(f(v))
     case Right(v) => Either<T,U>.Right(v)
  }

  function MapRight<S,T,U>(f: T -> U): Either<S,T> -> Either<S,U> {
    (e: Either<S,T>) =>
     match e 
     case Left(v) => Either<S,U>.Left(v)
     case Right(v) => Either<S,U>.Right(f(v))
  }

  function Map<S1,S2,T1,T2>(f: S1 -> S2, g: T1 -> T2): Either<S1,T1> -> Either<S2,T2> {
    (e: Either<S1,T1>) =>
      match e
      case Left(v) => Either<S2,T2>.Left(f(v))
      case Right(v) => Either<S2,T2>.Right(g(v))
  }

  /**********************************************************
  *
  *  Fold
  *
  ***********************************************************/

  function Fold<S,T,U>(f: S -> U, g: T -> U): Either<S,T> -> U {
    (e: Either<S,T>) =>
      match e
      case Left(v) => f(v)
      case Right(v) => g(v)
  }

  /**********************************************************
  *
  *  Comparison
  *
  ***********************************************************/

  function Equal<S,T>(eql: (S, S) -> bool, eqr: (T, T) -> bool): (Either<S,T>, Either<S,T>) -> bool {
    (e1: Either<S,T>, e2: Either<S,T>) =>
      match (e1, e2)
      case (Left(v1), Left(v2)) => eql(v1, v2)
      case (Right(v1), Right(v2)) => eqr(v1, v2)
      case _ => false
  }

  function Compare<S,T>(cmpl: (S, S) -> int, cmpr: (T, T) -> int): (Either<S,T>, Either<S,T>) -> int {
    (e1: Either<S,T>, e2: Either<S,T>) =>
      match (e1, e2)
      case (Left(v1), Left(v2)) => cmpl(v1, v2)
      case (Right(v1), Right(v2)) => cmpr(v1, v2)
      case (Left(_), Right(_)) => -1
      case (Right(_), Left(_)) => 1
  }

}

