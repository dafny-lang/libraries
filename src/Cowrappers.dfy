// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

module {:options "-functionSyntax:4"} Coreader {

  datatype Coreader<+S,+T> = Coreader(left: S, right: T)

  function ExtractRight<S,T>(r: Coreader<S,T>): T {
    r.right
  }

  function ExtractLeft<S,T>(r: Coreader<S,T>): S {
    r.left
  }

  function DuplicateLeft<S,T>(r: Coreader<S,T>): Coreader<S,Coreader<S,T>> {
    Coreader(r.left, r)
  }

  function DuplicateRight<S,T>(r: Coreader<S,T>): Coreader<Coreader<S,T>,T> {
    Coreader(r, r.right)
  }

  function ExtendRight<S,T1,T2>(f: Coreader<S,T1> -> T2, r: Coreader<S,T1>): Coreader<S,T2> {
    Coreader(r.left, f(r))
  }

  function ExtendLeft<S1,S2,T>(f: Coreader<S1,T> -> S2, r: Coreader<S1,T>): Coreader<S2,T> {
    Coreader(f(r), r.right)
  }

  function MapRight<S,T1,T2>(f: T1 -> T2): Coreader<S,T1> -> Coreader<S,T2> {
    (r: Coreader<S,T1>) => 
      Coreader(r.left, f(r.right))
  }

  function MapLeft<S1,S2,T>(f: S1 -> S2): Coreader<S1,T> -> Coreader<S2,T> {
    (r: Coreader<S1,T>) => 
      Coreader(f(r.left), r.right)
  }

  function KleisliCompositionRight<S,T1,T2,T3>(f: Coreader<S,T1> -> T2, g: Coreader<S,T2> -> T3): Coreader<S,T1> -> T3 {
    r => g(ExtendRight(f, r))
  }

  function KleisliCompositionLeft<S1,S2,S3,T>(f: Coreader<S1,T> -> S2, g: Coreader<S2,T> -> S3): Coreader<S1,T> -> S3 {
    r => g(ExtendLeft(f, r))
  }

  ghost function Equal<S,T>(eql: (S, S) -> bool, eqr: (T, T) -> bool): (Coreader<S,T>, Coreader<S,T>) -> bool {
    (r1: Coreader<S,T>, r2: Coreader<S,T>) =>
      eql(r1.left, r2.left) && eqr(r1.right, r2.right)
  }

}