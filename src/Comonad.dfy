// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Functor.dfy"
include "Cowrappers.dfy"

abstract module {:options "-functionSyntax:4"} Comonad refines Functor {
  /* Structure  */
  type F(!new)<T(!new)>

  function Extract<T(!new)>(w: F<T>): T

  function Duplicate<T(!new)>(w: F<T>): F<F<T>>

  /* Naturality */
  lemma LemmaExtractNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, w: F<S>)
    requires EquivalenceRelation(eq)
    ensures eq(f(Extract(w)), Extract(Map(f)(w)))

  lemma LemmaDuplicateNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, w: F<S>)
    requires EquivalenceRelation(eq)
    ensures EquivalenceRelation(Equal(eq))
    ensures Equal(Equal(eq))(Duplicate(Map(f)(w)), Map(Map(f))(Duplicate(w)))

  /* Counitality and Coassociativity */
  lemma LemmaCoUnitalityExtract<T(!new)>(eq: (T, T) -> bool, w: F<T>)
    requires EquivalenceRelation(eq)
    ensures && Equal(eq)(Map(Extract)(Duplicate(w)), w)
            && Equal(eq)(w, Extract(Duplicate(w)))
 
  lemma LemmaCoAssociativityDuplicate<T(!new)>(eq: (T, T) -> bool, w: F<T>) 
    requires && EquivalenceRelation(eq)
             && EquivalenceRelation(Equal(eq))
             && EquivalenceRelation(Equal(Equal(eq))) 
    ensures Equal(Equal(Equal(eq)))(Map(Duplicate)(Duplicate(w)), Duplicate(Duplicate(w)))
}

abstract module {:options "-functionSyntax:4"} CoreaderRightComonad refines Comonad {
  import Coreader

  type X(!new)

  function eql(x: X, y: X): bool

  lemma LemmaEquiv()
    ensures EquivalenceRelation(eql)

  /* Functor structure */
  type F(!new)<T(!new)> = Coreader.Coreader<X,T>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Coreader.MapRight(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
    Coreader.Equal(eql, eq)
  }  

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
    LemmaEquiv();
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
    LemmaEquiv();
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Comonad structure */
  function Extract<T(!new)>(w: F<T>): T {
    Coreader.ExtractRight(w)
  } 

  function Duplicate<T(!new)>(w: F<T>): F<F<T>> {
    Coreader.DuplicateLeft(w)
  }

  /* Naturality */
  lemma LemmaExtractNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, w: F<S>) {
  }

  lemma LemmaDuplicateNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, w: F<S>) {
    LemmaEquiv();
  }

  /* Counitality and Coassociativity */
  lemma LemmaCoUnitalityExtract<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
    LemmaEquiv();
  }
 
  lemma LemmaCoAssociativityDuplicate<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
    LemmaEquiv();
  }
}

abstract module {:options "-functionSyntax:4"} CoreaderLeftComonad refines Comonad {
  import Coreader

  type X(!new)

  function eqr(x: X, y: X): bool

  lemma LemmaEquiv()
    ensures EquivalenceRelation(eqr)

  /* Functor structure */
  type F(!new)<T(!new)> = Coreader.Coreader<T,X>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Coreader.MapLeft(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
    Coreader.Equal(eq, eqr)
  }  

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
    LemmaEquiv();
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
    LemmaEquiv();
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Comonad structure */
  function Extract<T(!new)>(w: F<T>): T {
    Coreader.ExtractLeft(w)
  } 

  function Duplicate<T(!new)>(w: F<T>): F<F<T>> {
    Coreader.DuplicateRight(w)
  }

  /* Naturality */
  lemma LemmaExtractNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, w: F<S>) {
  }

  lemma LemmaDuplicateNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, w: F<S>) {
    LemmaEquiv();
  }

  /* Counitality and Coassociativity */
  lemma LemmaCoUnitalityExtract<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
    LemmaEquiv();
  }
 
  lemma LemmaCoAssociativityDuplicate<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
    LemmaEquiv();
  }
}