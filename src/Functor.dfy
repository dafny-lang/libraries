// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Functions.dfy"
include "Relations.dfy"

abstract module {:options "-functionSyntax:4"} Functor {
  import opened Functions
  import opened Relations

  /* Structure */
  type W(!new)<T(!new)>

  function Map<S(!new),T(!new)>(f: S -> T): W<S> -> W<T>

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool
    requires EquivalenceRelation(eq)

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool)
    requires EquivalenceRelation(eq)
    ensures EquivalenceRelation(Equal(eq))

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T)
    requires EquivalenceRelation(eq) 
    requires forall x: S :: eq(f(x), g(x))
    ensures forall w: W<S> :: Equal(eq)(Map(f)(w), Map(g)(w))

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Map(Composition(f, g))(w), Composition(Map(f), Map(g))(w))

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T)
    requires EquivalenceRelation(eq) 
    requires forall x: T :: eq(id(x), x)
    ensures forall w: W<T> :: Equal(eq)(Map(id)(w), w)
}