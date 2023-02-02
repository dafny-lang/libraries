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

  /**********************************************************
  *
  *  Assumed structure 
  *
  ***********************************************************/

  /* Functor structure */
  type W(!new)<T>

  function Map<S,T>(f: S -> T): W<S> -> W<T>

  ghost function Equal<T>(eq: (T, T) -> bool): (eq': (W<T>, W<T>) -> bool)
    requires EquivalenceRelation(eq)
    ensures EquivalenceRelation(eq')

  /* Functoriality of Map */
  lemma LemmaMapFunction<S,T>(eq: (T, T) -> bool, f: S -> T, g: S -> T)
    requires EquivalenceRelation(eq) 
    requires forall x: S :: eq(f(x), g(x))
    ensures forall w: W<S> :: Equal(eq)(Map(f)(w), Map(g)(w))

  lemma LemmaMapFunctorial<S,T,U>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Map(Composition(f, g))(w), Composition(Map(f), Map(g))(w))

  lemma LemmaMapIdentity<T>(eq: (T, T) -> bool, id: T -> T)
    requires EquivalenceRelation(eq) 
    requires forall x: T :: eq(id(x), x)
    ensures forall w: W<T> :: Equal(eq)(Map(id)(w), w)

}

abstract module {:options "-functionSyntax:4"} Monad refines Functor {

  /**********************************************************
  *
  *  Assumed structure 
  *
  ***********************************************************/

  /* Monad structure */
  type W(!new)<T>

  function Return<T>(x: T): W<T>

  function Join<T>(ww: W<W<T>>): W<T>

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, x: S)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Map(f)(Return(x)), Return(f(x)))

  lemma LemmaJoinNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Map(f))(ww)), Map(f)(Join(ww)))

  /* Monad laws */
  lemma LemmaUnitalityJoin<T>(eq: (T, T) -> bool, w: W<T>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Return)(w)), w) && Equal(eq)(w, Join(Return(w)))

  lemma LemmaAssociativityJoin<T>(eq: (T, T) -> bool, www: W<W<W<T>>>) 
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Join)(www)), Join(Join(www)))

  /**********************************************************
  *
  *  Derived structure 
  *
  ***********************************************************/

  /* Derived functions */
  function Bind<S,T>(w: W<S>, f: S -> W<T>): W<T> {
    Join(Map(f)(w))
  }

  function KleisliComp<S,T,U>(f: S -> W<T>, g: T -> W<U>): S -> W<U> {
    x => Join(Map(g)(f(x)))
  }

  /* Derived lemmas */
  lemma LemmaLeftUnitalityBind<S,T>(eq: (T, T) -> bool, x: S, f: S -> W<T>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Bind(Return(x), f), f(x))
/*   {
    LemmaReturnNaturality(Equal(eq), f, x);
    LemmaUnitalityJoin(eq, f(x));
  } */

  lemma LemmaRightUnitalityBind<T>(eq: (T, T) -> bool, w: W<T>)
    requires EquivalenceRelation(eq)
    ensures Bind(w, Return) == w
/*   {
    LemmaUnitalityJoin(eq, w);
  } */

  lemma LemmaAssociativityBind<S,T,U>(w: W<S>, f: S -> W<T>, g: T -> W<U>)
    ensures Bind(Bind(w, f), g) == Bind(w, KleisliComp(f, g))
/*   {
    calc {
      Bind(Bind(w, f), g);
    == // Definition of Bind
      Join(Map(g)(Join(Map(f)(w))));
    ==  { LemmaJoinNaturality(g, Map(f)(w)); }
      Join(Join(Map(Map(g))(Map(f)(w))));
    == { LemmaMapFunctorial(f, Map(g), w); }
      Join(Join(Map(x => Map(g)(f(x)))(w)));
    == { LemmaAssociativityJoin(Map(x => Map(g)(f(x)))(w)); }
      Join(Map(Join)(Map(x => Map(g)(f(x)))(w)));
    == // Definition of Composition
      Join(Composition(Map(x => Map(g)(f(x))), Map(Join))(w));
    == {LemmaMapFunctorial(x => Map(g)(f(x)), Join, w);}
      Join(Map(Composition(x => Map(g)(f(x)), Join))(w));
    == { LemmaMapFunction((x, y) => x == y, Composition(x => Map(g)(f(x)), Join), x => Join(Map(g)(f(x)))); }
      Join(Map(x => Join(Map(g)(f(x))))(w));
    == // Definition of Bind, KleisliComp
      Bind(w, KleisliComp(f, g));
    }
  } */

  lemma LemmaAssociativityComposition<S,T,U,V>(f: S -> W<T>, g: T -> W<U>, h: U -> W<V>, x: S)
    ensures KleisliComp(KleisliComp(f, g), h)(x) == KleisliComp(f, KleisliComp(g, h))(x)
/*   {
    calc {
      KleisliComp(KleisliComp(f, g), h)(x);
    == // Definition of KleisliComp
      Join(Map(h)(Join(Map(g)(f(x)))));
    == { LemmaJoinNaturality(h, Map(g)(f(x))); }
      Join(Join(Map(Map(h))(Map(g)(f(x)))));
    == // Definition of Composition
      Join(Join(Composition(Map(g), Map(Map(h)))(f(x))));
    == { LemmaMapFunctorial(g, Map(h), f(x)); }
      Join(Join(Map(Composition(g, Map(h)))(f(x))));
    == { LemmaAssociativityJoin(Map(Composition(g, Map(h)))(f(x))); }
      Join(Map(Join)(Map(Composition(g, Map(h)))(f(x))) ); 
    == { LemmaMapFunctorial(Composition(g, Map(h)), Join, f(x)); }
      Join(Map(Composition(Composition(g, Map(h)), Join))(f(x)));
    == { LemmaMapFunction((x, y) => x == y, Composition(Composition(g, Map(h)), Join), y => Join(Map(h)(g(y)))); }
      Join(Map(y => Join(Map(h)(g(y))))(f(x)));
    == // Definition of KleisliComp
      KleisliComp(f, KleisliComp(g, h))(x);
    }
  } */

  lemma LemmaIdentityReturn<S,T>(eq: (T, T) -> bool, f: S -> W<T>, x: S)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(KleisliComp(f, Return)(x), f(x)) &&  Equal(eq)(f(x), KleisliComp(Return, f)(x))
/*   {
    calc {
      KleisliComp(f, Return)(x);
    == // Definition of Composition
      Join(Map(Return)(f(x)));
    == { LemmaUnitalityJoin(f(x)); }
      f(x);
    }
    calc {
      f(x);
    == { LemmaUnitalityJoin(f(x)); }
      Join(Return(f(x)));
    == { LemmaReturnNaturality(f, x); }
      Join(Map(f)(Return(x)));
    == // Definition of Composition
      KleisliComp(Return, f)(x);
    }
  } */
}

abstract module {:options "-functionSyntax:4"} Result refines Monad {

  /**********************************************************
  *
  *  Monad
  *
  ***********************************************************/
  
  type E

  function eqe(e1: E, e2: E): bool

  lemma {:axiom} LemmaEquivRel()
    ensures EquivalenceRelation(eqe)

  /* Monad structure */

  datatype W<T> = Success(value: T) | Failure(error: E)

  function Map<S,T>(f: S -> T): W<S> -> W<T> {
    (w: W<S>) =>
      match w 
      case Success(v) => W<T>.Success(f(v))
      case Failure(e) => W<T>.Failure(e)
  }



  ghost function Equal<T>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool
  {
    (w1: W<T>, w2: W<T>) =>
      match (w1, w2)
      case (Success(v1), Success(v2)) => eq(v1, v2)
      case (Failure(e1), Failure(e2)) => eqe(e1, e2)
      case _ => false
  }

  lemma LemmaEquivRelLift<T>(eq: (T, T) -> bool)
    requires EquivalenceRelation(eq)
    ensures EquivalenceRelation(Equal(eq))
  {
    assert Reflexive(Equal(eq)) by {
      
    }
  }


  function Return<T>(x: T): W<T> {
    Success(x)
  }
 
  function Join<T>(ww: W<W<T>>): W<T> {
    match ww
    case Success(v) => v
    case Failure(e) => W<T>.Failure(e)
  }

  /* Functoriality of Map */
  lemma LemmaMapFunction<S,T>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {}

  lemma LemmaMapFunctorial<S,T,U>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {}

  lemma LemmaMapIdentity<T>(eq: (T, T) -> bool, id: T -> T) {}

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, x: S) {}

  lemma LemmaJoinNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {}

  /* Monad laws */
  lemma LemmaUnitalityJoin<T>(eq: (T, T) -> bool, w: W<T>) {}

  lemma LemmaAssociativityJoin<T>(eq: (T, T) -> bool, www: W<W<W<T>>>) {}

  /**********************************************************
  *
  *  Wrapper
  *
  ***********************************************************/

  /* Get and Set */
  function Failure<T>(e: E): W<T> {
    W.Failure(e)
  } 

  predicate IsSuccess<T>(w: W<T>) {
    w.Success?
  }  

  predicate IsFailure<T>(w: W<T>) {
    w.Failure?
  }  

  function GetValue<T>(w: W<T>): T
    requires w.Success?
  {
    w.value
  }

  function GetValueDefault<T,E>(w: W<T>, default: T): T {
    match w 
    case Success(v) => v
    case Failure(_) => default
  }

  function GetError<T>(w: W<T>): E 
    requires w.Failure?
  {
    w.error
  }

  /* Fold */
  function Fold<T,U>(f: T -> U, g: E -> U): W<T> -> U {
    (w: W<T>) =>
      match w 
      case Success(v) => f(v)
      case Failure(e) => g(e)
  }

  /* Conversion to other types */
  function ToSeq<T>(w: W<T>): seq<T> {
    match w
    case Success(v) => [v]
    case Failure(_) => []
  }

  function ToSet<T>(w: W<T>): set<T> {
    match w
    case Success(v) => {v}
    case Failure(_) => {}   
  }

  // function ToOption<T>(w: W<T>): Option<T> {
  //   match w
  //   case Success(v) => Some(v)
  //   case Failure(_) => None()
  // }

}

module {:options "-functionSyntax:4"} Option refines Monad {

  /**********************************************************
  *
  *  Monad
  *
  ***********************************************************/
 
  /* Monad structure */
  datatype W<T> = None | Some(value: T)

  function Map<S,T>(f: S -> T): W<S> -> W<T>
  {
    (w: W<S>) =>
      match w 
      case None => W<T>.None
      case Some(v) => W<T>.Some(f(v))
  }

  ghost function Equal<T>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    (w1: W<T>, w2: W<T>) =>
      match (w1, w2)
      case (Some(v1), Some(v2)) => eq(v1, v2)
      case (None, None) => true
      case _ => false
  }

  function Return<T>(x: T): W<T> {
    Some(x)
  }

  function Join<T>(ww: W<W<T>>): W<T> {
    match ww
    case None => None
    case Some(w) => w
  }

  /* Functoriality of Map */
  lemma LemmaMapFunction<S,T>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {}

  lemma LemmaMapFunctorial<S,T,U>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {}

  lemma LemmaMapIdentity<T>(eq: (T, T) -> bool, id: T -> T) {}

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, x: S) {}

  lemma LemmaJoinNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {}

  /* Monad laws */
  lemma LemmaUnitalityJoin<T>(eq: (T, T) -> bool, w: W<T>) {}

  lemma LemmaAssociativityJoin<T>(eq: (T, T) -> bool, www: W<W<W<T>>>) {}

  /**********************************************************
  *
  *  Wrapper
  *
  ***********************************************************/

  /* Get and Fold */
  function GetValueDefault<T>(w: W<T>, default: T): T {
    match w
    case None => default
    case Some(v) => v
  }

  function GetValue<T>(w: W<T>): T
    requires w.Some?
  {
    w.value
  }

  function Fold<T,U>(u: U, f: T -> U): W<T> -> U {
    (w: W<T>) =>
      match w 
      case None => u
      case Some(v) => f(v)
  }

  /* Conversion to other types */
  // function ToResult<T>(e: E): Option<T> -> Result<T,E> {
  //   (o: Option<T>) =>
  //     match o 
  //     case Some(v) => Success(v)
  //     case None => Failure(e)
  // }

  function ToSeq<T>(w: W<T>): seq<T> {
    match w 
    case None => []
    case Some(v) => [v]
  }

  function ToSet<T>(w: W<T>): set<T> {
    match w
    case None => {}
    case Some(v) => {v}
  }

  /* Comparison */
  function Compare<T>(cmp: (T, T) -> int): (W<T>, W<T>) -> int {
    (w1: W<T>, w2: W<T>) =>
      match (w1, w2)
      case (Some(v1), Some(v2)) => cmp(v1, v2)
      case (None, None) => 0
      case (None, Some(_)) => -1
      case (Some(_), None) => 1
  }

}

module {:options "-functionSyntax:4"} Writer refines Monad {

  /**********************************************************
  *
  *  Monad
  *
  ***********************************************************/
 
  /* Monad structure */
  datatype W<T> = Result(value: T, log: string)

  function Map<S,T>(f: S -> T): W<S> -> W<T> {
    (w: W<S>) => W<T>.Result(f(w.value), w.log)
  }

  ghost function Equal<T>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    (w1: W<T>, w2: W<T>) => eq(w1.value, w2.value) && w1.log == w2.log
  }

  function Return<T>(x: T): W<T> {
    Result(x, "")
  }

  function Join<T>(ww: W<W<T>>): W<T> {
    Result((ww.value).value, (ww.value).log + ww.log)
  }

  /* Functoriality of Map */
  lemma LemmaMapFunction<S,T>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {}

  lemma LemmaMapFunctorial<S,T,U>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {}

  lemma LemmaMapIdentity<T>(eq: (T, T) -> bool, id: T -> T) {}

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, x: S) {}

  lemma LemmaJoinNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {}

  /* Monad laws */
  lemma LemmaUnitalityJoin<T>(eq: (T, T) -> bool, w: W<T>) {}

  lemma LemmaAssociativityJoin<T>(eq: (T, T) -> bool, www: W<W<W<T>>>) {}

  /**********************************************************
  *
  *  Wrapper
  *
  ***********************************************************/

  /* Get and Set */
  function GetValue<T>(w: W<T>): T {
    w.value
  }

  function GetLog<T>(w: W<T>): string {
    w.log
  }

  function Result<T>(v: T, s: string): W<T> {
    W<T>.Result(v, s)
  }
}

abstract module {:options "-functionSyntax:4"} Reader refines Monad {

  /**********************************************************
  *
  *  Monad
  *
  ***********************************************************/

  type A(!new)

  datatype W<T> = Reader(f: A -> T)

  function Map<S,T>(f: S -> T): W<S> -> W<T> {
    (w: W<S>) => Reader(a => f((w.f)(a)))
  }

  ghost function Equal<T>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    (w1: W<T>, w2: W<T>) =>
      forall a: A :: eq(w1.f(a), w2.f(a))
  }

  function Return<T>(x: T): W<T> {
    Reader(a => x)
  }

  function Join<T>(ww: W<W<T>>): W<T>{
    Reader(a => (ww.f(a)).f(a))
  }

  /* Functoriality of Map */
  lemma LemmaMapFunction<S,T>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {}

  lemma LemmaMapFunctorial<S,T,U>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {}

  lemma LemmaMapIdentity<T>(eq: (T, T) -> bool, id: T -> T) {}

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, x: S) {}

  lemma LemmaJoinNaturality<S,T>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {}

  /* Monad laws */
  lemma LemmaUnitalityJoin<T>(eq: (T, T) -> bool, w: W<T>) {}

  lemma LemmaAssociativityJoin<T>(eq: (T, T) -> bool, www: W<W<W<T>>>) {}

}

