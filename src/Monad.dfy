// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Functor.dfy"
include "Wrappers.dfy"

abstract module {:options "-functionSyntax:4"} Monad refines Functor {
  /* Structure  */
  type W(!new)<T(!new)>

  function Return<T(!new)>(x: T): W<T>

  function Join<T(!new)>(ww: W<W<T>>): W<T>

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Map(f)(Return(x)), Return(f(x)))

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Map(f))(ww)), Map(f)(Join(ww)))

  /* Monad laws */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: W<T>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Return)(w)), w) && Equal(eq)(w, Join(Return(w)))

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: W<W<W<T>>>) 
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Join)(www)), Join(Join(www)))
}


abstract module {:options "-functionSyntax:4"} ResultMonad refines Monad {
  import Result
    
  type E(!new)

  function eqe(x: E, y: E): bool

  lemma LemmaEquiv()
    ensures EquivalenceRelation(eqe)

  /* Functor structure */
  type W(!new)<T(!new)> = Result.Result<T,E>

  function Map<S(!new),T(!new)>(f: S -> T): W<S> -> W<T> {
    Result.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    Result.Equal(eq, eqe)
  }    

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
    LemmaEquiv();
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
    LemmaEquiv();
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): W<T> {
    Result.Return(x)
  }

  function Join<T(!new)>(ww: W<W<T>>): W<T> {
    Result.Join(ww)
  }

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {
    LemmaEquiv();
  }

  /* Monad laws */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: W<T>) {
    LemmaEquiv();
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: W<W<W<T>>>) {
    LemmaEquiv();
  }
}


module {:options "-functionSyntax:4"} WriterMonad refines Monad {
  import Writer 

  /* Functor structure */
  type W(!new)<T(!new)> = Writer.Writer<T>

  function Map<S(!new),T(!new)>(f: S -> T): W<S> -> W<T> {
    Writer.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    Writer.Equal(eq)
  }    

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): W<T> {
    Writer.Return(x)
  }

  function Join<T(!new)>(ww: W<W<T>>): W<T> {
    Writer.Join(ww)
  }

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {
  }

  /* Monad laws */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: W<T>) {
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: W<W<W<T>>>) {
  }
}


module {:options "-functionSyntax:4"} OptionMonad refines Monad {
  import Option

  /* Functor structure */
  type W(!new)<T(!new)> = Option.Option<T>

  function Map<S(!new),T(!new)>(f: S -> T): W<S> -> W<T> {
    Option.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    Option.Equal(eq)
  }    

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): W<T> {
    Option.Return(x)
  }

  function Join<T(!new)>(ww: W<W<T>>): W<T> {
    Option.Join(ww)
  }

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {
  }

  /* Monad laws */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: W<T>) {
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: W<W<W<T>>>) {
  }
}


abstract module {:options "-functionSyntax:4"} EitherRightMonad refines Monad {
  import Either 

  type X(!new)

  function eql(x: X, y: X): bool

  lemma LemmaEquiv()
    ensures EquivalenceRelation(eql)

  /* Functor structure */
  type W(!new)<T(!new)> = Either.Either<X,T>

  function Map<S(!new),T(!new)>(f: S -> T): W<S> -> W<T> {
    Either.MapRight(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    Either.Equal(eql, eq)
  }  

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
    LemmaEquiv();
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
    LemmaEquiv();
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): W<T> {
    Either.ReturnRight(x)
  }

  function Join<T(!new)>(ww: W<W<T>>): W<T> {
    Either.JoinRight(ww)
  }

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {
    LemmaEquiv();
  }

  /* Monad laws */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: W<T>) {
    LemmaEquiv();
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: W<W<W<T>>>) {
    LemmaEquiv();
  }
}


abstract module {:options "-functionSyntax:4"} EitherLeftMonad refines Monad {
  import Either 

  type X(!new)

  function eqr(x: X, y: X): bool

  lemma LemmaEquiv()
    ensures EquivalenceRelation(eqr)

  /* Functor structure */
  type W(!new)<T(!new)> = Either.Either<T,X>

  function Map<S(!new),T(!new)>(f: S -> T): W<S> -> W<T> {
    Either.MapLeft(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    Either.Equal(eq, eqr)
  }  

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
    LemmaEquiv();
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
    LemmaEquiv();
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): W<T> {
    Either.ReturnLeft(x)
  }

  function Join<T(!new)>(ww: W<W<T>>): W<T> {
    Either.JoinLeft(ww)
  }

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {
    LemmaEquiv();
  }

  /* Monad laws */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: W<T>) {
    LemmaEquiv();
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: W<W<W<T>>>) {
    LemmaEquiv();
  }
}


abstract module {:options "-functionSyntax:4"} ReaderMonad refines Monad {
  import Reader

  type X(!new)

  /* Functor structure */
  type W(!new)<T(!new)> = Reader.Reader<X,T>

  function Map<S(!new),T(!new)>(f: S -> T): W<S> -> W<T> {
    Reader.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (W<T>, W<T>) -> bool {
    Reader.Equal(eq)
  }    

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
    forall w: W<T> ensures Equal(eq)(w, w) {
      forall x: X ensures eq(w.f(x), w.f(x)) {
        assert eq(w.f(x), w.f(x));
      }
    }
    assert Reflexive(Equal(eq));

    forall v, w: W<T> ensures Equal(eq)(v, w) <==> Equal(eq)(w, v) {
      calc {
        Equal(eq)(v, w);
        <==>
        forall x: X :: eq(v.f(x), w.f(x));
        <==> { assert Symmetric(eq); }
        forall x: X :: eq(v.f(x), w.f(x));
        <==>
        Equal(eq)(w, v);
      }
    }
    assert Symmetric(Equal(eq));

    forall v, w, u: W<T> ensures Equal(eq)(v, w) && Equal(eq)(w, u) ==> Equal(eq)(v, u) {
      if Equal(eq)(v, w) && Equal(eq)(w, u) {
        forall x: X ensures eq(v.f(x), u.f(x)) {
          calc {
            eq(v.f(x), w.f(x)) && eq(w.f(x), u.f(x));
          ==> { assert Transitive(eq); }
            eq(v.f(x), u.f(x));
          }
        }
      }
    }
    assert Transitive(Equal(eq));
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: W<S>) {
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): W<T> {
    Reader.Return(x)
  }

  function Join<T(!new)>(ww: W<W<T>>): W<T> {
    Reader.Join(ww)
  }

  /* Naturality of Return and Join */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: W<W<S>>) {
  }

  /* Monad laws */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: W<T>) {
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: W<W<W<T>>>) {
  }
}





