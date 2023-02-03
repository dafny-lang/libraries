// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Functor.dfy"
include "Wrappers.dfy"

abstract module {:options "-functionSyntax:4"} Monad refines Functor {
  /* Structure  */
  type F(!new)<T(!new)>

  function Return<T(!new)>(x: T): F<T>

  function Join<T(!new)>(ww: F<F<T>>): F<T>

  /* Naturality */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Map(f)(Return(x)), Return(f(x)))

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: F<F<S>>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Map(f))(ww)), Map(f)(Join(ww)))

  /* Unitality and Associativity */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: F<T>)
    requires EquivalenceRelation(eq)
    ensures Equal(eq)(Join(Map(Return)(w)), w) && Equal(eq)(w, Join(Return(w)))

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: F<F<F<T>>>) 
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
  type F(!new)<T(!new)> = Result.Result<T,E>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Result.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
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

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): F<T> {
    Result.Return(x)
  }

  function Join<T(!new)>(ww: F<F<T>>): F<T> {
    Result.Join(ww)
  }

  /* Naturality */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: F<F<S>>) {
    LemmaEquiv();
  }

  /* Unitality and Associativity */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
    LemmaEquiv();
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: F<F<F<T>>>) {
    LemmaEquiv();
  }
}


module {:options "-functionSyntax:4"} WriterMonad refines Monad {
  import Writer 

  /* Functor structure */
  type F(!new)<T(!new)> = Writer.Writer<T>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Writer.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
    Writer.Equal(eq)
  }    

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): F<T> {
    Writer.Return(x)
  }

  function Join<T(!new)>(ww: F<F<T>>): F<T> {
    Writer.Join(ww)
  }

  /* Naturality */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: F<F<S>>) {
  }

  /* Unitality and Associativity */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: F<F<F<T>>>) {
  }
}


module {:options "-functionSyntax:4"} OptionMonad refines Monad {
  import Option

  /* Functor structure */
  type F(!new)<T(!new)> = Option.Option<T>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Option.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
    Option.Equal(eq)
  }    

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
  }

  /* Properties of Map */
  lemma LemmaMapFunction<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, g: S -> T) {
  }

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): F<T> {
    Option.Return(x)
  }

  function Join<T(!new)>(ww: F<F<T>>): F<T> {
    Option.Join(ww)
  }

  /* Naturality */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: F<F<S>>) {
  }

  /* Unitality and Associativity */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: F<F<F<T>>>) {
  }
}


abstract module {:options "-functionSyntax:4"} EitherRightMonad refines Monad {
  import Either 

  type X(!new)

  function eql(x: X, y: X): bool

  lemma LemmaEquiv()
    ensures EquivalenceRelation(eql)

  /* Functor structure */
  type F(!new)<T(!new)> = Either.Either<X,T>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Either.MapRight(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
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

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): F<T> {
    Either.ReturnRight(x)
  }

  function Join<T(!new)>(ww: F<F<T>>): F<T> {
    Either.JoinRight(ww)
  }

  /* Naturality */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: F<F<S>>) {
    LemmaEquiv();
  }

  /* Unitality and Associativity */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
    LemmaEquiv();
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: F<F<F<T>>>) {
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
  type F(!new)<T(!new)> = Either.Either<T,X>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Either.MapLeft(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
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

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
    LemmaEquiv();
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
    LemmaEquiv();
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): F<T> {
    Either.ReturnLeft(x)
  }

  function Join<T(!new)>(ww: F<F<T>>): F<T> {
    Either.JoinLeft(ww)
  }

  /* Naturality */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: F<F<S>>) {
    LemmaEquiv();
  }

  /* Unitality and Associativity */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
    LemmaEquiv();
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: F<F<F<T>>>) {
    LemmaEquiv();
  }
}


abstract module {:options "-functionSyntax:4"} ReaderMonad refines Monad {
  import Reader

  type X(!new)

  /* Functor structure */
  type F(!new)<T(!new)> = Reader.Reader<X,T>

  function Map<S(!new),T(!new)>(f: S -> T): F<S> -> F<T> {
    Reader.Map(f)
  }

  ghost function Equal<T(!new)>(eq: (T, T) -> bool): (F<T>, F<T>) -> bool {
    Reader.Equal(eq)
  }    

  /* Properties of Equal */
  lemma LemmaEquivRelLift<T(!new)>(eq: (T, T) -> bool) {
    forall w: F<T> ensures Equal(eq)(w, w) {
      forall x: X ensures eq(w.f(x), w.f(x)) {
        assert eq(w.f(x), w.f(x));
      }
    }
    assert Reflexive(Equal(eq));

    forall v, w: F<T> ensures Equal(eq)(v, w) <==> Equal(eq)(w, v) {
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

    forall v, w, u: F<T> ensures Equal(eq)(v, w) && Equal(eq)(w, u) ==> Equal(eq)(v, u) {
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

  lemma LemmaMapFunctorial<S(!new),T(!new),U(!new)>(eq: (U, U) -> bool, f: S -> T, g: T -> U, w: F<S>) {
  }

  lemma LemmaMapIdentity<T(!new)>(eq: (T, T) -> bool, id: T -> T) {
  }

  /* Monad structure */
  function Return<T(!new)>(x: T): F<T> {
    Reader.Return(x)
  }

  function Join<T(!new)>(ww: F<F<T>>): F<T> {
    Reader.Join(ww)
  }

  /* Naturality */
  lemma LemmaReturnNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, x: S) {
  }

  lemma LemmaJoinNaturality<S(!new),T(!new)>(eq: (T, T) -> bool, f: S -> T, ww: F<F<S>>) {
  }

  /* Unitality and Associativity */
  lemma LemmaUnitalityJoin<T(!new)>(eq: (T, T) -> bool, w: F<T>) {
  }

  lemma LemmaAssociativityJoin<T(!new)>(eq: (T, T) -> bool, www: F<F<F<T>>>) {
  }
}





