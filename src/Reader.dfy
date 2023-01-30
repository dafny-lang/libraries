include "Wrappers.dfy"

module {:options "-functionSyntax:4"} Reader {

  datatype Reader<-X,+T> = Reader(f: X -> T)

  function Return<X,T>(t: T): Reader<X,T> {
    Reader(x => t)
  }

  function Map<X,S,T>(f: S -> T): Reader<X,S> -> Reader<X,T> {
    (r: Reader<X,S>) => 
      Reader(x => f((r.f)(x)))
  }

  function Join<X,T>(rr: Reader<X,Reader<X,T>>): Reader<X,T> {
    Reader(x => (rr.f(x)).f(x))
  }

  function Bind<X,S,T>(r: Reader<X,S>, f: S -> Reader<X,T>): Reader<X,T> {
    Reader(x => (f((r.f)(x)).f)(x))
  }

  function Composition<X,S,T,U>(f: S -> Reader<X,T>, g: T -> Reader<X,U>): S -> Reader<X,U> {
    s => Bind(f(s), g)
  }

  ghost function Equal<X(!new),T>(eq: (T, T) -> bool): (Reader<X,T>, Reader<X,T>) -> bool 
  {
    (r1: Reader<X,T>, r2: Reader<X,T>) => forall x: X :: eq(r1.f(x), r2.f(x))
  }

  lemma LemmaUnitalityJoin<X,T>(r: Reader<X,T>)
    requires forall f: X -> T, g: X -> T :: (forall x: X :: f(x) == g(x)) ==> f == g
    ensures Join(Map(Return<X,T>)(r)) == r == Join(Return<X,Reader<X,T>>(r))
  {
  }

  lemma LemmaAssociativityJoin<X,T>(rrr: Reader<X,Reader<X,Reader<X,T>>>) 
    requires forall f: X -> T, g: X -> T :: (forall x: X :: f(x) == g(x)) ==> f == g
    ensures Join(Map(Join<X,T>)(rrr)) == Join(Join<X,Reader<X,T>>(rrr))
  {
  }  

  lemma LemmaLeftUnitalityBind<X,S,T>(s: S, f: S -> Reader<X,T>)
    requires forall f: X -> T, g: X -> T :: (forall x: X :: f(x) == g(x)) ==> f == g
    ensures Bind(Return(s), f) == f(s)
  {
    assert (Bind(Return(s), f)).f == (f(s).f);
  }

  lemma LemmaRightUnitalityBind<X,T>(r: Reader<X,T>)
    requires forall f: X -> T, g: X -> T :: (forall x: X :: f(x) == g(x)) ==> f == g
    ensures Bind(r, Return) == r
  {
  }

  lemma LemmaAssociativityBind<X,S,T,U>(r: Reader<X,S>, f: S -> Reader<X,T>, g: T -> Reader<X,U>)
    requires forall f: X -> U, g: X -> U :: (forall x: X :: f(x) == g(x)) ==> f == g
    ensures Bind(Bind(r, f), g) == Bind(r, Composition(f, g))
  {
  }

}
