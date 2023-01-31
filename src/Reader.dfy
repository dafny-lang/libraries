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
    ensures forall x: X :: Join(Map(Return<X,T>)(r)).f(x) == r.f(x) == Join(Return<X,Reader<X,T>>(r)).f(x)
  {
  }

  lemma LemmaAssociativityJoin<X,T>(rrr: Reader<X,Reader<X,Reader<X,T>>>) 
    ensures forall x: X :: Join(Map(Join<X,T>)(rrr)).f(x) == Join(Join<X,Reader<X,T>>(rrr)).f(x)
  {
  }  

  lemma LemmaLeftUnitalityBind<X,S,T>(s: S, f: S -> Reader<X,T>)
    ensures forall x: X :: Bind(Return(s), f).f(x) == f(s).f(x)
  {
  }

  lemma LemmaRightUnitalityBind<X,T>(r: Reader<X,T>)
    ensures forall x: X :: Bind(r, Return).f(x) == r.f(x)
  {
  }

  lemma LemmaAssociativityBind<X,S,T,U>(r: Reader<X,S>, f: S -> Reader<X,T>, g: T -> Reader<X,U>)
    ensures forall x: X :: Bind(Bind(r, f), g).f(x) == Bind(r, Composition(f, g)).f(x)
  {
  }

  lemma LemmaAssociativityComposition<X,S,T,U,V>(f: S -> Reader<X,T>, g: T -> Reader<X,U>, h: U -> Reader<X,V>)
    ensures forall s: S, x: X :: Composition(Composition(f, g),h)(s).f(x) == Composition(f, Composition(g,h))(s).f(x)
  {
  }

  lemma LemmaIdentityReturn<X,S,T>(f: S -> Reader<X,T>)
    ensures forall s: S, x: X :: Composition(f, Return<X,T>)(s).f(x) == f(s).f(x) == Composition(Return<X,S>, f)(s).f(x)
  {
  }
}
