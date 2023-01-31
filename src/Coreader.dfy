include "Wrappers.dfy"

module {:options "-functionSyntax:4"} Coreader {

  datatype Coreader<+X,+T> = Coreader(left: X, right: T)

  function Extract<X,T>(r: Coreader<X,T>): T {
    r.right
  }

  function Duplicate<X,T>(r: Coreader<X,T>): Coreader<X,Coreader<X,T>> {
    Coreader(r.left, r)
  }

  function Extend<X,S,T>(f: Coreader<X,S> -> T, r: Coreader<X,S>): Coreader<X,T> {
    Coreader(r.left, f(r))
  }

  function Map<X,S,T>(f: S -> T): Coreader<X,S> -> Coreader<X,T> {
    (r: Coreader<X,S>) => 
      Coreader(r.left, f(r.right))
  }

  function Composition<X,S,T,U>(f: Coreader<X,S> -> T, g: Coreader<X,T> -> U): Coreader<X,S> -> U {
    r => g(Extend(f, r))
  }

  lemma LemmaUnitalityExtract<X,T>(r: Coreader<X,T>)
    ensures Map(Extract)(Duplicate(r)) == r == Extract<X,Coreader<X,T>>(Duplicate(r))
  {
  }

  lemma LemmaAssociativityDuplicate<X,T>(r: Coreader<X,T>) 
    ensures Map(Duplicate)(Duplicate(r)) == Duplicate<X,Coreader<X,T>>(Duplicate(r))
  {
  }  

  lemma LemmaLeftUnitalityExtend<X,S,T>(r: Coreader<X,T>)
    ensures Extend(Extract, r) == r
  {
  }

  lemma LemmaRightUnitalityExtend<X,S,T>(f: Coreader<X,S> -> T, r: Coreader<X,S>)
    ensures Extract(Extend(f, r)) == f(r)
  {
  }

  lemma LemmaAssociativityExtend<X,S,T,U>(r: Coreader<X,S>, f: Coreader<X,S> -> T, g: Coreader<X,T> -> U)
    ensures Extend(g, Extend(f, r)) == Extend(Composition(f, g), r)
  {
  }

  lemma LemmaAssociativityComposition<X,S,T,U,V>(f: Coreader<X,S> -> T, g: Coreader<X,T> -> U, h: Coreader<X,U> -> V)
    ensures forall r: Coreader<X,S> :: Composition(Composition(f, g),h)(r) == Composition(f, Composition(g,h))(r)
  {
  }

  lemma LemmaIdentityExtract<X,S,T>(f: Coreader<X,S> -> T)
    ensures forall r: Coreader<X,S> :: Composition(f, Extract<X,T>)(r) == f(r) == Composition(Extract<X,S>, f)(r)
  {
  }
}