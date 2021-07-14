// RUN: %dafny "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../Mathematics.dfy"

module Isets {

  import Math = Mathematics

  /* If all elements in iset x are in iset y, x is a subset of y. */
  lemma lemma_subset<T>(x: iset<T>, y: iset<T>)
    requires forall e {:trigger e in y} :: e in x ==> e in y
    ensures x <= y
  {
  }

  /* Apply an injective function to each element of an iset. */
  function {:opaque} apply<X(!new), Y>(xs: iset<X>, f: X-->Y): (ys: iset<Y>)
    reads f.reads
    requires forall x {:trigger f.requires(x)} :: f.requires(x)
    requires Math.injective(f)
    ensures forall x {:trigger f(x)} :: x in xs <==> f(x) in ys
  {
    var ys := iset x | x in xs :: f(x);
    ys
  }

  /* Construct an iset using elements of another set for which a function
  returns true. */
  function {:opaque} filter<X(!new)>(xs: iset<X>, f: X~>bool): (ys: iset<X>)
    reads f.reads
    requires forall x {:trigger f.requires(x)} {:trigger x in xs} :: x in xs ==> f.requires(x)
    ensures forall y {:trigger f(y)}{:trigger y in xs} :: y in ys <==> y in xs && f(y)
  {
    var ys := iset x | x in xs && f(x);
    ys
  }

}
