
include "../Frames.dfy"

module IteratorExperiments {

  import opened Frames

  iterator ForEachWithIndex<T(0)>(s: seq<T>) yields (element: T, index: nat)
    ensures elements <= s
    yield ensures elements <= s
  {
    for i := 0 to |s|
      invariant i == |elements|
      invariant elements <= s
    {
      yield s[i], i;
    }
  }

  trait Enumerator<T> extends Validatable {

    method MoveNext() returns (more: bool)
      requires Valid()
      modifies Repr
      ensures fresh(Repr - old(Repr))
      ensures more ==> Valid()
      ensures more ==> Decreases() < old(Decreases())

    function method Current(): T
      reads this, Repr
      requires Valid()

    function Decreases(): nat 
      reads this, Repr
      requires Valid()
  }

  class ForEachWithIndexEnumerator<T(0)> extends Enumerator<(T, nat)> {

    const iter: ForEachWithIndex<T>
    ghost var remaining: nat

    constructor(s: seq<T>) ensures Valid() ensures fresh(Repr) {
      iter := new ForEachWithIndex(s);
      new;
      remaining := |iter.s|;
      Repr := {this, iter};
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && iter in Repr
      && this !in iter._modifies
      && this !in iter._reads
      && this !in iter._new
      && iter._modifies <= Repr
      && iter._reads <= Repr
      && iter._new <= Repr
      && iter.Valid()
      && remaining == |iter.s| - |iter.elements|
    }

    method MoveNext() returns (more: bool) 
      requires Valid()
      modifies Repr
      ensures fresh(Repr - old(Repr))
      ensures more ==> Valid()
      ensures more ==> Decreases() < old(Decreases())
    {
      more := iter.MoveNext();
      if (more) {
        assert old(iter.elements) < iter.elements;
      }
      remaining := |iter.s| - |iter.elements|;
      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
    }

    function method Current(): (T, nat) 
      reads this, Repr
      requires Valid()
    {
      (iter.element, iter.index)
    }

    function Decreases(): nat reads this, Repr requires Valid() {
      remaining
    }
  }

  method Main() {
    var s: seq<nat> := [1, 1, 2, 3, 5, 8];
    var e: Enumerator<(nat, nat)> := new ForEachWithIndexEnumerator(s);
    assert fresh(e.Repr);
    label start:
    var more := true;
    while (true) 
      invariant e.Valid()
      invariant old@start(allocated(e)) && fresh(e.Repr)
      decreases e.Decreases()
    {
      more := e.MoveNext();
      if (!more) { break; }

      var (element, index) := e.Current();
      print "Index: ", index, ", Element: ", element;
    }
  }

  // iterator Iter<T(0)>(s: set<T>) yields (x: T)
  //   yield ensures x in s && x !in xs[..|xs|-1];
  //   ensures s == set z | z in xs;
  // {
  //   var r := s;
  //   while (r != {})
  //     invariant forall z :: z in xs ==> x !in r;
  //                                 // r and xs are disjoint
  //     invariant s == r + set z | z in xs;
  //   {
  //     var y :| y in r;
  //     r, x := r - {y}, y;
  //     yield;
  //     assert y == xs[|xs|-1]; // a lemma to help prove loop invariant
  //   }
  // }

  // method UseIterToCopy<T(0)>(s: set<T>) returns (t: set<T>)
  //   ensures s == t;
  // {
  //   t := {};
  //   var m := new Iter(s);
  //   while (true)
  //     invariant m.Valid() && fresh(m._new);
  //     invariant t == set z | z in m.xs;
  //     decreases s - t;
  //   {
  //     var more := m.MoveNext();
  //     if (!more) { break; }
  //     t := t + {m.x};
  //   }
  // }
}