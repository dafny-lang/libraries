
include "../Frames.dfy"

module IteratorExperiments {

  import opened Frames

  iterator ForEachWithIndex<T(0)>(s: seq<T>) yields (element: T, index: nat)
    ensures elements == s
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
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures more <==> !Done()
      ensures !Done() ==> Decreases() < old(Decreases())

    // TODO: Still a problem here with calling `Current`
    // on a fresh enumerator without first calling `MoveNext`
    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()

    predicate Done()
      requires Valid()
      reads this, Repr

    // Needs a better name, it's only a measure that is USED
    // in decreases clauses but not the same thing.
    // Although decreases is already overloaded to mean slightly
    // different things for a method spec vs. a while loop spec.
    // NOT what decreases means on an iterator though.
    function Decreases(): nat 
      reads this, Repr
      requires Valid()

    // Should this be forced on every enumerator? Or provided on
    // an Enumerator<T> wrapper instead, since it's implementable generically?
    // ghost var enumerated: set<T>
  }

  class ForEachWithIndexEnumerator<T(0)> extends Enumerator<(T, nat)> {

    const iter: ForEachWithIndex<T>
    ghost var remaining: nat
    ghost var done: bool

    constructor(s: seq<T>) 
      ensures Valid() 
      ensures fresh(Repr) 
      ensures !Done()
    {
      iter := new ForEachWithIndex(s);
      new;
      done := false;
      remaining := |iter.s| - |iter.elements|;
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
      && (!done ==> iter.Valid())
      && remaining == |iter.s| - |iter.elements|
    }

    predicate Done()
      requires Valid()
      reads this, Repr
    {
      done
    }

    method MoveNext() returns (more: bool) 
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures more <==> !Done()
      ensures !Done() ==> Decreases() < old(Decreases())
    {
      more := iter.MoveNext();
      done := !more;
      remaining := |iter.s| - |iter.elements|;
      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
    }

    function method Current(): (T, nat) 
      reads this, Repr
      requires Valid()
    {
      (iter.element, iter.index)
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid() 
    {
      remaining
    }
  }

  class Filter<T(0)> extends Enumerator<T> {
    const wrapped: Enumerator<T>
    const filter: T -> bool
    var current: T

    constructor(wrapped: Enumerator<T>, filter: T -> bool) 
      requires wrapped.Valid()
      ensures Valid() 
    {
      this.wrapped := wrapped;
      this.filter := filter;
      Repr := {this} + wrapped.Repr;
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && ValidComponent(wrapped)
    }

    predicate Done()
      requires Valid()
      reads this, Repr
    {
      wrapped.Done()
    }

    method MoveNext() returns (more: bool) 
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures more <==> !Done()
      ensures !Done() ==> Decreases() < old(Decreases())
    {
      more := true;
      while (true)
        invariant Valid()
        invariant more <==> !wrapped.Done()
        invariant old(allocated(wrapped)) && fresh(wrapped.Repr - old(wrapped.Repr))
        decreases more, wrapped.Decreases()
      {
        assert wrapped.Repr < Repr;     // should satify the method decreases clause...
        more := wrapped.MoveNext();     // wrong decreases clauses applied?
        Repr := Repr + wrapped.Repr;
        if (!more) { break; }

        current := wrapped.Current();
        if (filter(current)) {
          break;
        }
      }
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
    {
      current
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
    {
      wrapped.Decreases()
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
      invariant more <==> !e.Done()
      invariant old@start(allocated(e)) && fresh(e.Repr)
      decreases e.Decreases()
    {
      more := e.MoveNext();
      if (!more) { break; }
      var (element, index) := e.Current();

      print "Index: ", index, ", Element: ", element, "\n";
    }
  }

  datatype E<T> = Done | Next(T, () -> E<T>)

  function OneTwoThree(): E<nat> {
    Next(1, () => Next(2, () => Next(3, () => Done)))
  }

  function CountdownFrom(n: nat): E<nat> {
    if n > 0 then
      Next(n, () => CountdownFrom(n - 1))
    else
      Done
  }

  function CountupFrom(n: nat): E<nat> {
    if n > 0 then
      Next(n, () => CountdownFrom(n + 1))
    else
      Done
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