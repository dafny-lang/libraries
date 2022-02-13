
include "../Frames.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module IteratorExperiments {

  import opened Frames
  import opened Wrappers

  import Seq

  // Would like to make this extend the even more general Looper
  // concept, but tough to use without bounded polymorphism.
  trait Enumerator<T> extends Validatable {

    // Any enumerator that produces one value at a time
    // and provably terminates is equivalent to an enumerator
    // that produces a specific seq<T>. This value may be underspecified
    // such that it is not known, even its length, until after all
    // values have been produced.
    // Dafny doesn't let you pass around an underspecified value though,
    // so we don't define a "to be enumerated" field or function.
    ghost var enumerated: seq<T>

    // Valid() is used as the enumeration invariant

    method MoveNext() returns (more: bool)
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures more <==> !Done()
      ensures !Done() ==> HasCurrent()
      ensures !Done() ==> Decreases() < old(Decreases())
      ensures !Done() ==> enumerated == old(enumerated) + [Current()]

    predicate HasCurrent()
      reads this, Repr
      requires Valid()

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires HasCurrent()

    function Decreases(): nat 
      reads this, Repr
      requires Valid()

    predicate method Done()
      requires Valid()
      reads this, Repr
  }

  class SeqEnumerator<T> extends Enumerator<T> {

    const elements: seq<T>
    var index: nat

    constructor(s: seq<T>) 
      ensures Valid()
      ensures fresh(Repr - {this})
    {
      elements := s;
      index := 0;
      Repr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
      && 0 <= index <= |elements|
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
    {
      |elements| - index
    }

    predicate method Done() 
      reads Repr
      requires Valid()
      ensures Decreases() == 0 ==> Done()
    {
      index == |elements|
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())
    {
      index := index + 1;
    }
  }

  iterator ForEachWithIndex<T(0)>(s: seq<T>) yields (element: T, index: nat)
    yield ensures elements <= s
    ensures elements == s
  {
    for i := 0 to |s|
      invariant i == |elements|
      invariant elements <= s
    {
      yield s[i], i;
    }
  }

  class ForEachWithIndexEnumerator<T(0)> extends Enumerator<(T, nat)> {

    const iter: ForEachWithIndex<T>
    var done: bool

    ghost const original: seq<T>
    ghost var hasCurrent: bool

    constructor(s: seq<T>) 
      ensures Valid() 
      ensures fresh(Repr) 
      ensures !Done()
    {
      iter := new ForEachWithIndex(s);
      original := s;
      new;
      done := false;
      hasCurrent := false;
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
      && enumerated == Seq.Zip(original[0..|enumerated|], Range(0, |enumerated|))
    }

    predicate method Done()
      requires Valid()
      reads this, Repr
      ensures Done() ==> enumerated == Seq.Zip(original, Range(0, |original|))
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
      ensures !Done() ==> HasCurrent()
      ensures !Done() ==> Decreases() < old(Decreases())
      ensures !Done() ==> enumerated == old(enumerated) + [Current()]
    {
      more := iter.MoveNext();
      done := !more;

      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
      if more {
        hasCurrent := true;
        enumerated := enumerated + [Current()];
      }
    }

    predicate HasCurrent()
      reads this, Repr
      requires Valid()
    {
      hasCurrent
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
      |original| - |enumerated|
    }
  }

  // TODO: move to Seq.dfy?
  function Range(start: int, end: int): seq<int> 
    requires start <= end
    decreases end - start
  {
    var length := end - start;
    seq(length, i requires 0 <= i < length => start + i)
  }

  // TODO: Prove the semantics!
  class Filter<T(0)> extends Enumerator<T> {
    const wrapped: Enumerator<T>
    const filter: T -> bool
    var hasCurrent: bool
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

    predicate method Done()
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
      ensures !Done() ==> HasCurrent()
      ensures !Done() ==> Decreases() < old(Decreases())
      ensures !Done() ==> enumerated == old(enumerated) + [Current()]
    {
      assert wrapped.Repr < Repr; 
      more := true;
      while (true)
        invariant Valid()
        invariant more <==> !wrapped.Done()
        modifies Repr
        decreases more, wrapped.Decreases()
      {
        assert wrapped.Repr < old(Repr);
        more := wrapped.MoveNext();
        Repr := Repr + wrapped.Repr;
        if (!more) { break; }

        assert Valid();
        assert wrapped.HasCurrent();
        current := wrapped.Current();
        if (filter(current)) {
          enumerated := enumerated + [Current()];
          break;
        }
      }
    }

    predicate HasCurrent()
      reads this, Repr
      requires Valid()
    {
      hasCurrent
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

    predicate DoneProperty() 
      requires Valid()
      requires Done()
      reads this, Repr
    {
      enumerated == wrapped.enumerated
    }
  }

  // (0) is necessary because we can't just use an Option<T> to
  // hold the current value - the spec doesn't prevent you from constructing
  // this and then calling Current() before calling MoveNext()
  // TODO: multiset version as well? Instead?
  class SetEnumerator<T(==, 0)> extends Enumerator<T> {
    ghost const original: set<T>
    var remaining: set<T>
    var current: T
    var hasCurrent: bool
    var done: bool

    constructor(s: set<T>) 
      ensures Valid() 
      ensures fresh(Repr)
    {
      this.original := s;
      this.remaining := s;
      this.done := false;

      enumerated := [];
      Repr := {this};
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
    }

    predicate method Done()
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
      ensures more ==> HasCurrent()
      ensures !Done() ==> Decreases() < old(Decreases())
      ensures !Done() ==> enumerated == old(enumerated) + [Current()]
    {
      if |remaining| == 0 {
        done := true;
        more := false;
      } else {
        var c :| c in remaining;
        current := c;
        hasCurrent := true;
        enumerated := enumerated + [current];
        remaining := remaining - {c};
        more := true;
      }
    }

    predicate HasCurrent()
      reads this, Repr
      requires Valid()
    {
      hasCurrent
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires HasCurrent()
    {
      current
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
    {
      |remaining|
    }

    predicate DoneProperty() 
      requires Valid()
      requires Done()
      reads this, Repr
    {
      multiset(enumerated) == multiset(original)
    }
  }

  // method Max(s: set<int>) returns (max: int)
  //   requires |s| > 0
  //   ensures max in s
  //   ensures forall x | x in s :: max >= x
  // {
  //   var first: int :| first in s;
  //   max := first;
  //   var sEnum: SetEnumerator<int> := new SetEnumerator(s - {max});
  //   assert fresh(sEnum.Repr);
  //   label start:
  //   var more := true;
  //   while (!sEnum.Done()) 
  //     invariant sEnum.Valid()
  //     invariant fresh(sEnum.Repr)
  //     invariant max == Seq.Max([first] + sEnum.enumerated)
  //     decreases more, sEnum.Decreases()
  //   {
  //     var more := sEnum.MoveNext();
  //     if !more { break; }

  //     if sEnum.Current() > max {
  //       max := sEnum.Current();
  //     }
  //   }
  // }

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

  datatype E<T> = Done | Next(T, Enum<T>)
  type Enum<T> = () -> E<T>

  function OneTwoThree(): Enum<nat> {
    () => Next(1, () => Next(2, () => Next(3, () => Done)))
  }

  function CountdownFrom(n: nat): Enum<nat> {
    () => 
      if n > 0 then
        Next(n, CountdownFrom(n - 1))
      else
        Done
  }

  // Doesn't terminate so you can't do this
  // function CountupFrom(n: nat): Enum<nat> {
  //   () => Next(n, CountupFrom(n + 1))
  // }

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