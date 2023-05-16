
include "../Wrappers.dfy"
include "../Frames.dfy"
include "../Math.dfy"
include "../Collections/Sequences/Seq.dfy"

module Actions {

  import opened Wrappers
  import opened Frames
  import opened Seq
  import opened Math

  trait Action<T, R> extends Validatable {

    ghost var consumed: seq<T>
    ghost var produced: seq<R>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases Repr, 0
    
    ghost predicate CanConsume(consumed: seq<T>, produced: seq<R>, next: T)
      requires CanProduce(consumed, produced)

    ghost predicate CanProduce(consumed: seq<T>, produced: seq<R>)

    ghost method Update(t: T, r: R) 
      modifies `consumed, `produced
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
    {
      consumed := consumed + [t];
      produced := produced + [r];
    }

    method Invoke(t: T) returns (r: R) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases Repr
      ensures Valid()
      // TODO: Will cause trouble when composing, see FilteredEnumerator in Enumerators.dfy
      // ensures fresh(Repr - old(Repr))
      // TODO: Not compatible with all actions
      ensures Repr <= old(Repr)
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
      ensures CanProduce(consumed, produced)
  }

  // Common action invariants

  ghost predicate OnlyProduces<T(!new), R(!new)>(i: Action<T, R>, c: R) {
    forall consumed: seq<T>, toProduce: seq<R> :: 
      i.CanProduce(consumed, toProduce) <==> forall x <- toProduce :: x == c
  }

  ghost predicate TerminatedBy<T>(s: seq<T>, c: T) {
    forall i, j | 0 <= i < j < |s| :: s[i] == c ==> s[j] == c
  }

  ghost predicate TerminatedByBeyond<T>(s: seq<T>, c: T, n: nat) {
    forall i | n <= i < |s| :: s[i] == c
  }

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  lemma TerminatedByBoundsEnumerated<T>(s: seq<Option<T>>, n: nat) 
    requires TerminatedByBeyond(s, None, n)
    ensures |Enumerated(s)| <= n
  {
    if |s| == 0 || s[0].None? {
    } else {
      TerminatedByBoundsEnumerated(s[1..], n - 1);
    }
  }

  ghost function ProducedForEnumerator<T>(s: seq<T>, n: nat): seq<Option<T>> {
    var before := Math.Min(|s|, n);
    var after := Math.Max(|s|, n);
    Seq.Map(x => Some(x), s[..before]) + Seq.Repeat(None, after - before)
  }

  ghost predicate EnumeratesAtMost<T(!new)>(e: Action<(), Option<T>>, n: nat) {
    forall consumed: seq<()>, toProduce: seq<Option<T>> ::
      e.CanProduce(consumed, toProduce) ==> |Enumerated(toProduce)| <= n
  }

  

  ghost predicate ProducesTerminatedBy<T(!new), R(!new)>(i: Action<T, R>, c: R, n: nat) {
    forall consumed: seq<T>, toProduce: seq<R> ::
      i.CanProduce(consumed, toProduce) ==> TerminatedByBeyond(toProduce, c, n)
  }

  ghost predicate ConsumesAnything<T(!new)>(a: Action<(), Option<T>>) {
    forall consumed, produced, next | a.CanProduce(consumed, produced) :: a.CanConsume(consumed, produced, next)
  }

  ghost predicate IsEnumerator<T(!new)>(a: Action<(), Option<T>>) {
    ConsumesAnything(a) && exists n :: ProducesTerminatedBy(a, None, n)
  }

  ghost function EnumerationDecreases<T(!new)>(a: Action<(), Option<T>>): nat
    requires a.Valid()
    reads a.Repr
    requires IsEnumerator(a)
  {
    var limit: nat :| ProducesTerminatedBy(a, None, limit);
    TerminatedByBoundsEnumerated(a.produced, limit);
    limit - |Enumerated(a.produced)|
  }

  // Potentially infinite enumerator
  type IEnumerator<T> = Action<(), T> 

  class SeqIEnumerator<T> extends Action<(), T> {

    const elements: seq<T>
    var index: nat

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases Repr, 0
    {
      && this in Repr
      && 0 <= index <= |elements|
      && |consumed| == index
      && produced == elements[0..index]
    }

    constructor(s: seq<T>) 
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures produced == []
      ensures elements == s
    {
      elements := s;
      index := 0;
      
      consumed := [];
      produced := [];
      Repr := {this};
    }

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<T>, next: ()) {
      |consumed| + 1 <= |elements|
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<T>) {
      |consumed| <= |elements| && produced == elements[..|consumed|]
    }

    method Invoke(t: ()) returns (r: T) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
      ensures CanProduce(consumed, produced)
    {
      r := elements[index];
      index := index + 1;

      Update((), r);
    }
  }

  class Filter<T(!new)> extends Action<(), Option<T>> {

    const wrapped: Action<(), Option<T>>
      
    // TODO: Can we support --> or ~>?
    const filter: T -> bool

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && IsEnumerator(wrapped)
      && CanProduce(consumed, produced)
    }

    constructor(filter: T -> bool, wrapped: Action<(), Option<T>>) 
      requires wrapped.Valid()
      requires IsEnumerator(wrapped)
      requires wrapped.consumed == [] && wrapped.produced == []
      ensures Valid()
    { 
      this.filter := filter;
      this.wrapped := wrapped;

      consumed := [];
      produced := [];
      Repr := {this} + wrapped.Repr;
    }

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<Option<T>>, next: ()) {
      true
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<Option<T>>) {
      exists producedByWrapped: seq<Option<T>> ::
        && wrapped.CanProduce(Seq.Repeat((), |producedByWrapped|), producedByWrapped)
        && Enumerated(produced) == Seq.Filter(filter, Enumerated(producedByWrapped))
    }

    method Invoke(t: ()) returns (r: Option<T>) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
      ensures CanProduce(consumed, produced)
    {
      assert Enumerated(produced) == Seq.Filter(filter, Enumerated(wrapped.produced));
      r := wrapped.Invoke(());
      while r.Some? && !filter(r.value)
        invariant Valid()
        invariant Enumerated(produced) == Seq.Filter(filter, Enumerated(wrapped.produced))
        decreases EnumerationDecreases(wrapped)
      {
        r := wrapped.Invoke(());
      }

      Update(t, r);
    }
  }

  // class Compose<T, V(!new), R> extends Action<T, R> {

  //   const first: Action<T, V>
  //   const second: Action<V, R>

  //   ghost predicate Valid() 
  //     reads this, Repr 
  //     ensures Valid() ==> this in Repr 
  //     ensures Valid() ==> 
  //       && CanProduce(consumed, produced)
  //     decreases Repr, 0
  //   {
  //     && this in Repr
  //     && ValidComponent(first)
  //     && ValidComponent(second)
  //     && CanProduce(consumed, produced)
  //   }

  //   constructor(second: Action<V, R>, first: Action<T, V>) 
  //     requires first.Valid()
  //     requires second.Valid()
  //     requires first.Repr !! second.Repr
  //     requires first.CanProduce([], [])
  //     requires second.CanProduce([], [])
  //     ensures Valid()
  //     ensures produced == []
  //   { 
  //     this.first := first;
  //     this.second := second;

  //     consumed := [];
  //     produced := [];
  //     Repr := {this} + first.Repr + second.Repr;
  //   }

  //   ghost predicate CanConsume(consumed: seq<T>, produced: seq<R>, next: T) {
  //     exists vs: seq<V> :: 
  //       && first.CanProduce(consumed, vs)
  //       && first.CanConsume(consumed, vs, next)
  //   }
  //   ghost predicate CanProduce(consumed: seq<T>, produced: seq<R>) {
  //     exists vs: seq<V> :: first.CanProduce(consumed, vs) && second.CanProduce(vs, produced)
  //   }

  //   method Invoke(t: T) returns (r: R) 
  //     requires Valid()
  //     requires CanConsume(consumed, produced, t)
  //     modifies Repr
  //     decreases Repr
  //     ensures Valid()
  //     ensures Repr <= old(Repr)
  //     ensures consumed == old(consumed) + [t]
  //     ensures produced == old(produced) + [r]
  //     ensures CanProduce(consumed, produced)
  //   {
  //     var v := first.Invoke(t);
  //     r := second.Invoke(v);

  //     Update(t, r);
  //   }

  // }

  type IAggregator<T> = Action<T, ()>
  type Aggregator<T(!new)> = a: Action<T, bool> | exists n :: ProducesTerminatedBy(a, false, n) witness *

  class ArrayAggregator<T(0)> extends Action<T, ()> {

    var storage: array<T>
    var index: nat

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases Repr, 0
    {
      && this in Repr
      && storage in Repr
      && 0 < storage.Length
      && 0 <= index <= storage.Length
      && consumed == storage[..index]
      && produced == Seq.Repeat((), |consumed|)
    }

    constructor() 
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures produced == []
    {
      index := 0;
      storage := new T[10];

      consumed := [];
      produced := [];
      Repr := {this, storage};
    }

    ghost predicate CanConsume(consumed: seq<T>, produced: seq<()>, next: T) {
      true
    }
    ghost predicate CanProduce(consumed: seq<T>, produced: seq<()>) {
      produced == Seq.Repeat((), |consumed|)
    }

    twostate predicate ValidReprChange(before: set<object>, after: set<object>) {
      fresh(after - before)
    }

    method Invoke(t: T) returns (r: ()) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
      ensures CanProduce(consumed, produced)
    {
      if index == storage.Length {
        var newStorage := new T[storage.Length * 2];
        forall i | 0 <= i < index {
          newStorage[i] := storage[i];
        }
        storage := newStorage;

        Repr := {this, storage};
      }
      storage[index] := t;
      index := index + 1;

      r := ();
      Update(t, r);
    }

    function Values(): seq<T>
      requires Valid()
      reads Repr
      ensures Values() == consumed
    {
      storage[..index]
    }
  }

  // class SeqEnumerator<T> extends Action<(), Option<T>> {

  //   const elements: seq<T>
  //   var index: nat

  //   ghost predicate Valid() 
  //     reads this, Repr 
  //     ensures Valid() ==> this in Repr 
  //     ensures Valid() ==> 
  //       && CanProduce(consumed, produced)
  //     decreases Repr, 0
  //   {
  //     && this in Repr
  //     && 0 <= index <= |elements|
  //     && Enumerated(produced) == elements[0..index]
  //   }

  //   constructor(s: seq<T>) 
  //     ensures Valid()
  //     ensures fresh(Repr - {this})
  //     ensures produced == []
  //     ensures elements == s
  //   {
  //     elements := s;
  //     index := 0;
      
  //     consumed := [];
  //     produced := [];
  //     Repr := {this};
  //   }

  //   ghost predicate CanConsume(toConsume: seq<()>, produced: seq<Option<T>>, next: ()) {
  //     true
  //   }
  //   ghost predicate CanProduce(consumed: seq<()>, toProduce: seq<Option<T>>) {
  //     toProduce == ProducedForEnumerator(elements, |consumed|)
  //   }

  //   method Invoke(t: ()) returns (r: Option<T>) 
  //     requires Valid()
  //     requires CanConsume(consumed, produced, t)
  //     ensures Valid()
  //     ensures consumed == old(consumed) + [t]
  //     ensures produced == old(produced) + [r]
  //     ensures CanProduce(consumed, produced)
  //   {

  //   }
  // }



  method Main() {
    var e: Action<(), int> := new SeqIEnumerator([1, 2, 3, 4, 5]);
    var x := e.Invoke(());
    assert e.produced == [1];
    x := e.Invoke(());
    assert e.produced == [1, 2];
    x := e.Invoke(());
    assert e.produced == [1, 2, 3];
    x := e.Invoke(());
    assert e.produced == [1, 2, 3, 4];
    x := e.Invoke(());
    assert e.produced == [1, 2, 3, 4, 5];

    var a := new ArrayAggregator();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    assert a.Values() == [1, 2, 3, 4, 5];
  }
}