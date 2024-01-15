
include "../Wrappers.dfy"
include "../Frames.dfy"
include "../Math.dfy"
include "../Collections/Sequences/Seq.dfy"

module Actions {

  import opened Wrappers
  import opened Frames
  import opened Seq
  import opened Math

  trait {:termination false} Action<T, R> extends Validatable {

    ghost var consumed: seq<T>
    ghost var produced: seq<R>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0

    // KEY DESIGN POINT: these predicates specifically avoid reading the current
    // state of the action.
    // That's so extrisnic properties of an action do NOT depend on their current state.
    // This is key to ensure that you can prove properties of a given action that
    // will continue to hold as the Dafny heap changes.
    // The downside is that these are then forced to use quantifiers
    // to talk about all possible states of an action.

    ghost predicate CanConsume(consumed: seq<T>, produced: seq<R>, next: T)
      requires CanProduce(consumed, produced)
      decreases height

    ghost predicate CanProduce(consumed: seq<T>, produced: seq<R>)
      decreases height

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
      decreases height
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
      ensures CanProduce(consumed, produced)
  }

  // Common action invariants

  ghost predicate OnlyProduces<T(!new), R(!new)>(i: Action<T, R>, c: R) {
    forall consumed: seq<T>, toProduce: seq<R> :: 
      i.CanProduce(consumed, toProduce) <==> forall x <- toProduce :: x == c
  }

  ghost predicate Terminated<T>(s: seq<T>, c: T, n: nat) {
    forall i | 0 <= i < |s| :: n <= i <==> s[i] == c
  }

  lemma TerminatedUndistributes<T>(left: seq<T>, right: seq<T>, c: T, n: nat)
    requires Terminated(left + right, c, n)
    ensures Terminated(left, c, n)
    ensures Terminated(right, c, Math.Max(0, n - |left|))
  {
    assert forall i | 0 <= i < |left| :: left[i] == (left + right)[i];
    assert forall i | 0 <= i < |right| :: right[i] == (left + right)[i + |left|];
  }

  ghost predicate ProducesTerminatedBy<T(!new), R(!new)>(i: Action<T, R>, c: R, limit: nat) {
    forall consumed: seq<T>, produced: seq<R> ::
      i.CanProduce(consumed, produced) ==> exists n: nat | n <= limit :: Terminated(produced, c, n)
  }

  type IAggregator<T> = Action<T, ()>
  type Aggregator<T(!new)> = a: Action<T, bool> | exists limit :: ProducesTerminatedBy(a, false, limit) witness *

  // TODO: Refactor to use DynamicArray
  class ArrayAggregator<T(0)> extends Action<T, ()> {

    var storage: array<T>
    var index: nat

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0
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

    ghost predicate CanConsume(consumed: seq<T>, produced: seq<()>, next: T)
      decreases height
    {
      true
    }
    ghost predicate CanProduce(consumed: seq<T>, produced: seq<()>)
      decreases height
    {
      produced == Seq.Repeat((), |consumed|)
    }

    twostate predicate ValidReprChange(before: set<object>, after: set<object>) {
      fresh(after - before)
    }

    method Invoke(t: T) returns (r: ()) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases height
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

  method AggregatorExample() {
    var a := new ArrayAggregator();
    var _ := a.Invoke(1);
    var _ := a.Invoke(2);
    var _ := a.Invoke(3);
    var _ := a.Invoke(4);
    var _ := a.Invoke(5);
    assert a.Values() == [1, 2, 3, 4, 5];
  }
}