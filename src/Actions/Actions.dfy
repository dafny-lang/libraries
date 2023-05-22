
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

  ghost predicate ProducesTerminatedBy<T(!new), R(!new)>(i: Action<T, R>, c: R, limit: nat) {
    forall consumed: seq<T>, produced: seq<R> ::
      i.CanProduce(consumed, produced) ==> exists n: nat | n <= limit :: Terminated(produced, c, n)
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