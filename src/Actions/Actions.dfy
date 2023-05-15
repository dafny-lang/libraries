
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
    
    ghost predicate CanConsume(consumed: seq<T>, produced: seq<R>, nextIn: T)
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
      ensures Valid()
      // TODO: Might be too limiting, could have a similar predicate for valid Repr changes.
      // At least this is necessary most of the time if you want to invoke an action multiple times,
      // But won't be true in general (e.g. an aggregator that has to allocate more storage).
      ensures Repr <= old(Repr)
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
      ensures CanProduce(consumed, produced)
  }

  ghost predicate OnlyProduces<T(!new), R(!new)>(i: Action<T, R>, c: R) {
    forall consumed: seq<T>, toProduce: seq<R> :: 
      i.CanProduce(consumed, toProduce) <==> forall x <- toProduce :: x == c
  }

  ghost predicate TerminatedBy<T>(s: seq<T>, c: T) {
    forall i, j | 0 <= i < j < |s| :: s[i] == c ==> s[j] == c
  }

  ghost predicate ProducesTerminatedBy<T(!new), R(!new)>(i: Action<T, R>, c: R) {
    forall consumed: seq<T>, toProduce: seq<R> ::
      i.CanProduce(consumed, toProduce) ==> TerminatedBy(toProduce, c)
  }

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
  }

  // TODO: Not strong enough, could still be infinite. exists n | terminated beyond n?
  // TODO: How to provide decreases clause for loops etc?
  type Enumerator<T(!new)> = a: Action<(), Option<T>> | ProducesTerminatedBy(a, None) witness *

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  ghost function ProducedForEnumerator<T>(s: seq<T>, n: nat): seq<Option<T>> {
    var before := Math.Min(|s|, n);
    var after := Math.Max(|s|, n);
    Seq.Map(x => Some(x), s[..before]) + Seq.Repeat(None, after - before)
  }

  ghost predicate EnumeratesAtMost<T(!new)>(e: Enumerator<T>, n: nat) {
    forall consumed: seq<()>, toProduce: seq<Option<T>> ::
      e.CanProduce(consumed, toProduce) ==> |Enumerated(toProduce)| <= n
  }

  type IAggregator<T> = Action<T, ()>
  type Aggregator<T(!new)> = a: Action<T, bool>  | ProducesTerminatedBy(a, false) witness *

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



}