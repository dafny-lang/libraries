
include "Actions.dfy"

module Enumerators {

  import opened Actions
  import opened Wrappers
  import opened Seq
  import opened Math

  function Enumerated<T>(produced: seq<Option<T>>): seq<T> {
    if |produced| == 0 || produced[0].None? then
      []
    else
      [produced[0].value] + Enumerated(produced[1..])
  }

  lemma TerminatedLimitBoundsEnumerated<T>(s: seq<Option<T>>, limit: nat) 
    requires exists n: nat | n <= limit :: Terminated(s, None, n)
    ensures |Enumerated(s)| <= limit
  {
    if |s| == 0 || s[0].None? {
    } else {
      var n: nat :| n <= limit && Terminated(s, None, n);
      assert Terminated(s[1..], None, n - 1);
      TerminatedLimitBoundsEnumerated(s[1..], limit - 1);
    }
  }

  lemma TerminatedBoundsEnumerated<T>(s: seq<Option<T>>, n: nat) 
    requires Terminated(s, None, n)
    ensures Math.Min(|s|, n) <= |Enumerated(s)|
  {
    if n == 0 || |s| == 0 {
    } else {
      if s[0] == None {
      } else {
        assert 1 <= |Enumerated(s)|;
        TerminatedBoundsEnumerated(s[1..], n - 1);
      }
    }
  }

  lemma TerminatedDistributesOverConcat<T>(left: seq<T>, right: seq<T>, c: T, n: nat)
    requires Terminated(left, c, |left|)
    requires Terminated(right, c, n)
    ensures Terminated(left + right, c, |left| + n)
  {}

  ghost function ProducedForEnumerator<T>(s: seq<T>, n: nat): seq<Option<T>> {
    var before := Math.Min(|s|, n);
    var after := Math.Max(|s|, n);
    Seq.Map(x => Some(x), s[..before]) + Seq.Repeat(None, after - before)
  }

  ghost predicate EnumeratesAtMost<T(!new)>(e: Action<(), Option<T>>, n: nat) {
    forall consumed: seq<()>, toProduce: seq<Option<T>> ::
      e.CanProduce(consumed, toProduce) ==> |Enumerated(toProduce)| <= n
  }

  ghost predicate ConsumesAnything<T(!new)>(a: Action<(), Option<T>>) {
    forall consumed, produced, next | a.CanProduce(consumed, produced) :: a.CanConsume(consumed, produced, next)
  }

  ghost predicate IsEnumerator<T(!new)>(a: Action<(), Option<T>>) {
    ConsumesAnything(a) && exists n :: ProducesTerminatedBy(a, None, n)
  }

  ghost function EnumerationLimit<T(!new)>(a: Action<(), Option<T>>): nat 
    requires IsEnumerator(a)
  {
    var limit: nat :| ProducesTerminatedBy(a, None, limit);
    limit
  }

  ghost function EnumerationTerminationMetric<T(!new)>(a: Action<(), Option<T>>): nat
    requires a.Valid()
    reads a.Repr
    requires IsEnumerator(a)
  {
    var limit := EnumerationLimit(a);
    TerminatedLimitBoundsEnumerated(a.produced, limit);
    limit - |Enumerated(a.produced)|
  }

  twostate lemma EnumerationTerminationMetricDecreased<T(!new)>(a: Action<(), Option<T>>, nextProduced: Option<T>)
    requires old(a.Valid())
    requires old(a.CanProduce(a.consumed, a.produced))
    requires a.Valid()
    requires a.CanProduce(a.consumed, a.produced)
    requires IsEnumerator(a)
    requires a.produced == old(a.produced) + [nextProduced];
    requires nextProduced.Some?
    ensures EnumerationTerminationMetric(a) < old(EnumerationTerminationMetric(a))
  {
    var before := old(a.produced);
    var n: nat :| n <= |before| && Terminated(before, None, n);
    var m: nat :| Terminated(a.produced, None, m);
    if n < |before| {
      assert before[|before| - 1] == None;
      assert a.produced[|a.produced| - 1] != None;
      assert |a.produced| <= m;
      assert a.produced[|before| - 1] != None;
      assert false;
    }
    assert |before| <= n;
    TerminatedLimitBoundsEnumerated(before, n);
    assert |Enumerated(before)| <= n;
    TerminatedDistributesOverConcat(before, [nextProduced], None, 1);
    assert Terminated(a.produced, None, |a.produced|);
    TerminatedBoundsEnumerated(a.produced, |a.produced|);
    assert |Enumerated(a.produced)| >= |a.produced|;
  }

  // Potentially infinite enumerator
  type IEnumerator<T> = Action<(), T> 

  class SeqEnumerator<T> extends Action<(), Option<T>> {

    const elements: seq<T>
    // TODO: size_t? It's a hell of a lot easier to prove correct
    // if this can increase unbounded to stay at |consumed|,
    // but it's not ghost so we care about bounding it.
    var index: nat

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0
    {
      && this in Repr
      && index == |consumed|
      && CanProduce(consumed, produced)
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

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<Option<T>>, next: ()) 
      decreases height
    {
      true
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<Option<T>>) 
      decreases height
    {
      var index := |consumed|;
      var values := Math.Min(index, |elements|);
      var nones := index - values;
      produced == Seq.Map(x => Some(x), elements[..values]) + Seq.Repeat(None, nones)
    }

    method Invoke(t: ()) returns (r: Option<T>) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases height
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
      ensures CanProduce(consumed, produced)
    {
      if index < |elements| {
        r := Some(elements[index]);
      } else {
        r := None;
      }

      index := index + 1;
      Update((), r);
    }
  }

  lemma SeqEnumeratorIsEnumerator<T(!new)>(e: SeqEnumerator<T>) 
    ensures IsEnumerator(e)
  {
    assert ConsumesAnything(e);
    forall consumed, produced | e.CanProduce(consumed, produced) 
    {
      assert Terminated(produced, None, |e.elements|);
      TerminatedLimitBoundsEnumerated(produced, |e.elements|);
      assert |Enumerated(produced)| <= |e.elements|;
    }
    assert ProducesTerminatedBy(e, None, |e.elements|);
  }

  class SeqIEnumerator<T> extends Action<(), T> {

    const elements: seq<T>
    var index: nat

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0
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

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<T>, next: ()) 
      decreases height
    {
      |consumed| + 1 <= |elements|
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<T>) 
      decreases height
    {
      |consumed| <= |elements| && produced == elements[..|consumed|]
    }

    method Invoke(t: ()) returns (r: T) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases height
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

  method EnumeratorExample() {
    var e2: SeqEnumerator<int> := new SeqEnumerator([1, 2, 3, 4, 5]);
    SeqEnumeratorIsEnumerator(e2);

    // Could be `while next :- e2.Invoke(())` instead :)
    while true 
      invariant e2.Valid()
      invariant fresh(e2.Repr)
      decreases EnumerationTerminationMetric(e2)
    {
      label beforeLoop: 
      var next: Option<int> := e2.Invoke(());
      if next.None? { break; }
      EnumerationTerminationMetricDecreased@beforeLoop(e2, next);

      print next.value;
    }
  }

  method IEnumeratorExample() {
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

  method Main() {
    EnumeratorExample();
  }
}