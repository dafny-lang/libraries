
include "Enumerators.dfy"

module Filtered {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  class Filter<T(!new)> extends Action<(), Option<T>> {

    const wrapped: Action<(), Option<T>>
      
    // TODO: Can we support --> or ~>?
    const filter: T -> bool

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && IsEnumerator(wrapped)
      && CanProduce(consumed, produced)
      && Enumerated(produced) == Seq.Filter(filter, Enumerated(wrapped.produced))
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
      height := wrapped.height + 1;
    }

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<Option<T>>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<Option<T>>)
      ensures CanProduce(consumed, produced) ==> |consumed| == |produced|
      decreases height
    {
      && |consumed| == |produced|
      && exists producedByWrapped: seq<Option<T>> :: ValidWrappedProduced(produced, producedByWrapped)
    }

    ghost predicate ValidWrappedProduced(produced: seq<Option<T>>, producedByWrapped: seq<Option<T>>) {
      && wrapped.CanProduce(Seq.Repeat((), |producedByWrapped|), producedByWrapped)
      && Enumerated(produced) == Seq.Filter(filter, Enumerated(producedByWrapped))
    }

    method {:vcs_split_on_every_assert} Invoke(t: ()) returns (r: Option<T>) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases height
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
    {
      while true
        invariant wrapped.Valid()
        invariant fresh(wrapped.Repr - old(wrapped.Repr))
        invariant ValidWrappedProduced(produced, wrapped.produced)
        invariant produced == old(produced)
        invariant consumed == old(consumed)
        invariant Enumerated(produced) == Seq.Filter(filter, Enumerated(wrapped.produced))
        decreases EnumerationTerminationMetric(wrapped)
      {
        assert IsEnumerator(wrapped);
        assert ConsumesAnything(wrapped);
        assert wrapped.Valid();
        assert wrapped.CanProduce(wrapped.consumed, wrapped.produced);
        label before:
        r := wrapped.Invoke(());

        Repr := {this} + wrapped.Repr;

        if r.None? || filter(r.value) {
          break;
        }
        EnumerationTerminationMetricDecreased@before(wrapped, r);

        // var wrappedEnumeratedBefore := Enumerated(old@before(wrapped.produced));
        // assert wrapped.produced == old@before(wrapped.produced) + [r];

        // ProducingSomeImpliesTerminated@before(wrapped, r);
        // TerminatedBoundsEnumerated(wrapped.produced, |wrapped.produced|);
        // // TerminatedDistributesOverConcat(old@before(wrapped.produced), [r], None, 1);
        // assert |Enumerated(wrapped.produced)| == |wrapped.produced|;
        // assert wrapped.produced == old@before(wrapped.produced) + [r];
        // EnumeratedDistributesOverConcat(old@before(wrapped.produced), [r], 1);
        // assert Enumerated(wrapped.produced) == Enumerated(old@before(wrapped.produced)) + [r.value];
        
        // assert Enumerated(old(produced)) == Seq.Filter(filter, Enumerated(old(wrapped.produced)));
        // calc {
        //   Seq.Filter(filter, Enumerated(wrapped.produced));
        //   Seq.Filter(filter, Enumerated(old(wrapped.produced) + [r]));
        //   Seq.Filter(filter, Enumerated(old(wrapped.produced)) + Enumerated([r]));
        //   Seq.Filter(filter, Enumerated(old(wrapped.produced)) + [r.value]);
        //   { LemmaFilterDistributesOverConcat(filter, wrappedEnumeratedBefore, [r.value]); }
        //   Seq.Filter(filter, Enumerated(old(wrapped.produced))) + Seq.Filter(filter, [r.value]);
        //   Seq.Filter(filter, Enumerated(old(wrapped.produced)));
        // }
        // assert Enumerated(produced) == Seq.Filter(filter, Enumerated(wrapped.produced));
      }

      assert r.Some? ==> filter(r.value);
      assert wrapped.CanProduce(wrapped.consumed, wrapped.produced);
      Update(t, r);
    }
  }
}