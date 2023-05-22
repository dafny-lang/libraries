
include "Enumerators.dfy"

module Filtered {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  class Filter<T(!new)> extends Action<(), Option<T>> {

    const wrapped: Action<(), Option<T>>
    ghost const wrappedCanProduce: (seq<()>, seq<Option<T>>) -> bool
      
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
      wrappedCanProduce := wrapped.CanProduce;
      new;
      assert Enumerated(produced) == Seq.Filter(filter, Enumerated(wrapped.produced));
    }

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<Option<T>>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<Option<T>>)
      decreases height
    {
      exists producedByWrapped: seq<Option<T>> ::
        && wrappedCanProduce(Seq.Repeat((), |producedByWrapped|), producedByWrapped)
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
      ensures CanProduce(consumed, produced)
    {
      while true
        invariant Valid()
        invariant fresh(wrapped.Repr - old(wrapped.Repr))
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
        var r' := wrapped.Invoke(());

        Repr := {this} + wrapped.Repr;
        r := r';

        if r.None? || filter(r.value) {
          break;
        }

        var wrappedEnumeratedBefore := Enumerated(old@before(wrapped.produced));
        assert wrapped.produced == old@before(wrapped.produced) + [r'];
        assert Terminated(old@before(wrapped.produced), None, |old@before(wrapped.produced)|);
        TerminatedDistributesOverConcat(old@before(wrapped.produced), [r], None, 1);
        assert Enumerated(wrapped.produced) == wrappedEnumeratedBefore + [r.value];
        LemmaFilterDistributesOverConcat(filter, wrappedEnumeratedBefore, [r.value]);
        assert Enumerated(produced) == Seq.Filter(filter, Enumerated(wrapped.produced));

        EnumerationTerminationMetricDecreased@before(wrapped, r);
      }


      Update(t, r);
    }
  }
}