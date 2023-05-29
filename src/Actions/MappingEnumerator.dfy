
include "Enumerators.dfy"

module Mapped {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  class Map<T(!new), R(!new)> extends Action<(), Option<R>> {

    const wrapped: Action<(), Option<T>>
    ghost const wrappedCanProduce: (seq<()>, seq<Option<T>>) -> bool
      
    // TODO: Can we support --> or ~>?
    const f: T -> R

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
      && Enumerated(produced) == Seq.Map(f, Enumerated(wrapped.produced))
    }

    constructor(f: T -> R, wrapped: Action<(), Option<T>>) 
      requires wrapped.Valid()
      requires IsEnumerator(wrapped)
      requires wrapped.consumed == [] && wrapped.produced == []
      ensures Valid()
    { 
      this.f := f;
      this.wrapped := wrapped;

      consumed := [];
      produced := [];
      Repr := {this} + wrapped.Repr;
      height := wrapped.height + 1;
      wrappedCanProduce := wrapped.CanProduce;
      new;
      assert ValidWrappedProduced(produced, wrapped.produced);
    }

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<Option<R>>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<Option<R>>)
      decreases height
    {
      exists producedByWrapped: seq<Option<T>> :: ValidWrappedProduced(produced, producedByWrapped)
    }

    ghost predicate ValidWrappedProduced(produced: seq<Option<R>>, producedByWrapped: seq<Option<T>>) {
      && wrappedCanProduce(Seq.Repeat((), |producedByWrapped|), producedByWrapped)
      && Enumerated(produced) == Seq.Map(f, Enumerated(producedByWrapped))
    }

    method Invoke(t: ()) returns (r: Option<R>) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases height
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
    {
      assert ConsumesAnything(wrapped);
      assert wrapped.Valid();
      assert wrapped.CanProduce(wrapped.consumed, wrapped.produced);
      var x := wrapped.Invoke(());
      match x {
        case Some(v) => r := Some(f(v));
        case None => r := None;
      }
      Repr := {this} + wrapped.Repr;
      Update(t, r);
      EnumeratedDistributes(wrapped, x);
      assert Enumerated(wrapped.produced) == Enumerated(old(wrapped.produced)) + Enumerated([x]);
      Seq.LemmaMapDistributesOverConcat(f, Enumerated(old(wrapped.produced)), Enumerated([x]));
      assert Enumerated(old(produced)) == Seq.Map(f, Enumerated(old(wrapped.produced)));
      ThisIsEnumerator();
      calc {
        Enumerated(produced);
        { EnumeratedDistributes(this, r); }
        Enumerated(old(produced)) + Enumerated([r]);
      }
      assert ValidWrappedProduced(produced, wrapped.produced);
    }

    lemma ThisIsEnumerator()
      requires Valid()
      ensures IsEnumerator(this)
    {
      assert IsEnumerator(wrapped);
      var limit := EnumerationBound(wrapped);
      forall consumed, produced, next | CanProduce(consumed, produced) {
        assert CanConsume(consumed, produced, next);

        var producedByWrapped: seq<Option<T>> :| ValidWrappedProduced(produced, producedByWrapped);
        assert |Enumerated(producedByWrapped)| <= limit;
      }
    }
  }
}