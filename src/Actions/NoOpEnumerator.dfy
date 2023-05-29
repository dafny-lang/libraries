
include "Enumerators.dfy"

module NoOp {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  class NoOp<T(!new)> extends Action<(), Option<T>> {

    const wrapped: Action<(), Option<T>>
    ghost const wrappedCanProduce: (seq<()>, seq<Option<T>>) -> bool
      
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
      && consumed == wrapped.consumed
      && produced == wrapped.produced
      && wrappedCanProduce == wrapped.CanProduce
    }

    constructor(wrapped: Action<(), Option<T>>) 
      requires wrapped.Valid()
      requires IsEnumerator(wrapped)
      requires wrapped.consumed == [] && wrapped.produced == []
      ensures Valid()
    { 
      this.wrapped := wrapped;

      consumed := [];
      produced := [];
      Repr := {this} + wrapped.Repr;
      height := wrapped.height + 1;
      wrappedCanProduce := wrapped.CanProduce;
      new;
      assert ValidWrappedProduced(consumed, produced, wrapped.produced);
    }

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<Option<T>>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<Option<T>>)
      decreases height
    {
      exists producedByWrapped: seq<Option<T>> :: ValidWrappedProduced(consumed, produced, producedByWrapped)
    }

    ghost predicate ValidWrappedProduced(consumed: seq<()>, produced: seq<Option<T>>, producedByWrapped: seq<Option<T>>) {
      && wrappedCanProduce(consumed, producedByWrapped)
      && produced == producedByWrapped
    }

    method Invoke(t: ()) returns (r: Option<T>) 
      requires Valid()
      requires CanConsume(consumed, produced, t)
      modifies Repr
      decreases height
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures consumed == old(consumed) + [t]
      ensures produced == old(produced) + [r]
    {
      r := wrapped.Invoke(());

      Repr := {this} + wrapped.Repr;
      Update(t, r);
      
      assert ValidWrappedProduced(consumed, produced, wrapped.produced);
    }

    lemma ThisIsEnumerator()
      requires Valid()
      ensures IsEnumerator(this)
    {
      var limit := EnumerationBound(wrapped);
      assert EnumerationBoundedBy(this, limit);
    }
  }
}