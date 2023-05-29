
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
      && consumed == wrapped.consumed
      && produced == Seq.Map(maybeF, wrapped.produced)
      && wrappedCanProduce == wrapped.CanProduce
    }

    constructor(f: T -> R, wrapped: Action<(), Option<T>>) 
      requires wrapped.Valid()
      requires IsEnumerator(wrapped)
      requires wrapped.consumed == [] && wrapped.produced == []
      ensures Valid()
      ensures fresh(Repr - (wrapped.Repr))
      ensures this.wrapped == wrapped;
      ensures this.f == f;
    { 
      this.f := f;
      this.wrapped := wrapped;

      consumed := [];
      produced := [];
      Repr := {this} + wrapped.Repr;
      height := wrapped.height + 1;
      wrappedCanProduce := wrapped.CanProduce;
      new;
      assert ValidWrappedProduced(consumed, produced, wrapped.produced);
    }

    ghost predicate CanConsume(consumed: seq<()>, produced: seq<Option<R>>, next: ())
      decreases height
    {
      true
    }
    ghost predicate CanProduce(consumed: seq<()>, produced: seq<Option<R>>)
      decreases height
    {
      exists producedByWrapped: seq<Option<T>> :: ValidWrappedProduced(consumed, produced, producedByWrapped)
    }

    ghost predicate ValidWrappedProduced(consumed: seq<()>, produced: seq<Option<R>>, producedByWrapped: seq<Option<T>>) {
      && wrappedCanProduce(consumed, producedByWrapped)
      && produced == Seq.Map(maybeF, producedByWrapped)
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
      assert wrapped.Valid();
      var x := wrapped.Invoke(());
      match x {
        case Some(v) => r := Some(f(v));
        case None => r := None;
      }
      Repr := {this} + wrapped.Repr;
      Update(t, r);

      Seq.LemmaMapDistributesOverConcat(maybeF, old(wrapped.produced), [x]);
      assert ValidWrappedProduced(consumed, produced, wrapped.produced);
    }

    function maybeF(t: Option<T>): Option<R> {
      match t
      case Some(v) => Some(f(v))
      case None => None
    }

    lemma ThisIsEnumerator()
      requires Valid()
      ensures IsEnumerator(this)
    {
      var limit := EnumerationBound(wrapped);
      forall consumed, produced | CanProduce(consumed, produced) 
        ensures exists n: nat | n <= limit :: Terminated(produced, None, n)
      {
        var producedByWrapped :| ValidWrappedProduced(consumed, produced, producedByWrapped);
        var n :| n <= limit && Terminated(producedByWrapped, None, n);
        assert Terminated(produced, None, n);
      }
      assert EnumerationBoundedBy(this, limit);
    }
  }

  method Example() {
    var e: SeqEnumerator<int> := new SeqEnumerator([1, 2, 3, 4, 5]);
    SeqEnumeratorIsEnumerator(e);
    var f: Map<int, int> := new Map(x => x * 2, e);
    
    var x := f.Invoke(());
    assert f.produced == [Some(2)];
    assert [x] == [Some(2)];
    assert x == Some(2);
  }
}