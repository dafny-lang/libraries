
include "Enumerators.dfy"

module Mapped {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  class Map<T, R(!new), R'(!new)> extends Action<T, R'> {

    const wrapped: Action<T, R>
    ghost const wrappedCanConsume: (seq<T>, seq<R>, T) --> bool
    ghost const wrappedCanProduce: (seq<T>, seq<R>) -> bool
      
    // TODO: Can we support --> or ~>?
    const f: R -> R'

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && CanProduce(consumed, produced)
      && consumed == wrapped.consumed
      && produced == Seq.Map(f, wrapped.produced)
      && wrappedCanConsume == wrapped.CanConsume
      && wrappedCanProduce == wrapped.CanProduce
    }

    constructor(f: R -> R', wrapped: Action<T, R>) 
      requires wrapped.Valid()
      requires wrapped.consumed == [] && wrapped.produced == []
      ensures Valid()
      ensures fresh(Repr - (wrapped.Repr))
      ensures this.wrapped == wrapped
      ensures this.f == f
    { 
      this.f := f;
      this.wrapped := wrapped;

      consumed := [];
      produced := [];
      Repr := {this} + wrapped.Repr;
      height := wrapped.height + 1;
      wrappedCanConsume := wrapped.CanConsume;
      wrappedCanProduce := wrapped.CanProduce;
      new;
      assert ValidWrappedProduced(consumed, produced, wrapped.produced);
    }

    ghost predicate CanConsume(consumed: seq<T>, produced: seq<R'>, next: T)
      requires CanProduce(consumed, produced)
      decreases height
    {
      forall producedByWrapped: seq<R> | ValidWrappedProduced(consumed, produced, producedByWrapped) ::
        assert wrapped.CanProduce(consumed, producedByWrapped);
        wrapped.CanConsume(consumed, producedByWrapped, next)
    }
    ghost predicate CanProduce(consumed: seq<T>, produced: seq<R'>)
      decreases height
    {
      exists producedByWrapped: seq<R> :: ValidWrappedProduced(consumed, produced, producedByWrapped)
    }

    ghost predicate ValidWrappedProduced(consumed: seq<T>, produced: seq<R'>, producedByWrapped: seq<R>) {
      && wrappedCanProduce(consumed, producedByWrapped)
      && produced == Seq.Map(f, producedByWrapped)
    }

    method Invoke(t: T) returns (r: R') 
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
      var x := wrapped.Invoke(t);
      r := f(x);

      Repr := {this} + wrapped.Repr;
      Update(t, r);

      Seq.LemmaMapDistributesOverConcat(f, old(wrapped.produced), [x]);
      assert ValidWrappedProduced(consumed, produced, wrapped.produced);
    }
  }

  // lemma EnumeratornessCommutes<R(!new), R'(!new)>(mapped: Map<(), Option<R>, Option<R'>>)
  //   requires mapped.Valid()
  //   requires IsEnumerator(mapped.wrapped)
  //   ensures IsEnumerator(mapped)
  // {
  //   var limit := EnumerationBound(mapped.wrapped);
  //   forall consumed, produced | mapped.CanProduce(consumed, produced) 
  //     ensures exists n: nat | n <= limit :: Terminated(produced, None, n)
  //   {
  //     var producedByWrapped :| mapped.ValidWrappedProduced(consumed, produced, producedByWrapped);
  //     var n :| n <= limit && Terminated(producedByWrapped, None, n);
  //     assert Terminated(produced, None, n);
  //   }
  //   assert EnumerationBoundedBy(mapped, limit);
  // }

  method Example() {
    var e: SeqEnumerator<int> := new SeqEnumerator([1, 2, 3, 4, 5]);
    SeqEnumeratorIsEnumerator(e);
    var f := (x: Option<int>) => match x {
      case Some(v) => Some(v + v)
      case None => None
    };
    var mapped: Map<(), Option<int>, Option<int>> := new Map(f, e);
    
    var x := mapped.Invoke(());
    assert mapped.produced == [Some(2)];
    assert [x] == [Some(2)];
    assert x == Some(2);
  }
}