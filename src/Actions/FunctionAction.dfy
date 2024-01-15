
include "Enumerators.dfy"

module Mapped {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  class FunctionAction<T, R> extends Action<T, R> {

    // TODO: Can we support ~>?
    const f: T --> R

    ghost predicate Valid()
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(consumed, produced)
      && produced == Seq.Map(f, consumed)
    }

    constructor(f: T -> R) 
      ensures Valid()
      ensures this.f == f
      ensures fresh(Repr)
      ensures consumed == []
    { 
      this.f := f;

      consumed := [];
      produced := [];
      Repr := {this};
    }

    ghost predicate CanConsume(consumed: seq<T>, produced: seq<R>, next: T)
      requires CanProduce(consumed, produced)
      decreases height
    {
      f.requires(next)
    }
    ghost predicate CanProduce(consumed: seq<T>, produced: seq<R>)
      decreases height
    {
      && (forall t <- consumed :: f.requires(t))
      && produced == Seq.Map(f, consumed)
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
    {
      r := f(t);

      Update(t, r);
    }
  }

  method Example() {
    var doubler := new FunctionAction(v => v + v);
    
    assert doubler.consumed == [];
    assert doubler.produced == [];
    
    var x := doubler.Invoke(2);
    assert doubler.produced == [x];
    assert [x] == [4];
    assert x == 4;
  }
}