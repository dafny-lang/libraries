
include "Enumerators.dfy"

module Functions {

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
        && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
      && Produced() == Seq.Map(f, Consumed())
    }

    constructor(f: T -> R) 
      ensures Valid()
      ensures this.f == f
      ensures fresh(Repr)
      ensures history == []
    { 
      this.f := f;

      history := [];
      Repr := {this};
    }

    ghost predicate CanConsume(history: seq<(T, R)>, next: T)
      requires CanProduce(history)
      decreases height
    {
      f.requires(next)
    }
    ghost predicate CanProduce(history: seq<(T, R)>)
      decreases height
    {
      forall e <- history :: f.requires(e.0) && e.1 == f(e.0)
    }

    method Invoke(t: T) returns (r: R) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
      ensures EnsuresTwostate(t)
    {
      assert Valid();
      r := f(t);

      Update(t, r);
    }
  }

  method Example() {
    var doubler := new FunctionAction(v => v + v);
    
    assert doubler.history == [];
    
    var x := doubler.Invoke(2);
    assert doubler.Produced() == [x];
    assert [x] == [4];
    assert x == 4;
  }
}