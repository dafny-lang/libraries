
include "Enumerators.dfy"

module ConstructorExample {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  class C {
    var x: nat

    constructor(x: nat) 
      reads {}
      ensures this.x == x
    {
      this.x := x;
    }
  }

  class MakeCAction extends Action<nat, C> {

    ghost predicate Valid()
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && CanProduce(history)
      && (forall e <- history :: e.1 in Repr)
    }

    constructor() 
      ensures Valid()
      ensures fresh(Repr)
      ensures history == []
    { 
      history := [];
      Repr := {this};
    }

    ghost predicate CanConsume(history: seq<(nat, C)>, next: nat)
      requires CanProduce(history)
      decreases height
    {
      true
    }
    ghost predicate CanProduce(history: seq<(nat, C)>)
      reads this, Repr
      decreases height
    {
      forall e <- history :: e.1.x == e.0
    }

    method Invoke(t: nat) returns (r: C) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Valid();
      r := new C(t);

      Update(t, r);
    }
  }

  lemma MakeCActionMakesCs(a: MakeCAction)
    ensures forall history | a.CanProduce(history) :: 
      forall e: (nat, C) <- history :: fresh(e.1)

  // method Example() {
  //   var doubler := new FunctionAction(v => v + v);
    
  //   assert doubler.history == [];
    
  //   var x := doubler.Invoke(2);
  //   assert doubler.Produced() == [x];
  //   assert [x] == [4];
  //   assert x == 4;
  // }
}