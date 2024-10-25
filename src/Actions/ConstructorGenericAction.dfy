
include "Enumerators.dfy"

module GenericConstructorExample {

  import opened GenericActions
  import opened Enumerators
  import opened Wrappers
  import opened Seq
  import opened Termination

  class C {
    var x: nat

    constructor(x: nat) 
      reads {}
      ensures this.x == x
    {
      this.x := x;
    }
  }

  class MakeCAction extends GenericAction<nat, C> {

    constructor() 
    { 
    }

    ghost predicate Requires(t: nat)
      reads Reads(t) 
    {
      true
    }
    ghost function Reads(t: nat): set<object>
      reads this
      ensures this in Reads(t)
    {
      {this}
    }
    ghost function Modifies(t: nat): set<object>
      reads Reads(t)
    {
      {}
    }
    ghost function Decreases(t: nat): TerminationMetric
      reads Reads(t)
    {
      NatTerminationMetric(0)
    }
    twostate predicate Ensures(t: nat, new r: C)
      reads Reads(t)
    {
      true
    }

    method Invoke(t: nat) returns (r: C) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      r := new C(t);

      assert IsFresh(r);
    }

    twostate predicate IsFresh(new r: C) {
      fresh(r)
    }
  }

  // lemma MakeCActionMakesCs(a: MakeCAction)
  //   ensures forall history | a.CanProduce(history) :: 
  //     forall e: (nat, C) <- history :: fresh(e.1)

  // method Example() {
  //   var doubler := new FunctionAction(v => v + v);
    
  //   assert doubler.history == [];
    
  //   var x := doubler.Invoke(2);
  //   assert doubler.Produced() == [x];
  //   assert [x] == [4];
  //   assert x == 4;
  // }
}