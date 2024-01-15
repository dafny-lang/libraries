
include "Enumerators.dfy"

module NoOp {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  // Useful test case to ensure it's possible to compose Actions in general:
  // if you can't simply wrap an Action and implement the same specification,
  // there's no hope of changing behavior or composing Actions. :)
  class NoOp<T(!new), R(!new)> extends Action<T, R> {

    const wrapped: Action<T, R>
      
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
      && produced == wrapped.produced
    }

    constructor(wrapped: Action<T, R>) 
      requires wrapped.Valid()
      requires wrapped.consumed == [] && wrapped.produced == []
      ensures Valid()
    { 
      this.wrapped := wrapped;

      consumed := [];
      produced := [];
      Repr := {this} + wrapped.Repr;
      height := wrapped.height + 1;
      new;
    }

    ghost predicate CanConsume(consumed: seq<T>, produced: seq<R>, next: T)
      requires CanProduce(consumed, produced)
      decreases height
    {
      wrapped.CanConsume(consumed, produced, next)
    }

    ghost predicate CanProduce(consumed: seq<T>, produced: seq<R>)
      decreases height
    {
      wrapped.CanProduce(consumed, produced)
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
      r := wrapped.Invoke(t);

      Repr := {this} + wrapped.Repr;
      Update(t, r);
    }
  }

  lemma EnumeratornessCommutes<R(!new)>(noop: NoOp<(), Option<R>>)
    requires noop.Valid()
    requires IsEnumerator(noop.wrapped)
    ensures IsEnumerator(noop)
  {
    // TODO: working around the fact that triggers don't automatically apply
    // because noop has the type NoOp as opposed to Action.
    // Not sure if there's a more reusable workaround to the problem (which is going to recur frequently in this library)
    var noopAsAction: Action<(), Option<R>> := noop;

    forall consumed, produced, next | noop.CanProduce(consumed, produced) ensures noopAsAction.CanConsume(consumed, produced, next) {
      assert noop.CanConsume(consumed, produced, next);
    }

    var limit := EnumerationBound(noop.wrapped);
    forall consumed: seq<()>, produced: seq<Option<R>> | noopAsAction.CanProduce(consumed, produced) ensures exists n: nat | n <= limit :: Terminated(produced, None, n) {
      assert noop.CanProduce(consumed, produced);
    }
    assert EnumerationBoundedBy(noop, limit);
  }
}