include "Enumerators.dfy"

module NoOp {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq

  // Useful test case to ensure it's possible to compose Actions in general:
  // if you can't simply wrap an Action and implement the same specification,
  // there's no hope of changing behavior or composing Actions. :)
  class NoOp<T, R> extends Action<T, R> {

    const wrapped: Action<T, R>
      
    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> 
        && CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && CanProduce(history)
      && history == wrapped.history
    }

    constructor(wrapped: Action<T, R>) 
      requires wrapped.Valid()
      requires wrapped.history == []
      ensures Valid()
    { 
      this.wrapped := wrapped;

      history := [];
      Repr := {this} + wrapped.Repr;
      height := wrapped.height + 1;
      new;
    }

    ghost predicate CanConsume(history: seq<(T, R)>, next: T)
      requires CanProduce(history)
      decreases height
    {
      wrapped.CanConsume(history, next)
    }

    ghost predicate CanProduce(history: seq<(T, R)>)
      decreases height
    {
      wrapped.CanProduce(history)
    }

    method Invoke(t: T) returns (r: R) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert CanConsume(history, t);
      r := wrapped.Invoke(t);

      Repr := {this} + wrapped.Repr;
      Update(t, r);
      assert Valid();
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

    forall history, next | noop.CanProduce(history) ensures noopAsAction.CanConsume(history, next) {
      assert noop.CanConsume(history, next);
    }

    var limit := EnumerationBound(noop.wrapped);
    forall history | noopAsAction.CanProduce(history) ensures exists n: nat | n <= limit :: Terminated(Outputs(history), None, n) {
      assert noop.CanProduce(history);
    }
    assert EnumerationBoundedBy(noop, limit);
  }
}