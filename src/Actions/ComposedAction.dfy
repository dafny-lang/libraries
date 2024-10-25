include "Actions.dfy"
include "Enumerators.dfy"
include "FunctionAction.dfy"

module Composed {

  import opened Actions
  import opened Enumerators
  import opened Wrappers
  import opened Seq
  import opened Functions

  class Compose<T(!new), V(!new), R(!new)> extends Action<T, R> {

    const first: Action<T, V>
    const second: Action<V, R>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && CanProduce(history)
      && Consumed() == first.Consumed()
      && first.Produced() == second.Consumed()
      && Produced() == second.Produced()
    }

    constructor(second: Action<V, R>, first: Action<T, V>) 
      requires first.Valid()
      requires second.Valid()
      requires first.Repr !! second.Repr
      requires first.history == []
      requires second.history == []
      ensures Valid()
      ensures history == []
    { 
      this.first := first;
      this.second := second;

      history := [];
      Repr := {this} + first.Repr + second.Repr;
      height := first.height + second.height + 1;
    }

    ghost predicate CanConsume(history: seq<(T, R)>, next: T)
      requires CanProduce(history)
      decreases height
    {
      forall piped: seq<V> | CanPipe(history, piped) :: 
        && var firstHistory := Seq.Zip(Inputs(history), piped);
        && var secondHistory := Seq.Zip(piped, Outputs(history));
        && first.CanConsume(firstHistory, next)
        && forall pipedNext: V | first.CanProduce(firstHistory + [(next, pipedNext)]) ::
          && second.CanConsume(secondHistory, pipedNext)

      // Note that you can't compose any arbitrary first with a second:
      // if you need to read first.produced to know if you can consume another input,
      // that won't work here because this outer CanConsume predicate doesn't take that as input.
      // (...unless there's a way of inferring what was produced from second.produced)
    }

    ghost predicate CanProduce(history: seq<(T, R)>)
      decreases height
    {
      exists piped: seq<V> :: CanPipe(history, piped)
    }

    ghost predicate CanPipe(history: seq<(T, R)>, piped: seq<V>) 
      decreases height, 0
    {
      && |piped| == |history|
      && first.CanProduce(Seq.Zip(Inputs(history), piped))
      && second.CanProduce(Seq.Zip(piped, Outputs(history)))
    }

    method Invoke(t: T) returns (r: R) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert first.Valid();
      var v := first.Invoke(t);
      r := second.Invoke(v);

      Update(t, r);
      Repr := {this} + first.Repr + second.Repr;
    }
  }

  method Example() {
    var e: SeqEnumerator<int> := new SeqEnumerator([1, 2, 3, 4, 5]);
    SeqEnumeratorIsEnumerator(e);
    var f := (x: Option<int>) => match x {
      case Some(v) => Some(v + v)
      case None => None
    };
    var doubler := new FunctionAction(f);
    var mapped: Compose<(), Option<int>, Option<int>> := new Compose(doubler, e);

    // TODO: Need some lemmas
    var x := mapped.Invoke(());
    assert mapped.Produced() == [Some(2)];
    assert [x] == [Some(2)];
    assert x == Some(2);
  }
}