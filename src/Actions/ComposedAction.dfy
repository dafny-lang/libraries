include "Actions.dfy"

module Composed {

  import opened Actions

  class Compose<T(!new), V(!new), R(!new)> extends Action<T, R> {

    const first: Action<T, V>
    const second: Action<V, R>

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      ensures Valid() ==> 
        && CanProduce(consumed, produced)
      decreases height, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && CanProduce(consumed, produced)
      && consumed == first.consumed
      && produced == second.produced
    }

    constructor(second: Action<V, R>, first: Action<T, V>) 
      requires first.Valid()
      requires second.Valid()
      requires first.Repr !! second.Repr
      requires first.consumed == []
      requires first.produced == []
      requires second.consumed == []
      requires second.produced == []
      ensures Valid()
      ensures produced == []
    { 
      this.first := first;
      this.second := second;

      consumed := [];
      produced := [];
      Repr := {this} + first.Repr + second.Repr;
      height := first.height + second.height + 1;
    }

    ghost predicate CanConsume(consumed: seq<T>, produced: seq<R>, next: T)
      requires CanProduce(consumed, produced)
      decreases height
    {
      forall vs: seq<V> | first.CanProduce(consumed, vs) ::
        first.CanConsume(consumed, vs, next)

      // Note that you can't compose any arbitrary first with a second:
      // if you need to read first.produced to know if you can consume another input,
      // that won't work here because this outer CanConsume predicate doesn't take that as input.
      // (...unless there's a way of inferring what was produced from second.produced??)
    }

    ghost predicate CanProduce(consumed: seq<T>, produced: seq<R>)
      decreases height
    {
      forall vs: seq<V> | first.CanProduce(consumed, vs) ::
        second.CanProduce(vs, produced)
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
      ensures CanProduce(consumed, produced)
    {
      assert first.Valid();
      var v := first.Invoke(t);
      
      assert second.Valid();
      r := second.Invoke(v);

      Update(t, r);
      Repr := {this} + first.Repr + second.Repr;
    }

  }
}