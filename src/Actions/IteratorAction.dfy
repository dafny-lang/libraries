include "Enumerators.dfy"

module IteratorActionExample {

  import opened Actions
  import opened Enumerators
  import opened Wrappers

  iterator Iter<T(0)>(s: set<T>) yields (x: T)
    yield ensures x in s && x !in xs[..|xs|-1]
    ensures s == set z | z in xs
  {
    var r := s;
    while (r != {})
      invariant r !! set z | z in xs
      invariant s == r + set z | z in xs
    {
      var y :| y in r;
      assert y !in xs;
      r, x := r - {y}, y;
      assert y !in xs;
      yield;
      assert y == xs[|xs|-1]; // a lemma to help prove loop invariant
    }
  }

  class IterAction<T(0, ==)> extends Action<(), Option<T>> {

    const i: Iter<T>
    var more: bool

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      ensures Valid() ==> CanProduce(history)
      decreases height, 0
    {
      && this in Repr
      && i in Repr
      && i._new <= Repr
      && i._reads <= Repr
      && i._modifies <= Repr
      && this !in i._reads
      && this !in i._new
      && (more ==> i.Valid())
      && CanProduce(history)
    }

    constructor(i: Iter<T>) 
      requires i.Valid()
      requires i.xs == []
      ensures Valid()
    {
      this.i := i;
      this.more := true;

      history := [];
      Repr := {this, i} + i._modifies + i._reads + i._new;
      new;
      assert (set x | x in Enumerated(Outputs(history))) == {};
    }

    ghost predicate CanConsume(history: seq<((), Option<T>)>, next: ())
      requires CanProduce(history)
      decreases height
    {
      true
    }

    ghost predicate CanProduce(history: seq<((), Option<T>)>)
      decreases height
    { 
      && var enumeratedSet := (set x | x in Enumerated(Outputs(history)));
      && enumeratedSet <= i.s
    }

    method Invoke(t: ()) returns (r: Option<T>) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
    {
      assert Valid();
      assert this !in i._reads;
      if more {
        r := Some(i.x);
        assert this !in i._reads;
      
        var more := i.MoveNext();
        assert this !in i._reads;
        assert more ==> i.Valid();
        assert this !in i._new;
      } else {
        assert this !in i._new;
        r := None;
        assert this !in i._new;
      }
      assert this !in i._new;
      assert more ==> i.Valid();

      Update(t, r);
      Repr := {this, i} + i._reads + i._new + i._modifies;

      assert this in Repr;
      assert i in Repr;
      assert i._reads <= Repr;
      assert i._new <= Repr;
      assert more ==> i.Valid();
      // assert CanProduce(consumed, produced);
    }
  }

}