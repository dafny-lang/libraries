
include "../Frames.dfy"
include "../Wrappers.dfy"
include "Loopers.dfy"

module RustStyle {

  import opened Frames
  import opened Wrappers
  import opened Loopers

  trait RustStyleIterator<T> extends Validatable {

    method Next() returns (res: Option<T>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures res.Some? ==> Decreases() < old(Decreases())
      ensures old(Decreases()) == 0 ==> res.None?

    function Decreases(): nat
      reads Repr
      requires Valid()
  }

  class RustStyleIteratorEnumerator<T> extends Enumerator<T> {

    const iter: RustStyleIterator<T>
    var next: Option<T>

    ghost var decr: nat

    constructor(iter: RustStyleIterator<T>)
      requires iter.Valid()
      modifies iter.Repr
      ensures Valid()
      ensures iter.Repr <= old(iter.Repr)
      ensures Repr == {this} + iter.Repr
    {
      this.iter := iter;
      new;
      this.next := iter.Next();
      Repr := {this} + iter.Repr;
      if this.next.None? {
        decr := 0;
      } else {
        decr := iter.Decreases() + 1;
      }
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
      && ValidComponent(iter)
      && decr == (if this.next.None? then 0 else iter.Decreases() + 1)
    }

    method Step() 
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];
      next := iter.Next();
      if this.next.None? {
        decr := 0;
      } else {
        decr := iter.Decreases() + 1;
      }
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
    {
      next.value
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
    {
      decr
    }

    predicate method Done() 
      reads Repr
      requires Valid()
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
    {
      next.None?
    }
  }

  class SeqRustStyleIterator<T> extends RustStyleIterator<T> {

    var s: seq<T>

    constructor(s: seq<T>) 
      ensures Valid()
      ensures fresh(Repr)
    {
      this.s := s;
      Repr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
    }

    method Next() returns (res: Option<T>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures res.Some? ==> Decreases() < old(Decreases())
      ensures old(Decreases()) == 0 ==> res.None?
    {
      if |s| > 0 {
        res := Some(s[0]);
        s := s[1..];
      } else {
        res := None;
      }
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
    {
      |s|
    }
  }

  method Main() {
    var iter := new SeqRustStyleIterator([1,2,3,4,5]);

    var enum: Enumerator<int> := new RustStyleIteratorEnumerator(iter);
    while (!enum.Done()) 
      invariant enum.Valid() && fresh(enum.Repr)
      decreases enum.Decreases()
    {
      // Loop body starts
      print enum.Current();
      // Loop body ends

      enum.Step();
    }
  }
}