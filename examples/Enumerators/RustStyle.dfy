// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/Frames.dfy"
include "../../src/Wrappers.dfy"
include "Enumerators.dfy"

// There are lots of ways to define an Iterator/Enumerator
// concept, and there is precious little alignment on the exact
// APIs that various programming languages have chosen. :)
// This is an example of how to adapt another flavour of enumerator
// (Rust's in this case) to Dafny's.
module RustStyleExample {

  import opened Frames
  import opened Wrappers
  import opened Enumerators

  // Roughly aligns with Rust's std::iter::Iterator trait.
  // https://doc.rust-lang.org/std/iter/trait.Iterator.html
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

  // Adapts from a Rust Iterator to an Enumerator.
  // Because the latter defines HasNext() as a pure predicate,
  // the adaptor needs to pre-fetch the next element eagerly.
  // An alternative approach is to extend Enumerator<Option<T>>
  // instead, in which case clients of the enumerator will need
  // to handle None values as well, likely by break-ing out of the
  // loop.
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
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(iter)
      && decr == (if this.next.None? then 0 else iter.Decreases() + 1)
    }

    method Next() returns (element: T) 
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      element := next.value;
      enumerated := enumerated + [element];

      next := iter.Next();
      if this.next.None? {
        decr := 0;
      } else {
        decr := iter.Decreases() + 1;
      }
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
      decreases Repr, 1
    {
      decr
    }

    predicate method HasNext() 
      reads Repr
      requires Valid()
      decreases Repr, 2
      ensures Decreases() == 0 ==> !HasNext()
    {
      next.Some?
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
      decreases Repr, 0
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
    while (enum.HasNext()) 
      invariant enum.Valid() && fresh(enum.Repr)
      decreases enum.Decreases()
    {
      var element := enum.Next();

      print element, "\n";
    }
  }
}