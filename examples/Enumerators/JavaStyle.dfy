// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/Frames.dfy"
include "../../src/Wrappers.dfy"
include "Enumerators.dfy"

// There are lots of ways to define an Iterator/Enumerator
// concept, and there is precious little alignment on the exact
// APIs that various programming languages have chosen. :)
// This is an example of how to adapt another flavour of enumerator
// (Java's in this case) to Dafny's.
module JavaStyleExample {

  import opened Frames
  import opened Wrappers
  import opened Enumerators

  // Roughly aligns with Java's Iterator interface.
  trait JavaStyleIterator<T> extends Validatable {

    method HasNext() returns (result: bool)
      requires Valid()
      ensures !result <==> Decreases() == 0

    method Next() returns (res: T)
      requires Valid()
      requires Decreases() > 0
      modifies Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())

    function Decreases(): nat
      reads Repr
      requires Valid()
  }

  // Adapts from a Java Iterator to an Enumerator.
  class JavaStyleIteratorEnumerator<T> extends Enumerator<T> {

    const iter: JavaStyleIterator<T>

    constructor(iter: JavaStyleIterator<T>)
      requires iter.Valid()
      modifies iter.Repr
      ensures Valid()
      ensures iter.Repr <= old(iter.Repr)
      ensures Repr == {this} + iter.Repr
    {
      this.iter := iter;
      Repr := {this} + iter.Repr;
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(iter)
    }

    method Next() returns (element: Option<T>) 
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures ienumerated == old(ienumerated) + [element]
      ensures element.Some? ==> (
        && Decreases() < old(Decreases())
        && enumerated == old(enumerated) + [element.value]
      )
      ensures element.None? ==> (
        && Decreases() == 0
        && enumerated == old(enumerated)
      )
    {
      var hasNext := iter.HasNext();
      if hasNext {
        var value := iter.Next();
        element := Some(value);
      } else {
        element := None;
      }
      Enumerated(element);
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
      decreases Repr, 1
    {
      iter.Decreases()
    }
  }

  class SeqJavaStyleIterator<T> extends JavaStyleIterator<T> {

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

    method HasNext() returns (result: bool) 
      requires Valid()
      ensures !result <==> Decreases() == 0
    {
      return |s| > 0;
    }

    method Next() returns (res: T)
      requires Valid()
      requires Decreases() > 0
      modifies Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
    {
      res := s[0];
      s := s[1..];
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
    {
      |s|
    }
  }

  method Main() {
    var iter := new SeqJavaStyleIterator([1,2,3,4,5]);

    var enum: Enumerator<int> := new JavaStyleIteratorEnumerator(iter);
    while true
      invariant enum.Valid() && fresh(enum.Repr)
      decreases enum.Decreases()
    {
      var element := enum.Next();
      if element.None? { break; }

      print element.value, "\n";
    }
  }
}