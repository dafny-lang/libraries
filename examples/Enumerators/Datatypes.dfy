// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "Enumerators.dfy"

// An example of an enumerator that traverses the sub-values in 
// an algebraic datatype value.
module DatatypeEnumerator {

  import opened Enumerators
  
  // TODO: A TreeEnumerator would be much more interesting!
  // Show how to implement multiple traversal options, probably
  // using ConcatEnumerator for child paths.

  // TODO: Could define a Enumerable<T> trait as well, although datatypes
  // can't yet implement that anyway.
  datatype List<T> = Cons(value: T, tail: List<T>) | Nil {
    method Enumerator() returns (e: Enumerator<T>) 
      ensures e.Valid()
      ensures fresh(e.Repr)
    {
      e := new ListEnumerator(this);
    }
  }

  class ListEnumerator<T> extends Enumerator<T> {

    var next: List<T>

    constructor(next: List<T>) 
      ensures Valid()
      ensures fresh(Repr - {this})
    {
      this.next := next;

      enumerated := [];
      Repr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
      decreases Repr, 1
    {
      // TODO: This is where I wish I could just say "next" and 
      // rely on the well-founded ordering.
      Length(next)
    }


    static function Length(l: List<T>): nat {
      match l
      case Cons(_, tail) => 1 + Length(tail)
      case Nil => 0
    }

    predicate method HasNext() 
      reads Repr
      requires Valid()
      decreases Repr, 2
      ensures Decreases() == 0 ==> !HasNext()
    {
      next.Cons?
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
      next := next.tail;

      enumerated := enumerated + [element];
    }
  }

  method Main() {
    var list := Cons(1, Cons(2, Cons(3, Cons(4, Cons(5, Nil)))));

    var e := list.Enumerator();
    while e.HasNext()
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var x := e.Next();

      print x;
    }
  }
}