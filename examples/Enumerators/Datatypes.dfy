
include "Enumerators.dfy"

module DatatypeEnumerator {

  import opened Enumerators
  
  // Implicit trait approach
  datatype List<T> = Cons(value: T, tail: List<T>) | Nil {
    method Enumerator() returns (e: Enumerator<T>) {
      e := new ListEnumerator(this);
    }

    function Length(): nat {
      match this
      case Cons(_, tail) => 1 + tail.Length()
      case Nil => 0
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
      decreases Repr
    {
      && this in Repr
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
    {
      // This is where I wish I could just say "next" and 
      // rely on the well-founded ordering.
      next.Length()
    }

    predicate method HasNext() 
      reads Repr
      requires Valid()
      decreases Repr, 0
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
}