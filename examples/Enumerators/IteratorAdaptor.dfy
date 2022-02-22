
include "Enumerators.dfy"
include "../Wrappers.dfy"

module IteratorAdaptorExample {

  import opened Enumerators
  import opened Wrappers

  iterator RangeIterator(start: int, end: int) yields (element: int)
    requires start <= end
    yield ensures element - start + 1 == |elements|
    yield ensures _new == {};
    ensures |elements| == end - start
  {
    for i := start to end
      invariant i - start == |elements|
      invariant _new == {}
    {
      yield i;
    }
  }

  class RangeEnumerator extends Enumerator<int> {

    const iter: RangeIterator
    var remaining: nat

    constructor(start: int, end: int) 
      requires start <= end
      ensures Valid() 
      ensures fresh(Repr) 
    { 
      iter := new RangeIterator(start, end);
      remaining := end - start;
      enumerated := [];
      
      new;
      
      Repr := {this, iter};
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
      && iter in Repr
      && iter._modifies + iter._reads + iter._new == {}
      && iter.Valid()
      && remaining == (iter.end - iter.start) - |iter.elements|
    } 

    predicate method HasNext()
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0
    {
      remaining > 0
    }

    method Next() returns (element: int)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr) 
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      var more := iter.MoveNext();
      element := iter.element;
      enumerated := enumerated + [element];
      remaining := remaining - 1;
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid()
      decreases Repr, 1
    {
      remaining
    }
  }
}