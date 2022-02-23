
include "../../src/Enumerators/Enumerators.dfy"
include "../../src/Wrappers.dfy"

// Dafny iterators do not share any common supertype, so there isn't
// currently any way to write a single adaptor from an arbitrary
// iterator to the Enumerator<T> trait. However, this example should
// serve as a template for adapting any specific iterator.
//
// In practice, a loop that uses a specific iterator type will need to
// declare a "decreases" termination metric, and hence the iterator
// in question will need at least one "yield ensures" clause to
// support such a metric. The same is true for adapting a specific iterator
// to the Enumerator<T> trait in order to implement the Decreases() function.
module IteratorAdaptorExample {

  import opened Enumerators
  import opened Wrappers
  
  iterator RangeIterator(start: int, end: int) yields (element: int)
    requires start <= end
    // This is necessary in order to prove termination via Decreases()
    yield ensures element - start + 1 == |elements|
    // This is necessary to prove the Repr <= old(Repr) post-condition
    // of Next(). Iterators that instantiate and "hand off" objects
    // will need a weaker post-condition.
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