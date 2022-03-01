// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

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
    // These are necessary in order to prove termination via Decreases()
    yield ensures |elements| <= end - start
    ensures |elements| == end - start
    // These are necessary to prove the Repr <= old(Repr) post-condition
    // of Next(). Iterators that instantiate and "hand off" objects
    // will need weaker post-conditions.
    yield ensures _new == {}
    ensures _new == {}
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
    var iterDone: bool
    var remaining: nat

    constructor(start: int, end: int) 
      requires start <= end
      ensures Valid() 
      ensures fresh(Repr) 
    { 
      iter := new RangeIterator(start, end);
      remaining := end - start;
      iterDone := false;
      enumerated := [];
      Repr := {this, iter};
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
      && iter in Repr
      && iter._modifies == iter._reads == iter._new == {}
      && (!iterDone ==> iter.Valid())
      && (iterDone ==> remaining == 0)
      && remaining == (iter.end - iter.start) - |iter.elements|
    } 

    method Next() returns (element: Option<int>)
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
      if iterDone {
        element := None;
      } else {
        var more := iter.MoveNext();
        if more {
          element := Some(iter.element);
          remaining := remaining - 1;
        } else {
          iterDone := true;
          element := None;
        }
      }
      
      Enumerated(element);
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