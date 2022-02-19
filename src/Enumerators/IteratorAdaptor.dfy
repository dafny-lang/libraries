
include "Enumerators.dfy"
include "../Wrappers.dfy"

module IteratorAdaptorExample {


  import opened Enumerators
  import opened Wrappers
  iterator RangeIterator(start: int, end: int) yields (element: int)
    requires start <= end
    yield ensures element - start + 1 == |elements|
    ensures |elements| == end - start
  {
    for i := start to end
      invariant i - start == |elements|
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
      
      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
      && iter in Repr
      && this !in iter._modifies
      && this !in iter._reads
      && this !in iter._new
      && iter._modifies <= Repr
      && iter._reads <= Repr
      && iter._new <= Repr
      && (remaining > 0 ==> iter.Valid())
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
      remaining := remaining - 1;

      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
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