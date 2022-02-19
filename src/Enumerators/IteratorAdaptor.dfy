
include "Enumerators.dfy"
include "../Wrappers.dfy"

module IteratorAdaptorExample {


  import opened Enumerators
  import opened Wrappers
  iterator SeqIterator<T(0)>(s: seq<T>) yields (element: T)
    yield ensures elements <= s
    ensures elements == s
  {
    for i := 0 to |s|
      invariant i == |elements|
      invariant elements <= s
    {
      yield s[i];
    }
  }

  class SeqIteratorEnumerator<T(0)> extends Enumerator<Option<T>> {

    const iter: SeqIterator<T>
    var hasNext: bool

    ghost const original: seq<T>
    ghost var decr: nat

    constructor(s: seq<T>) 
      ensures Valid() 
      ensures fresh(Repr) 
    { 
      iter := new SeqIterator(s);
      hasNext := true;
      original := s;
      enumerated := [];
      
      new;
      
      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
      decr := |iter.s| - |enumerated|;

      assert this in Repr;
      assert iter in Repr;
      assert this !in iter._modifies;
      assert this !in iter._reads;
      assert this !in iter._new;
      assert iter._modifies <= Repr;
      assert iter._reads <= Repr;
      assert iter._new <= Repr;
      assert (hasNext ==> iter.Valid());
      assert (hasNext ==> iter.elements < iter.s);
      // assert decr == |iter.s| - |enumerated|;
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
      && (hasNext ==> iter.Valid())
      && (hasNext ==> iter.elements < iter.s)
      && decr == |iter.s| - |enumerated|
    } 

    predicate method HasNext()
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0
    {
      hasNext
    }

    method Next() returns (element: Option<T>)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr) 
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      
      hasNext := iter.MoveNext();
      if hasNext {
        element := Some(iter.element);
      } else {
        element := None;
      }

      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
      decr := |iter.s| - |enumerated|;
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid()
      decreases Repr, 1
    {
      decr 
    }
  }
}