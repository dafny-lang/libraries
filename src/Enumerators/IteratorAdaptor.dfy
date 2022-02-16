
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
    var done: bool

    ghost const original: seq<T>
    ghost var decr: nat

    constructor(s: seq<T>) 
      ensures Valid() 
      ensures fresh(Repr) 
    {
      iter := new SeqIterator(s);
      done := false;
      original := s;
      enumerated := [];
      
      new;
      
      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
      decr := |iter.s| - |enumerated|;
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && iter in Repr
      && this !in iter._modifies
      && this !in iter._reads
      && this !in iter._new
      && iter._modifies <= Repr
      && iter._reads <= Repr
      && iter._new <= Repr
      && (!done ==> iter.Valid())
      && (!done ==> iter.elements < iter.s)
      && decr == |iter.s| - |enumerated|
    } 

    predicate method Done()
      requires Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
    {
      done
    }

    method Next() returns (element: Option<T>)
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr) 
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      
      var more := iter.MoveNext();
      if more {
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
    {
      decr
    }
  }
}