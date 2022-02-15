
include "Loopers.dfy"

module IteratorAdaptorExample {

  import opened Loopers

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

  class SeqIteratorEnumerator<T(0)> extends Enumerator<T> {

    const iter: SeqIterator<T>
    var done: bool

    ghost const original: seq<T>
    ghost var decr: nat

    constructor(s: seq<T>) 
      ensures Valid() 
      ensures fresh(Repr) 
    {
      iter := new SeqIterator(s);
      original := s;
      enumerated := [];
      
      new;

      // Calling MoveNext() right away ensures we only enumerate yielded state.
      var more := iter.MoveNext();
      done := !more;
      
      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
      decr := |iter.s| - |enumerated|;
      assert !done ==> iter.elements < iter.s; 
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
      && (!done ==> enumerated + [iter.element] == iter.elements)
      && (done ==> enumerated == iter.elements)
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

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr) 
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];

      var more := iter.MoveNext();
      done := !more;
      
      assert iter._new == {};

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
      assert (!done ==> iter.Valid());
      assert (!done ==> enumerated + [iter.element] == iter.elements);
      assert (done ==> enumerated == iter.elements);
      assert !done ==> iter.elements < iter.s; 
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
    {
      iter.element
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid() 
    {
      decr
    }
  }
}