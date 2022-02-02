include "Wrappers.dfy"

module Actions {  

  import opened Wrappers

  trait {:termination false} Action<A, R>
  {
    method Invoke(a: A) returns (r: R)
      requires Requires(a)
      modifies Modifies(a)
      ensures old(allocated(r)) && Ensures(a, r)

    predicate Requires(a: A)
    function Modifies(a: A): set<object>
    twostate predicate Ensures(a: A, r: R)
  }

  type IEnumeration<T> = Action<(), T>

  // predicate Enumerates<T>(e: IEnumeration<T>, elements: seq<T>) {
  //   e.Ensures((), elements[0])
  // }

  trait IEnumerator<T> {
    ghost var pending: seq<T>
    ghost var Repr: set<object>

    predicate Valid() reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr

    method Next() returns (t: T)
      requires Valid()
      requires |pending| > 0
      modifies Repr
      ensures Valid()
      ensures t == old(pending)[0]
      ensures pending == old(pending)[1..]
  }

  trait Enumerator<T> {
    ghost var pending: seq<T>
    ghost var Repr: set<object>

    predicate Valid() reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr

    method Next() returns (t: Option<T>)
      requires Valid()
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures |old(pending)| > 0 ==>
        && t.Some?
        && t.value == old(pending)[0]
        && pending == old(pending)[1..]
      ensures |old(pending)| == 0 ==>
        && t.None?
        && unchanged(this)
  }

  trait MyEnumerator<T> extends IEnumerator<T> {

  }

  iterator SeqIterator<T(0)>(s: seq<T>) yields (t: T) {
    for i := 0 to |s| {
      yield s[i];
    }
  }

  class SeqEnumerator<T> extends MyEnumerator<T> {

    var elements: seq<T>

    constructor(s: seq<T>) {
      pending := s;
      elements := s;
      Repr := {this};
    }

    predicate Valid() reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
      && pending == elements
    }

    method Next() returns (t: T)
      requires Valid()
      requires |pending| > 0
      modifies Repr
      ensures Valid()
      ensures fresh(Repr - old(Repr))
      ensures t == old(pending)[0]
      ensures pending == old(pending)[1..]
      ensures |pending| == |old(pending)| + 1
    {
      t := elements[0];
      elements := elements[1..];
      pending := elements;
    }
  }

  method Count<T>(e: Enumerator<T>) returns (count: int) 
    requires e.Valid()
    modifies e.Repr
    decreases *
    ensures count == |e.pending|
  {
    count := 0;
    var next := e.Next();
    if next.None? {
      return;
    }
    count := count + 1;
    while next.Some? 
      invariant e.Valid()
      invariant fresh(e.Repr - old(e.Repr))
      invariant count + |e.pending| == |old(e.pending)|
      decreases *
    {
      label before: next := e.Next();

      // assert |old@before(e.pending)| + 1 == |e.pending|;
      if next.Some? {
        count := count + 1;
      }
    }
    assert |e.pending| == 0;
  }
}