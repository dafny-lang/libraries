include "Wrappers.dfy"
include "Frames.dfy"

module Actions {  

  import opened Wrappers
  import opened Frames

  // TODO: Unfortunately, would be good to have Action0 up to ActionN for
  // some small N. Maybe also M for number of returns.
  // Using () is SUPER awkward with Dafny syntax. An action with
  // no arguments or return using unit looks like:
  // var _ := runnable.Invoke(());
  trait {:termination false} Action<A, R> extends Validatable
  {
    method Invoke(a: A) returns (r: R)
      requires Valid()
      requires Requires(a)
      modifies Modifies(a)
      decreases Decreases(a)
      ensures ValidAndDisjoint()
      ensures old(allocated(r)) && Ensures(a, r)

    predicate Requires(a: A)
    // Need this separately from Repr for callers
    // Repr is the frame for Valid(), but callers
    // need to know what ELSE gets modified.
    function Modifies(a: A): set<object> requires Requires(a)
    function Decreases(a: A): nat
    predicate Ensures(a: A, r: R)
  }

  // TODO: ArrayCollector will be more interesting, to track capacity
  class SeqCollector<T> extends Action<T, ()> {

    var elements: seq<T>

    predicate Valid() reads this, Repr {
      true
    }

    method Invoke(t: T) returns (nothing: ()) 
      requires Valid()
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t)
      ensures ValidAndDisjoint()
      ensures old(allocated(())) && Ensures(t, ())
    {
      elements := elements + [t];
    }

    predicate Requires(t: T) {
      true
    }

    function Modifies(t: T): set<object> {
      {this}
    }

    function Decreases(t: T): nat {
      0
    }

    predicate Ensures(t: T, nothing: ()) {
      true
    }
  }

  class FunctionAsAction<T, R> extends Action<T, R> {
    const f: T ~> R
    const e: (T, R) ~> bool

    constructor(f: T ~> R, e: (T, R) ~> bool) {
      this.f := f;
      this.e := e;
    }

    predicate Valid() reads this, Repr {
      // TODO: This is what we want but can't because we're not using (!new)
      // forall t: T :: e(t, f(t))
      true
    }

    method Invoke(t: T) returns (r: R) 
      requires Valid()
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t)
      ensures ValidAndDisjoint()
      ensures old(allocated(r)) && Ensures(t, r)
    {
      r := f(t);
    }

    predicate Requires(t: T) {
      f.requires(t)
    }

    function Modifies(t: T): set<object> {
      {}
    }

    function Decreases(t: T): nat {
      0
    }

    predicate Ensures(t: T, r: R) {
      e(t, r)
    }
  }

  class ComposedAction<T, M, R> extends Action<T, R> {
    const inner: Action<T, M>
    const outer: Action<M, R>

    constructor(inner: Action<T, M>, outer: Action<M, R>) {
      this.inner := inner;
      this.outer := outer;
    }

    predicate Valid() reads this, Repr {
      true
    }

    method Invoke(t: T) returns (r: R) 
      requires Valid()
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t)
      ensures ValidAndDisjoint()
      ensures old(allocated(r)) && Ensures(t, r)
    {
      var m := inner.Invoke(t);
      r := outer.Invoke(m);
    }

    predicate Requires(t: T) {
      inner.Requires(t)
    }

    function Modifies(t: T): set<object> {
      set m: M, o: object | inner.Ensures(t, m) && o in outer.Modifies(m) :: o
    }

    function Decreases(t: T): nat {
      inner.Decreases(t)
    }

    predicate Ensures(t: T, r: R) {
      exists m: M :: inner.Ensures(t, m) && outer.Ensures(m, r)
    }
  }

  class InvokeAction extends Action<Action<int, ()>, ()> {

    predicate Valid() reads this, Repr {
      true
    }

    method Invoke(a: Action<int, ()>) returns (nothing: ()) 
      requires Valid()
      requires Requires(a)
      modifies Modifies(a)
      decreases Decreases(a)
      ensures ValidAndDisjoint()
      ensures Ensures(a, ())
    {
      var _ := a.Invoke(42);
    }

    predicate Requires(a: Action<int, ()>) {
      a.Decreases(42) < Decreases(a)
    }

    function Modifies(a: Action<int, ()>): set<object> requires Requires(a) {
      a.Modifies(42)
    }

    function Decreases(a: Action<int, ()>): nat {
      0
    }

    predicate Ensures(a: Action<int, ()>, nothing: ()) {
      true
    }
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
      ensures |pending| == |old(pending)| - 1
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
      decreases |e.pending|
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