
include "../Wrappers.dfy"
include "../Frames.dfy"
include "../Collections/Sequences/Seq.dfy"

module Enumerators {

  import opened Wrappers
  import opened Frames
  import opened Seq

  // An invariant that constrains what Next() can return,
  // based on the previously enumerated elements.
  // Used to express possibly incomplete knowledge about the enumerator's behavior,
  // without needing to know the concrete class of the enumerator
  // or read any of its fields.
  type EnumerationInvariant<!T> = (seq<T>, Option<T>) -> bool

  trait {:termination false} Enumerator<T> extends Validatable {
    
    ghost var enumerated: seq<T>

    ghost const inv: EnumerationInvariant<T>

    ghost method Enumerated(element: Option<T>)
      modifies this`enumerated
      ensures element.Some? ==> enumerated == old(enumerated) + [element.value]
      ensures element.None? ==> unchanged(`enumerated)
    {
      if element.Some? {
        enumerated := enumerated + [element.value];
      }
    }

    // The termination measure for the enumerator. Must decrease on every
    // call to Next() that doesn't return None.
    //
    // Would be better as an arbitrary termination clause somehow instead,
    // but we don't have language-level access to the built-in well-founded
    // ordering. See https://github.com/dafny-lang/dafny/issues/762.
    // TODO: Rename since this isn't 1:1 with decreases clauses, possibly "Remaining"
    function Decreases(): nat
      reads Repr
      decreases Repr, 1
      requires Valid()

    // TODO: Done() alias for Decreases() == 0?

    method Next() returns (element: Option<T>)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      // This is more restrictive than the usual post-condition of
      // Validatable.ValidAndDisjoint(), because if we allow the Repr
      // of an enumerator to grow, even if fresh, it becomes much more
      // difficult to prove termination of a wrapper enumerator like
      // FilteredEnumerator below which needs to make a recursive call to
      // Next() inside a loop. 
      ensures Repr <= old(Repr)
      ensures inv(old(enumerated), element)
      ensures element.Some? ==> (
        && Decreases() < old(Decreases())
        && enumerated == old(enumerated) + [element.value]
      )
      ensures element.None? ==> (
        && Decreases() == 0
        && enumerated == old(enumerated)
      )
  }

  class SeqEnumerator<T(==)> extends Enumerator<T> {

    const elements: seq<T>
    var index: nat

    constructor(s: seq<T>) 
      ensures Valid()
      ensures fresh(Repr - {this})
      ensures enumerated == []
      ensures elements == s
    {
      elements := s;
      index := 0;
      
      enumerated := [];
      Repr := {this};
      inv := (sofar, next: Option<T>) => (
        match next
        case Some(x) => sofar + [x] <= s
        case None => sofar == s
      );
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
      && 0 <= index <= |elements|
      && enumerated == elements[0..index]
      && inv == (sofar, next: Option<T>) => (
        match next
        case Some(x) => sofar + [x] <= elements
        case None => sofar == elements
      )
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
      decreases Repr, 1
    {
      |elements| - index
    }

    method Next() returns (element: Option<T>)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures inv(old(enumerated), element)
      ensures element.Some? ==> (
        && Decreases() < old(Decreases())
        && enumerated == old(enumerated) + [element.value]
      )
      ensures element.None? ==> (
        && Decreases() == 0
        && enumerated == old(enumerated)
      )
    {
      if index < |elements| {
        element := Some(elements[index]);
        index := index + 1;
      } else {
        element := None;
        assert enumerated == elements;
      }
      Enumerated(element);
    }
  }

  class MappingEnumerator<T(!new), R> extends Enumerator<R> {
    const wrapped: Enumerator<T>
    const f: T -> R

    constructor(f: T -> R, wrapped: Enumerator<T>) 
      requires wrapped.Valid()
      requires wrapped.enumerated == []
      ensures Valid() 
      ensures fresh(Repr - wrapped.Repr)
      ensures enumerated == []
      ensures this.wrapped == wrapped
      ensures this.f == f
    {
      this.wrapped := wrapped;
      this.f := f;
      Repr := {this} + wrapped.Repr;
      enumerated := [];
      inv := (sofar, next: Option<R>) => (
        && exists wrappedSofar :: 
          && sofar == Seq.Map(f, wrappedSofar)
          && match next
             case Some(r) => exists t :: r == f(t) && wrapped.inv(wrappedSofar, Some(t))
             case None => wrapped.inv(wrappedSofar, None)
      );
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && enumerated == Seq.Map(f, wrapped.enumerated)
      && inv == (sofar, next: Option<R>) => (
        && exists wrappedSofar :: 
          && sofar == Seq.Map(f, wrappedSofar)
          && match next
             case Some(r) => exists t :: r == f(t) && wrapped.inv(wrappedSofar, Some(t))
             case None => wrapped.inv(wrappedSofar, None)
      )
    }

    method Next() returns (element: Option<R>)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures inv(old(enumerated), element)
      ensures element.Some? ==> (
        && Decreases() < old(Decreases())
        && enumerated == old(enumerated) + [element.value]
      )
      ensures element.None? ==> (
        && Decreases() == 0
        && enumerated == old(enumerated)
      )
    {
      var optT := wrapped.Next();
      match optT
      case Some(t) => {
        element := Some(f(t));
        Enumerated(element);
      }
      case None => {
        element := None;
        Enumerated(element);
      }
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
      decreases Repr, 1
    {
      wrapped.Decreases()
    }
  }

  ghost predicate EnumeratesThisMany<T(!new)>(e: Enumerator<T>, n: nat) {
    forall sofar :: e.inv(sofar, None) ==> |sofar| == n
  }

  ghost predicate Enumerates<T(!new)>(e: Enumerator<T>, s: seq<T>) {
    forall sofar :: e.inv(sofar, None) ==> sofar == s
  }

  method MapEnumerator<T(!new), R>(f: T -> R, e: Enumerator<T>) returns (e': Enumerator<R>) 
    requires e.Valid()
    requires e.enumerated == []
    ensures (e'.inv == (sofar: seq<R>, next: Option<R>) => (
        && exists wrappedSofar :: 
          && sofar == Seq.Map(f, wrappedSofar)
          && match next
             case Some(r) => exists t :: r == f(t) && e.inv(wrappedSofar, Some(t))
             case None => e.inv(wrappedSofar, None)))
  {
    e' := new MappingEnumerator(f, e);
  }

  method Main() {
    var e: Enumerator<int> := new SeqEnumerator([1, 2, 3, 4, 5]);
    assert EnumeratesThisMany(e, 5);
    assert Enumerates(e, [1, 2, 3, 4, 5]);

    var f := (x: int) => x + 2;
    var e': Enumerator<int> := MapEnumerator(f, e);
    assert EnumeratesThisMany(e', 5);

    assert forall y :: exists x | y == f(x) :: x == y - 2;
    assert Enumerates(e, [3, 4, 5, 6, 7]);
  }
}