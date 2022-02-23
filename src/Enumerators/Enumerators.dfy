// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../Frames.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module Enumerators {

  import opened Frames
  import opened Wrappers
  import opened Seq


  // A trait for any value that produces a finite set of value.
  trait {:termination false} Enumerator<T> extends Validatable {
    
    // The Valid() predicate from the Validatable trait ends up
    // becoming the "enumeration invariant", which in turn becomes
    // the loop invariant in a while loop that uses an enumerator.

    // All values produced by the Next() method in the order they
    // were produced.
    ghost var enumerated: seq<T>

    // Any enumerator that produces one value at a time
    // and provably terminates is equivalent to an enumerator
    // that produces a specific seq<T>. This value may be underspecified
    // such that it is not known, even its length, until after all
    // values have been produced.
    // Dafny doesn't let you pass around an underspecified value though,
    // so we don't define a "to be enumerated" field or function.
    
    // The termination measure for the enumerator. Must decrease on every
    // call to Next().
    //
    // Would be better as an arbitrary termination clause somehow instead,
    // but we don't have language-level access to the built-in well-founded
    // ordering. See https://github.com/dafny-lang/dafny/issues/762.
    function Decreases(): nat
      reads Repr
      decreases Repr, 1
      requires Valid()

    // Pre-condition for Next(). Making this a pure predicate means that
    // enumerators have to at least know ahead of time if they are able to
    // produce a value, even if they do not know what value it is until
    // Next() is invoked. This avoids forcing the type parameter for any
    // enumerator to satisfy the Auto-initializable type characteristic (0),
    // and allows for much cleaner assertions about state and invariants.
    // When this is overly restrictive, having an enumerator produce a wrapper
    // such as Option<T> instead is a good option (ha!), with the caveat that
    // client code will need to skip over Nones. 
    predicate method HasNext() 
      reads Repr
      requires Valid()
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0

    method Next() returns (element: T)
      requires Valid()
      requires HasNext()
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
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
  }

  class SeqEnumerator<T> extends Enumerator<T> {

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
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
      && 0 <= index <= |elements|
      && enumerated == elements[0..index]
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
      decreases Repr, 1
    {
      |elements| - index
    }

    predicate method HasNext() 
      reads Repr
      requires Valid()
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0
      ensures !HasNext() ==> enumerated == elements
    {
      index < |elements|
    }

    method Next() returns (element: T)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      element := elements[index];
      enumerated := enumerated + [element];
      index := index + 1;
    }
  }

  // This encapsulates the canonical method for enumerating
  // the values in a set by using :| and set subtraction.
  // Enumerating a set this way will generally take quadratic time, however,
  // given each set subtraction will normally require making a new copy of
  // the set at runtime.
  //
  // The good news is that if the Enumerator concept, or a generalized
  // type characteristic it satisfies, is added to Dafny itself, then
  // the various runtimes can provide a much more efficient implementation
  // of this enumerator based on iteration features in the underlying set
  // implementation.
  class SetEnumerator<T(==)> extends Enumerator<T> {
    ghost const original: set<T>
    var remaining: set<T>

    constructor(s: set<T>) 
      ensures Valid() 
      ensures fresh(Repr)
      ensures enumerated == []
      ensures original == s
    {
      this.original := s;
      this.remaining := s;

      enumerated := [];
      Repr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && multiset(enumerated) + multiset(remaining) == multiset(original)
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
      decreases Repr, 1
    {
      |remaining|
    }
    
    predicate method HasNext()
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0
    {
      |remaining| > 0
    }

    method Next() returns (element: T)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      var picked: T :| picked in remaining;
      element := picked;
      remaining := remaining - {element};
      enumerated := enumerated + [element];
    }
  }

  class MappingEnumerator<T, R> extends Enumerator<R> {
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
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && enumerated == Seq.Map(f, wrapped.enumerated)
    }

    predicate method HasNext()
      reads Repr
      requires Valid()
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0
    {
      assert wrapped.HasNext() ==> Decreases() > 0;
      wrapped.HasNext()
    }

    method Next() returns (element: R)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      var t := wrapped.Next();
      element := f(t);
      enumerated := enumerated + [element];
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
      decreases Repr, 1
    {
      wrapped.Decreases()
    }
  }

  class ConcatEnumerator<T> extends Enumerator<T> {

    const first: Enumerator<T>
    const second: Enumerator<T>

    constructor(first: Enumerator<T>, second: Enumerator<T>)
      requires first.Valid() && first.enumerated == []
      requires second.Valid() && second.enumerated == []
      requires first.Repr !! second.Repr
      ensures Valid() 
      ensures fresh(Repr - first.Repr - second.Repr) 
      ensures this.first == first
      ensures this.second == second
    {
      this.first := first;
      this.second := second;
      
      enumerated := first.enumerated + second.enumerated;
      Repr := {this} + first.Repr + second.Repr;
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && (first.HasNext() ==> second.enumerated == [])
      && enumerated == first.enumerated + second.enumerated
    }

    predicate method HasNext()
      requires Valid()
      reads this, Repr
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0
    {
      assert first.HasNext() ==> Decreases() > 0;
      assert second.HasNext() ==> Decreases() > 0;
      first.HasNext() || second.HasNext()
    }

    method Next() returns (element: T)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      if first.HasNext() {
        element := first.Next();
        assert first.Decreases() < old(first.Decreases());
      } else {
        element := second.Next();
        assert second.Decreases() < old(second.Decreases());
      }

      Repr := {this} + first.Repr + second.Repr;
      enumerated := enumerated + [element];
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid() 
      decreases Repr, 1
    {
      first.Decreases() + second.Decreases()
    }
  }

  // Note that to satisfy the Enumerator API, this enumerator has
  // to eagerly fetch the next value to return from Next().
  // An alternative is to use a MappingEnumerator that maps to Option<T>
  // values, and having consumers skip None values.
  class FilteredEnumerator<T> extends Enumerator<T> {
    const wrapped: Enumerator<T>
    const filter: T -> bool
    var next: Option<T>

    constructor(wrapped: Enumerator<T>, filter: T -> bool) 
      requires wrapped.Valid()
      requires wrapped.enumerated == []
      modifies wrapped.Repr
      ensures Valid()
      ensures fresh(Repr - old(wrapped.Repr))
      ensures enumerated == []
      ensures this.wrapped == wrapped
      ensures this.filter == filter
    {
      this.wrapped := wrapped;
      this.filter := filter;
      this.next := None;
      Repr := {this} + wrapped.Repr;
      enumerated := [];

      new;
      
      FindNext();
    }

    predicate AlmostValid()
      reads this, Repr
      ensures AlmostValid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && (if next.Some? then enumerated + [next.value] else enumerated) == Seq.Filter(filter, wrapped.enumerated)
    }

    predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && AlmostValid()
      && (next.None? ==> !wrapped.HasNext())
    }

    predicate method HasNext()
      reads Repr
      requires Valid()
      decreases Repr, 2
      ensures HasNext() ==> Decreases() > 0
      ensures !HasNext() ==> !wrapped.HasNext()
    {
      assert if next.Some? then Decreases() >= 1 else true;
      next.Some?
    }

    method Next() returns (element: T)
      requires Valid()
      requires HasNext()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]
    {
      element := next.value;
      enumerated := enumerated + [element];
      next := None;

      FindNext();
    }

    method FindNext() 
      requires AlmostValid()
      requires next.None?
      modifies Repr
      decreases Repr, 0
      ensures Valid()
      ensures Decreases() <= old(wrapped.Decreases() + (if next.Some? then 1 else 0))
      ensures unchanged(this`enumerated)
      ensures unchanged(this`Repr)
    {
      while (wrapped.HasNext() && next.None?)
        invariant AlmostValid()
        invariant wrapped.Repr < old(Repr)
        invariant Repr == old(Repr)
        invariant unchanged(this`enumerated)
        invariant wrapped.Decreases() + (if next.Some? then 1 else 0) <= old(wrapped.Decreases() + (if next.Some? then 1 else 0))
        decreases wrapped.Decreases()
      {
        var wrappedEnumeratedBefore := wrapped.enumerated;
        // This is where it is very difficult to prove termination if we
        // allow wrapped.Repr to potentially grow, because the assertion
        // we must satisfy for the recursive call to be allowed is actually
        // wrapped.Repr < old(Repr). That means updating Repr after this call
        // wouldn't help.
        var t := wrapped.Next();
        reveal Seq.Filter();
        LemmaFilterDistributesOverConcat(filter, wrappedEnumeratedBefore, [t]);
          
        if filter(t) {
          next := Some(t);
        }
      }
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid()
      decreases Repr, 1
    {
      // If we could declare semi-arbitrary values as in decreases clauses,
      // this could just be (wrapped.Decreases(), next)
      wrapped.Decreases() + (if next.Some? then 1 else 0)
    }
  }

  method Fold<T, A>(f: (A, T) -> A, init: A, e: Enumerator<T>) returns (result: A)
    requires e.Valid()
    requires e.enumerated == []
    modifies e.Repr
    ensures e.Valid()
    ensures !e.HasNext()
    ensures result == Seq.FoldLeft(f, init, e.enumerated)
  {
    reveal Seq.FoldLeft();
    result := init;
    while (e.HasNext())
      invariant e.Valid() && e.Repr <= old(e.Repr)
      decreases e.Decreases()

      invariant result == Seq.FoldLeft(f, init, e.enumerated)
    {
      ghost var enumeratedBefore := e.enumerated;
      var element := e.Next();
      result := f(result, element);

      Seq.LemmaFoldLeftDistributesOverConcat(f, init, enumeratedBefore, [element]);
    }
  }

  method CollectToSeq<T>(e: Enumerator<T>) returns (result: seq<T>)
    requires e.Valid()
    // TODO: Might remove these
    requires e.enumerated == []
    modifies e.Repr
    ensures e.Valid()
    ensures !e.HasNext()
    ensures result == e.enumerated
  {
    result := [];
    while (e.HasNext())
      invariant e.Valid() && e.Repr <= old(e.Repr)
      decreases e.Decreases()

      invariant result == e.enumerated
    {
      var element := e.Next();
      result := result + [element];
    }

    // TODO: Figure out how to use Fold instead. Good case study for invariant support!
    // var f := (s, x) => s + [x];
    // result := Fold(f, [], e);
    // Seq.LemmaInvFoldLeft(???, (s, x, s') => s + x == s', f, [], []);
  }
}