// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../Frames.dfy"
include "../Wrappers.dfy"
include "../Math.dfy"
include "../Collections/Sequences/Seq.dfy"

module Enumerators {

  import opened Frames
  import opened Wrappers
  import opened Seq
  import opened Math

  // A trait for any value that produces a potentially infinite sequence of values.
  trait {:termination false} IEnumerator<T> extends Validatable {

    // The Valid() predicate from the Validatable trait can be thought of
    // as the "enumeration invariant", which in turn becomes
    // the loop invariant in a while loop that uses an enumerator.

    // All values produced by the Next() method in the order they
    // were produced.
    // TODO: Is this actually useful?
    ghost var ienumerated: seq<T>

    method Next() returns (element: T)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures ienumerated == old(ienumerated) + [element]
  }

  class NatEnumerator extends IEnumerator<nat> {
    
    var next: nat
    
    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr, 0
    {
      && this in Repr
      && next == |ienumerated|
      && ienumerated == seq(|ienumerated|, i => i)
    }

    constructor() 
      ensures Valid()
      ensures fresh(Repr)
    {
      next := 0;
      Repr := {this};
      ienumerated := [];
    }

    method Next() returns (element: nat)
      requires Valid()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures ienumerated == old(ienumerated) + [element]
    {
      element := next;
      next := next + 1;

      ienumerated := ienumerated + [element];
    }
  }

  // A trait for any value that produces a finite sequence of values.
  trait {:termination false} Enumerator<T> extends IEnumerator<Option<T>> {
    
    ghost var enumerated: seq<T>

    ghost method Enumerated(element: Option<T>)
      modifies this`ienumerated, this`enumerated
      ensures ienumerated == old(ienumerated) + [element]
      ensures element.Some? ==> enumerated == old(enumerated) + [element.value]
      ensures element.None? ==> unchanged(`enumerated)
    {
      ienumerated := ienumerated + [element];
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
      // TODO: Package up the rest in a twostate predicate?
      ensures ienumerated == old(ienumerated) + [element]
      ensures element.Some? ==> (
        && Decreases() < old(Decreases())
        && enumerated == old(enumerated) + [element.value]
      )
      ensures element.None? ==> (
        && Decreases() == 0
        && enumerated == old(enumerated)
      )
  }

  /**********************************************************
  *
  *  Specializations
  *
  ***********************************************************/

  // TODO: These aren't actually what we need. They only assert
  // a property about the current state of an enumerator, but we need
  // to assert this property holds for the enumerator in the future
  // as well, as long as it stays Valid().
  //
  // An alternate that works is to make these traits with body-less
  // lemmas that must be proven by subclasses. That will cause an explosion
  // of concrete types, though, because (for example) the ConcatEnumerator<T>
  // can't dynamically decide to extend SizedEnumerator<T> whenever
  // its two children do, so it forces a separate SizedConcatEnumerator<T>
  // (which can't even share implementation by extending SizedEnumerator<T>)

  // TODO: Don't use "Size", implies sizeof() semantics
  ghost predicate Sized<T>(e: Enumerator<T>, count: nat) 
    reads e.Repr
    requires e.Valid()
  {
    e.Decreases() == 0 ==> |e.enumerated| == count
  }

  ghost predicate EnumeratesMultiset<T>(e: Enumerator<T>, enumerated: multiset<T>) 
    reads e.Repr
    requires e.Valid()
  {
    e.Decreases() == 0 ==> multiset(e.enumerated) == enumerated
  }

  ghost predicate EnumeratesSet<T>(e: Enumerator<T>, enumerated: set<T>) 
    reads e.Repr
    requires e.Valid()
  {
    e.Decreases() == 0 ==> multiset(e.enumerated) == multiset(enumerated)
  }

  ghost predicate EnumeratesSeq<T>(e: Enumerator<T>, enumerated: seq<T>) 
    reads e.Repr
    requires e.Valid()
  {
    e.Decreases() == 0 ==> e.enumerated == enumerated
  }
  
  /**********************************************************
  *
  *  Concrete implementations
  *
  ***********************************************************/

  // TODO: Some of these should be IEnumerator adaptors instead,
  // possibly with an Enumerator subclass specialization.

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

    ghost predicate Valid() 
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

    method Next() returns (element: Option<T>)
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
      if index < |elements| {
        element := Some(elements[index]);
        index := index + 1;
      } else {
        element := None;
      }
      Enumerated(element);
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
  // of EnumeratorOfSet<T> based on iteration features in the underlying set
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

    ghost predicate Valid() 
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
    
    method Next() returns (element: Option<T>)
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
      if |remaining| > 0 {
        var t :| t in remaining;
        element := Some(t);
        remaining := remaining - {t};
      } else {
        element := None;
      }
      Enumerated(element);
    }
  }

  /**********************************************************
  *
  *  Higher-order operations
  *
  ***********************************************************/

  // TODO: Great case study for maintaining known properties through this transformation.
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

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && enumerated == Seq.Map(f, wrapped.enumerated)
    }

    method Next() returns (element: Option<R>)
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

  lemma MappingEnumeratorPreservesLength<T, R>(e: MappingEnumerator<T, R>, count: nat) 
    requires e.Valid()
    requires Sized(e.wrapped, count)
    ensures Sized(e, count)
  {}

  // TODO: Generalize to a FlattenEnumerator that wraps an Enumerator<Enumerator<T>> instead?
  class ConcatEnumerator<T> extends Enumerator<T> {

    const first: Enumerator<T>
    var firstDone: bool
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
      this.firstDone := false;
      this.second := second;
      
      enumerated := first.enumerated + second.enumerated;
      Repr := {this} + first.Repr + second.Repr;
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && (firstDone ==> first.Decreases() == 0)
      && (!firstDone ==> second.enumerated == [])
      && enumerated == first.enumerated + second.enumerated
    }

    method Next() returns (element: Option<T>)
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
      element := None;
      if !firstDone {
        element := first.Next();
      }
      if element.None? {
        firstDone := true;
        element := second.Next();
      }

      Repr := {this} + first.Repr + second.Repr;
      Enumerated(element);
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid() 
      decreases Repr, 1
    {
      first.Decreases() + second.Decreases()
    }

    lemma CountOfResult(firstCount: nat, secondCount: nat)
      requires Valid()
      requires Sized(first, firstCount)
      requires Sized(second, secondCount)
      ensures Sized(this, firstCount + secondCount)
    {}
  }

  // This is a tricky one to make fully general:
  //
  // * The most general is of type (IEnumerator<A>, IEnumerator<B>) -> IEnumerator<(A, B)>
  // * If either argument is finte, the result is too
  // * If both arguments are sized, the result is too
  //
  // ...and if the class forgets any useful such properties,
  // additional code can't add them later since the methods are opaque :(
  //
  // May also want an Enumerator2<A, B> variation, to avoid the
  // pair overhead for common cases like `foreach x, index in`
  class ZipEnumerator<A, B> extends Enumerator<(A, B)> {

    const first: Enumerator<A>
    const second: Enumerator<B>

    constructor(first: Enumerator<A>, second: Enumerator<B>, size: nat)
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

      enumerated := [];
      Repr := {this} + first.Repr + second.Repr;
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      // TODO: See top-level comment
      // && |enumerated| == |first.enumerated| == |second.enumerated|
      // && enumerated == Seq.Zip(first.enumerated, second.enumerated)
    }

    method Next() returns (element: Option<(A, B)>)
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
      var left := first.Next();
      var right := second.Next();
      if left.Some? && right.Some? {
        element := Some((left.value, right.value));
      } else {
        element := None;
      }
      
      Repr := {this} + first.Repr + second.Repr;
      Enumerated(element);
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid() 
      decreases Repr, 1
    {
      Math.Min(first.Decreases(), second.Decreases())
    }
  }

  class WithIndexEnumerator<T> extends Enumerator<(T, nat)> {

    const wrapped: Enumerator<T>
    var nextIndex: nat

    constructor(wrapped: Enumerator<T>) 
      requires wrapped.Valid()
      requires wrapped.enumerated == []
      ensures Valid() 
      ensures fresh(Repr - wrapped.Repr)
      ensures enumerated == []
      ensures this.wrapped == wrapped
    {
      this.wrapped := wrapped;
      this.nextIndex := 0;

      Repr := {this} + wrapped.Repr;
      enumerated := [];
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      // TODO: Similar challenge to ZipEnumerator although hopefully not as hard
      // && enumerated == Seq.Zip(wrapped.enumerated, seq(|wrapped.enumerated|, i => i))
    }

    method Next() returns (element: Option<(T, nat)>)
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
      var t := wrapped.Next();
      if t.Some? {
        element := Some((t.value, nextIndex));
        nextIndex := nextIndex + 1;
      } else {
        element := None;
      }
      Enumerated(element);

      // reveal Seq.Zip();
      // assert enumerated == Seq.Zip(wrapped.enumerated, seq(|wrapped.enumerated|, i => i));
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
      decreases Repr, 1
    {
      wrapped.Decreases()
    }
  }

  class FilteredEnumerator<T> extends Enumerator<T> {
    const wrapped: Enumerator<T>
    const filter: T -> bool

    constructor(wrapped: Enumerator<T>, filter: T -> bool) 
      requires wrapped.Valid()
      requires wrapped.enumerated == []
      ensures Valid()
      ensures fresh(Repr - old(wrapped.Repr))
      ensures enumerated == []
      ensures this.wrapped == wrapped
      ensures this.filter == filter
    {
      this.wrapped := wrapped;
      this.filter := filter;
      Repr := {this} + wrapped.Repr;
      enumerated := [];
    }

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
      && enumerated == Seq.Filter(filter, wrapped.enumerated)
    }

    method Next() returns (element: Option<T>)
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
      element := None;
      var more := true;
      while more
        invariant Valid()
        invariant wrapped.Repr < old(Repr)
        invariant Repr == old(Repr)
        invariant element.Some? ==> Decreases() < old(Decreases())
        invariant !more && element.None? ==> Decreases() == 0
        invariant !more && element.None? ==> enumerated == old(enumerated)
        invariant unchanged(`ienumerated)
        invariant enumerated == Seq.Filter(filter, wrapped.enumerated)
        decreases wrapped.Decreases(), more
      {
        var wrappedEnumeratedBefore := wrapped.enumerated;
        // This is where it is very difficult to prove termination if we
        // allow wrapped.Repr to potentially grow, because the assertion
        // we must satisfy for the recursive call to be allowed is actually
        // wrapped.Repr < old(Repr). That means updating Repr after this call
        // wouldn't help.
        var element := wrapped.Next();
        if element.None? {
          assert Decreases() == 0;
          more := false;
          // break;
        } else {
          reveal Seq.Filter();
          LemmaFilterDistributesOverConcat(filter, wrappedEnumeratedBefore, [element.value]);

          if filter(element.value) {
            enumerated := enumerated + [element.value];
            more := false;
            // break;
          } else {
          }
        }
      }
      ienumerated := ienumerated + [element];
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid()
      decreases Repr, 1
    {
      wrapped.Decreases()
    }
  }

  // This would allow a foreach loop to bind the values enumerated so far:
  // 
  // foreach (x, xs) in WithEnumerated(collection) { ... }
  //
  // I like this better than the magical definitions iterators provide,
  // since this way you're not culture-specific. :)
  class WithEnumeratedEnumerator<T> extends Enumerator<(T, ghost seq<T>)> {
    const wrapped: Enumerator<T>

    constructor(wrapped: Enumerator<T>) 
      requires wrapped.Valid()
      requires wrapped.enumerated == []
      ensures Valid() 
      ensures fresh(Repr - wrapped.Repr)
      ensures enumerated == []
      ensures this.wrapped == wrapped
    {
      this.wrapped := wrapped;
      Repr := {this} + wrapped.Repr;
      enumerated := [];
    }

    ghost predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
      && ValidComponent(wrapped)
    }

    method Next() returns (element: Option<(T, ghost seq<T>)>)
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
      var optT := wrapped.Next();
      match optT
      case Some(t) => {
        element := Some((t, ghost wrapped.enumerated));
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

  method Fold<T, A>(f: (A, T) -> A, init: A, e: Enumerator<T>) returns (result: A)
    requires e.Valid()
    requires e.enumerated == []
    modifies e.Repr
    ensures e.Valid()
    ensures e.Decreases() == 0
    ensures result == Seq.FoldLeft(f, init, e.enumerated)
  {
    reveal Seq.FoldLeft();
    result := init;
    while true
      invariant e.Valid() && e.Repr <= old(e.Repr)
      decreases e.Decreases()

      invariant result == Seq.FoldLeft(f, init, e.enumerated)
    {
      // TODO: Will the foreach loop sugar support this?
      // May at least need to use old@<label> instead.
      ghost var enumeratedBefore := e.enumerated;
      var element := e.Next();
      if element.None? { break; }

      result := f(result, element.value);

      Seq.LemmaFoldLeftDistributesOverConcat(f, init, enumeratedBefore, [element.value]);
    }
  }

  method CollectToSeq<T>(e: Enumerator<T>) returns (result: seq<T>)
    requires e.Valid()
    // TODO: Might remove these
    requires e.enumerated == []
    modifies e.Repr
    ensures e.Valid()
    ensures e.Decreases() == 0
    ensures result == e.enumerated
  {
    result := [];
    
    while true
      invariant e.Valid() && e.Repr <= old(e.Repr)
      decreases e.Decreases()

      invariant result == e.enumerated
    {
      var element := e.Next();
      if element.None? { break; }

      result := result + [element.value];
    }

    // TODO: Figure out how to use Fold instead. Good case study for invariant support!
    // var f := (s, x) => s + [x];
    // result := Fold(f, [], e);
    // Seq.LemmaInvFoldLeft(???, (s, x, s') => s + x == s', f, [], []);
  }

  // TODO: Still working on this one, it needs a solid specification of the number of
  // elements e will enumerate.
  // method CollectToArray<T(0)>(e: Enumerator<T>, size: nat) returns (result: array<T>)
  //   requires e.Valid()
  //   requires e.enumerated == []
  //   requires Sized(e, size)
  //   modifies e.Repr
  //   ensures e.Valid()
  //   ensures e.Decreases() == 0
  //   ensures result[..] == e.enumerated
  // {
  //   result := new T[size];
  //   var eWithIndex: Enumerator := new WithIndexEnumerator(e);
  //   while true
  //     invariant eWithIndex.Valid() && fresh(eWithIndex.Repr - e.Repr)
  //     modifies eWithIndex.Repr
  //     decreases eWithIndex.Decreases()
  //   {
  //     var pair := eWithIndex.Next();
  //     if pair.None? { break; }
  //     var (element, index) := pair.value;

  //     result[index] := element;
  //   }
  //   assert |e.enumerated| == size;
  // }

  trait Enumerable<T> extends Validatable {

    method Enumerator() returns (e: Enumerator<T>)
      requires Valid()
      ensures Valid()
      ensures e.Valid()
      ensures fresh(e.Repr)
      // TODO: How to express "will enumerate the contents of this"?
  }

  class SeqEnumerable<T> extends Enumerable<T> {
    const s: seq<T>

    ghost predicate Valid()
      reads this, Repr
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      this in Repr
    }

    method Enumerator() returns (e: Enumerator<T>)
      requires Valid()
      ensures Valid()
      ensures e.Valid()
      ensures fresh(e.Repr)
    {
      e := new SeqEnumerator(s);
    }
  }

}