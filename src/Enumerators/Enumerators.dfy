
// include "../Actions.dfy"
include "../Frames.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module Enumerators {

  // import opened Actions
  import opened Frames
  import opened Wrappers
  import opened Seq

  trait {:termination false} Enumerator<T> extends Validatable {
    
    // The Valid() predicate from the Validatable trait ends up
    // becoming the "enumeration invariant", which in turn becomes
    // the loop invariant in a while loop that uses an enumerator.

    ghost var enumerated: seq<T>

    // Any enumerator that produces one value at a time
    // and provably terminates is equivalent to an enumerator
    // that produces a specific seq<T>. This value may be underspecified
    // such that it is not known, even its length, until after all
    // values have been produced.
    // Dafny doesn't let you pass around an underspecified value though,
    // so we don't define a "to be enumerated" field or function.

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
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [element]

    // Would be better as an arbitrary termination clause somehow instead
    // https://github.com/dafny-lang/dafny/issues/762
    function Decreases(): nat
      reads Repr
      decreases Repr, 1
      requires Valid()
  }

  // TODO: Common EagerEnumerator<T> that wraps a Enumerator<Option<T>>
  // for cases like Filter or IteratorAdaptor that can't calculate HasNext() 
  // ahead of time?

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

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
      decreases Repr, 1
    {
      |remaining|
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

    // TODO: Unset once each is Done() to allow garbage collection?
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

  // TODO: Prove the semantics!
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
      ensures !HasNext() ==> !wrapped.HasNext() // TODO
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

  method CollectToSeq<T>(e: Enumerator<T>) returns (s: seq<T>)
    requires e.Valid()
    // TODO: Might remove this
    requires e.enumerated == []
    modifies e.Repr
    ensures e.Valid()
    ensures !e.HasNext()
    ensures s == e.enumerated
  {
    s := [];
    while (e.HasNext())
      invariant e.Valid() && e.Repr <= old(e.Repr)
      decreases e.Decreases()

      invariant s == e.enumerated
    {
      var element := e.Next();
      s := s + [element];
    }
  }

  // method Max(s: set<int>) returns (max: int)
  //   requires |s| > 0
  //   ensures max in s
  //   ensures forall x | x in s :: max >= x
  // {
  //   var first: int :| first in s;
  //   max := first;
  //   var rest := s - {max};

  //   var sEnum: SetEnumerator<int> := new SetEnumerator(rest);
  //   while (sEnum.HasNext()) 
  //     invariant sEnum.Valid()
  //     invariant fresh(sEnum.Repr)
  //     invariant max == Seq.Max([first] + sEnum.enumerated)
  //     decreases sEnum.Decreases()
  //   {
  //     var element := sEnum.Next();

  //     if max < element {
  //       max := element;
  //     }
  //   }
  //   assert max == Seq.Max([first] + sEnum.enumerated);
  //   assert multiset(sEnum.enumerated) == multiset(rest);
  // }

  method Example1() {
    var numbers := [1, 2, 3, 4, 5];

    var e: Enumerator<int> := new SeqEnumerator(numbers);
    while (e.HasNext()) 
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();

      print element, "\n";
    }
  }

  method Example2() {
    var first := [1, 2, 3, 4, 5];
    var second := [6, 7, 8];
    var e1 := new SeqEnumerator(first);
    var e2 := new SeqEnumerator(second);
    var e := new ConcatEnumerator(e1, e2);
   
    while (e.HasNext()) 
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();

      print element, "\n";
    }
  }

  method PrintWithCommas() {
    var first := [1, 2, 3, 4, 5];
    var e := new SeqEnumerator(first);
   
    while (e.HasNext()) 
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();

      print element;
      if e.HasNext() {
        print ", ";
      }
    }
    print "\n";
  }

  method MappingExample() {
    var first := [1, 2, 3, 4, 5];
    var e1 := new SeqEnumerator(first);
    var e := new MappingEnumerator(x => x + 2, e1);
   
    var result: seq<int> := [];
    while (e.HasNext()) 
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();

      result := result + [element];
    }
    assert e.enumerated == Seq.Map(x => x + 2, first);
  }

  // TODO: Explicit example of working with lazy iterators, more emphasis on `HasNext` being a pure function
  // TODO: Need to give background on Validatable, the fact that Valid() is the loop invariant
  // TODO: Mention `enumerated` ghost variable, proving semantics based on that
  // TODO: Are ghost enumerators a thing? :)
  // TODO: Most enumerator constructors should ensure enumerated == [] and other things
  //       Important to have end to end examples to ensure correctness invariants are actually usable!
  //       Also usually need to (at least for v1) require that child enumerators are fresh (enumerated == [])
  // TODO: Framing invariant is a pain in the butt, seems to need a label to be generic
  // TODO: Example of various traversals of datatype trees/graphs
  // TODO: Think about Enumerator<T> (and hypothetical Aggregator<T>) as special cases of
  //       Action<T, R>s with a relationship between their pre- and post-conditions.
}