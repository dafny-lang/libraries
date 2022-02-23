// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/Enumerators/Enumerators.dfy"

module Demo {

  import opened Enumerators

  // Note the common template for using a while loop on
  // an arbitrary Enumerator. This will likely be what we
  // propose that a "foreach" loop in Dafny will desugar to.

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

  // Some examples showing the equivalence between enumerator
  // operations and sequence operations.

  method RoundTrip(s: seq<nat>) returns (result: seq<nat>)
    ensures result == s
  {
    var e: Enumerator := new SeqEnumerator(s);
    result := CollectToSeq(e);
  }

  method AddTwoToEach(s: seq<nat>) returns (result: seq<nat>)
    ensures result == Seq.Map(x => x + 2, s)
  {
    var e := new SeqEnumerator(s);
    var mapped := new MappingEnumerator(x => x + 2, e);
    result := CollectToSeq(mapped);
  }

  method SetToSeq<T>(s: set<T>) returns (result: seq<T>)
    ensures multiset(result) == multiset(s)
  {
    var e := new SetEnumerator(s);
    result := CollectToSeq(e);
  }

  method Filter<T>(s: seq<T>, p: T -> bool) returns (result: seq<T>)
    ensures result == Seq.Filter(p, s)
  {
    var e := new SeqEnumerator(s);
    var filtered: FilteredEnumerator := new FilteredEnumerator(e, p);
    result := CollectToSeq(filtered);
    assert filtered.Valid();
  }

  method Concatenate<T>(first: seq<T>, second: seq<T>) returns (result: seq<T>)
    ensures result == first + second
  {
    var e1 := new SeqEnumerator(first);
    var e2 := new SeqEnumerator(second);
    var concatenated: ConcatEnumerator := new ConcatEnumerator(e1, e2);
    result := CollectToSeq(concatenated);
    assert concatenated.Valid();
  }

  // TODO: The examples above work because Dafny is aware of the concrete
  // types of the various enumerator values, and hence knows the additional post-conditions
  // of Valid() and !HasNext() necessary to support the more specific assertions.
  // That's why we need to explicitly attach a more specific type than Enumerator
  // to some variables, when type inference would otherwise choose Enumerator.
  // This will be an issue when trying to add more higher-order operations on enumerators,
  // or on linking to external implementations that don't have specific Dafny types to
  // attach their invariants on. 
  //
  // We'd like to have signatures like this, that ensures the Valid() and HasNext() 
  // implementations on the result have the desired properties, so we don't need the 
  // verifier to know the concrete type of the result:
  //
  // method MakeSeqEnumerator<T>(s: seq<T>) returns (result: Enumerator<T>)
  //   ensures forall e :: (result's HasNext applied to e) == false ==> e.enumerated == s)
  //
  // There isn't currently any way to refer to the HasNext function on the result that doesn't
  // bind result as the function receiver, though, and my attempts to define ghost vars that
  // hold onto such function references haven't worked out well so far.
}