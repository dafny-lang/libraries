// RUN: %dafny /compile:3 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/Enumerators/Enumerators.dfy"

module Demo {

  import opened Enumerators
  import opened Wrappers

  // Note the common template for using a while loop on
  // an arbitrary Enumerator. This will likely be what we
  // propose that a "foreach" loop in Dafny will desugar to.

  method Example1() {
    var numbers := [1, 2, 3, 4, 5];

    var e: Enumerator<int> := new SeqEnumerator(numbers);
    while true
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();
      if element.None? { break; }

      print element.value, "\n";
    }
  }

  method Example2() {
    var first := [1, 2, 3, 4, 5];
    var second := [6, 7, 8];
    var e1 := new SeqEnumerator(first);
    var e2 := new SeqEnumerator(second);
    var e: Enumerator := new ConcatEnumerator(e1, e2);
   
    while true
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();
      if element.None? { break; }

      print element.value, "\n";
    }
  }

  method PrintWithCommas() {
    var first := [1, 2, 3, 4, 5];
    var e: Enumerator := new SeqEnumerator(first);
   
    for index := 0 to *
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();
      if element.None? { break; }

      if index > 0 {
        print ", ";
      }
      print element;
    }
    print "\n";
  }

  method MappingExample() {
    var first := [1, 2, 3, 4, 5];
    var e1 := new SeqEnumerator(first);
    var e: Enumerator := new MappingEnumerator(x => x + 2, e1);
   
    var result: seq<int> := [];
    while true
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      var element := e.Next();
      if element.None? { break; }

      result := result + [element.value];
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

  // method ToArray(s: seq<nat>) returns (result: array<nat>)
  //   ensures result[..] == s
  // {
  //   var e: Enumerator := new SeqEnumerator(s);
  //   assert Sized(e, |s|);
  //   result := CollectToArray(e, |s|);
  // }

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

  method SeqEnumerator<T>(s: seq<T>) returns (r: Enumerator<T>) 
    ensures r.Valid() && fresh(r.Repr)
    // ensures Sized(r, |s|)
  {
    r := new SeqEnumerator(s);
  }

  // method SizedExample<T>()
  // {
  //   var e: Enumerator := SeqEnumerator([1,2,3,4,5]);
  //   assert Sized(e, 5);
  //   var one := e.Next();
  //   assert Sized(e, 5);
  // }


  method Filter<T>(s: seq<T>, p: T -> bool) returns (result: seq<T>)
    ensures result == Seq.Filter(p, s)
  {
    var e := new SeqEnumerator(s);
    var filtered: FilteredEnumerator := new FilteredEnumerator(e, p);
    result := CollectToSeq(filtered);
    assert e.enumerated == s;
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

  // method ConcatenateToArray<T(0)>(first: seq<T>, second: seq<T>) returns (result: array<T>)
  //   ensures result[..] == first + second
  // {
  //   var e1 := new SeqEnumerator(first);
  //   var e2 := new SeqEnumerator(second);
  //   var concatenated: ConcatEnumerator := new ConcatEnumerator(e1, e2);
  //   concatenated.CountOfResult(|first|, |second|);
  //   result := CollectToArray(concatenated, |first| + |second|);
  //   assert concatenated.Valid();
  // }

  class Cell {
    constructor() {}
  }

  // An enumerator that produces newly allocated objects.
  // Test case for framing.
  class CellEnumerator extends Enumerator<Cell> {
    var remaining: nat
    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr
      decreases Repr, 0
    {
      && this in Repr
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
      decreases Repr, 1
    {
      remaining
    }
    
    method Next() returns (element: Option<Cell>)
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
      if remaining > 0 {
        var cell := new Cell();
        element := Some(cell);
        remaining := remaining - 1;
      } else {
        element := None;
      }
      Enumerated(element);
    }
  }

  method EnumerateForever() decreases * {
    var allNats := new NatEnumerator();
    while true 
      invariant allNats.Valid() && fresh(allNats.Repr)
      decreases * 
    {
      var next := allNats.Next();
      print next;
    }
  }
}