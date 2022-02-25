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

  // TODO: Add examples that use external implementations of specialized traits
  // like EnumeratorOfSeq<T>.
}