include "../../src/Enumerators/Enumerators.dfy"

module Demo {

  import opened Enumerators

  method AddTwoToEach(s: seq<nat>) returns (result: seq<nat>)
    ensures forall x | x in result :: x >= 2
  {
    result := Seq.Map(x => x + 2, s);
  }

  method RoundTrip(s: seq<nat>) returns (result: seq<nat>)
    ensures result == s
  {
    var e: Enumerator := new SeqEnumerator(s);
    result := CollectToSeq(e);
  }

  method AddTwoToEachEnumeratorVersion(s: seq<nat>) returns (result: seq<nat>)
    ensures result == Seq.Map(x => x + 2, s)
  {
    var e := new SeqEnumerator(s);
    var mapped: Enumerator := new MappingEnumerator(x => x + 2, e);
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
    var e1: Enumerator<T> := new SeqEnumerator(first);
    var e2: Enumerator<T> := new SeqEnumerator(second);
    var concatenated: ConcatEnumerator := new ConcatEnumerator(e1, e2);
    result := CollectToSeq(concatenated);
    assert concatenated.Valid();
  }

  // TODO: Need to support the case of an invariant that isn't attached to a specific
  // concrete type that implements Enumerator<T>.
  // Want to state "will enumerate this" without that being baked into Enumerator<T> itself.
  
}