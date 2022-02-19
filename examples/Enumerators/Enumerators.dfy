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
    var e: SeqEnumerator := new SeqEnumerator(s);
    result := CollectToSeq(e);
  }

  method AddTwoToEachEnumeratorVersion(s: seq<nat>) returns (result: seq<nat>)
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
    var filtered := new FilteredEnumerator(e, p);
    result := CollectToSeq(filtered);
  }

  method Concatenate<T>(first: seq<T>, second: seq<T>) returns (result: seq<T>)
    ensures result == first + second
  {
    var e1: Enumerator<T> := new SeqEnumerator(first);
    var e2 := new SeqEnumerator(second);
    var concatenated: ConcatEnumerator := new ConcatEnumerator(e1, e2);
    result := CollectToSeq(concatenated);
    assert concatenated.Valid();
  }

}