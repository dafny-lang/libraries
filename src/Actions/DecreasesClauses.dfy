
module Termination {

  datatype ClauseTail = More(next: TerminationMetric) | Top

  datatype TerminationMetric = TerminationMetric(first: TMValue, rest: ClauseTail) {
    predicate IsSmallerThan(other: TerminationMetric) {
      if first == other.first then
        match (rest, other.rest) {
          case (Top, _) => false
          case (More(_), Top) => true
          case (More(next), More(otherNext)) => next.IsSmallerThan(otherNext)
        }
      else
        first.IsSmallerThan(other.first)
    }

    ghost function {:axiom} Ordinal(): ORDINAL
  }

  lemma {:axiom} OrdinalOrdered(left: TerminationMetric, right: TerminationMetric) 
    requires left.IsSmallerThan(right)
    ensures left.Ordinal() < right.Ordinal()

  datatype TMValue = 
    | TMNat(natValue: nat)
    | TMChar(charValue: nat)
    | TMSeq(seqValue: seq<TMValue>) 
    // TODO: etc
  {
    predicate IsSmallerThan(other: TMValue) {
      match (this, other) {
        case (TMNat(left), TMNat(right)) => left < right
        case (TMChar(left), TMChar(right)) => left < right
        case (TMSeq(left), TMSeq(right)) => left < right // TODO: should be Seq.IsSubsequenceOf
        // TODO: etc
        case _ => false
      }
    }
  }
}

module Example {

  datatype D = Less(x: nat) | More(x: nat)

  function Foo(d: D): nat 
    decreases d
  {
    if d.More? then
      Foo(Less(d.x))
    else
      if d.x == 0 then  
        42
      else
        Foo(Less(d.x - 1))
  }
}