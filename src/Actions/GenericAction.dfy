
include "../Wrappers.dfy"
include "../Frames.dfy"
include "../Math.dfy"
include "../Collections/Sequences/Seq.dfy"

include "DecreasesClauses.dfy"

module GenericActions {

  import opened Wrappers
  import opened Frames
  import opened Seq
  import opened Math
  import opened Termination

  trait {:termination false} Action<T, R> extends Validatable {

    ghost predicate Requires(t: T)
    ghost function Reads(t: T): set<object>
    ghost function Modifies(t: T): set<object>
    ghost function Decreases(t: T): TerminationMetric
    ghost predicate Ensures(t: T, r: R)

    method Invoke(t: T) returns (r: R) 
      requires Requires(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
  }

}