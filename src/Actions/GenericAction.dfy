
include "../Wrappers.dfy"
include "../Frames.dfy"
include "../Math.dfy"
include "../Collections/Sequences/Seq.dfy"

include "DecreasesClauses.dfy"

module GenericActions {

  import opened Termination

  trait {:termination false} GenericAction<T, R> {

    // Specification predicates

    ghost predicate Requires(t: T)
      reads Reads(t)
    ghost function Reads(t: T): set<object>
      // requires Requires(t)
      reads this
      ensures this in Reads(t)
    ghost function Modifies(t: T): set<object>
      reads Reads(t)
    ghost function Decreases(t: T): TerminationMetric
      reads Reads(t)
    twostate predicate Ensures(t: T, new r: R)
      reads Reads(t)

    // Actual action implementation

    method Invoke(t: T) returns (r: R) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
  }

}