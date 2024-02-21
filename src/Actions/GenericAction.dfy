
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
      reads this
      ensures this in Reads(t)
    ghost function Modifies(t: T): set<object>
      reads Reads(t)
    ghost function Decreases(t: T): TerminationMetric
      reads Reads(t)
    // These are split in two because we can't pass r
    // to a twostate predicate (since it might not be allocated
    // in the previous state)
    ghost predicate Ensures(t: T, r: R)
      reads Reads(t)
    twostate predicate EnsuresTwostate(t: T)
      reads Reads(t)

    // Action action implementation

    method Invoke(t: T) returns (r: R) 
      requires Requires(t)
      reads Reads(t)
      modifies Modifies(t)
      decreases Decreases(t).Ordinal()
      ensures Ensures(t, r)
      ensures EnsuresTwostate(t)
  }

}