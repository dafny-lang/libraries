
include "../Actions.dfy"

module Loopers {

  import opened Actions

  trait Looper {
      predicate Invariant()
      method Step() 
        requires Invariant()
        ensures Invariant()
  }

  method DoLoopStar(l: Looper) 
    requires l.Invariant()
    decreases *
  {
    while (true) decreases * {
      l.Step();
    }
  }

  trait TerminatingLooper {
      ghost var Repr: set<object>
      predicate Invariant()
        reads this, Repr
        ensures Invariant() ==> this in Repr
      
      // Will need to be arbitrary termination clause somehow instead
      // https://github.com/dafny-lang/dafny/issues/762
      // TODO: split up the ghost version from the version called at runtime?
      function method Decreases(): nat
        reads Repr
        decreases Repr
        requires Invariant()
      predicate method Done() 
        reads Repr
        requires Invariant()
      {
        Decreases() == 0
      }

      method Step() 
        requires Invariant()
        requires !Done()
        modifies Repr
        ensures Invariant()
        ensures fresh(Repr - old(Repr))
        ensures Decreases() < old(Decreases())
  }

  method DoLoop(l: TerminatingLooper) 
    requires l.Invariant()
    modifies l.Repr
    ensures l.Invariant()
    ensures l.Done()
  {
    while (l.Decreases() > 0)
      invariant l.Invariant()
      invariant fresh(l.Repr - old(l.Repr))
    {
      l.Step();
    }
  }

  class SeqLooper<T> extends TerminatingLooper {

    const elements: seq<T>
    var index: nat

    constructor(s: seq<T>) {
      elements := s;
      index := 0;
      Repr := {this};
    }

    predicate Invariant() 
      reads this, Repr 
      ensures Invariant() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
      && 0 <= index <= |elements|
    }

    function method Decreases(): nat
      reads Repr
      requires Invariant()
    {
      |elements| - index
    }

    method Step()
      requires Invariant()
      requires !Done()
      modifies Repr
      ensures Invariant()
      ensures fresh(Repr - old(Repr))
      ensures Decreases() < old(Decreases())
    {
      index := index + 1;
    }
  }

  class ForEach<T> extends TerminatingLooper {
    const iter: TerminatingLooper
    const body: Action<TerminatingLooper, ()>

    constructor(iter: TerminatingLooper, body: Action<TerminatingLooper, ()>) {
      this.iter := iter;
      this.body := body;
    }

    predicate Invariant() 
      reads this, Repr
      decreases Repr
      ensures Invariant() ==> this in Repr
    {
      && this in Repr
      && iter in Repr
      && iter.Repr <= Repr
      && this !in iter.Repr
      && iter.Invariant() && (iter.Invariant() ==> body.Requires(iter))
    }

    function method Decreases(): nat 
      reads Repr
      requires Invariant()
    {
      iter.Decreases()
    }

    method Step() 
      requires Invariant()
      requires Decreases() > 0
      modifies Repr
      decreases Repr
      ensures Invariant()
      ensures fresh(Repr - old(Repr))
      ensures Decreases() < old(Decreases())
    {
      iter.Step();
      var _ := body.Invoke(iter);
    }
  }
}