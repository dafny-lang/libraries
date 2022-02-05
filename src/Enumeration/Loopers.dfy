
include "../Actions.dfy"
include "../Frames.dfy"

module Loopers {

  import opened Actions
  import opened Frames

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

  trait TerminatingLooper extends Validatable {
    // Will need to be arbitrary termination clause somehow instead
    // https://github.com/dafny-lang/dafny/issues/762
    // TODO: split up the ghost version from the version called at runtime?
    // Implementor needs to use this to prove termination, but caller
    // only needs Done()
    function method Decreases(): nat
      reads Repr
      decreases Repr
      requires Valid()
    predicate method Done() 
      reads Repr
      requires Valid()
    {
      Decreases() == 0
    }

    method Step() 
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())
  }

  method DoLoop(l: TerminatingLooper) 
    requires l.Valid()
    modifies l.Repr
    ensures l.Valid()
    ensures l.Done()
  {
    while (l.Decreases() > 0)
      invariant l.Valid()
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

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
      && 0 <= index <= |elements|
    }

    function method Decreases(): nat
      reads Repr
      requires Valid()
    {
      |elements| - index
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
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

    predicate Valid() 
      reads this, Repr
      decreases Repr
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && ValidComponent(iter)
      && ValidComponent(body)
      && iter.Repr !! body.Repr
      && (iter.Valid() ==> body.Requires(iter))
      && (iter.Valid() ==> body.Modifies(iter) == {})
    }

    function method Decreases(): nat 
      reads Repr
      requires Valid()
    {
      iter.Decreases()
    }

    method Step() 
      requires Valid()
      requires Decreases() > 0
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())
    {
      iter.Step();
      Repr := Repr + iter.Repr;
      
      var _ := body.Invoke(iter);
      Repr := Repr +  body.Repr;
    }
  }

  
}