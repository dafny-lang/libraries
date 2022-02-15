
// include "../Actions.dfy"
include "../Frames.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module Enumerators {

  // import opened Actions
  import opened Frames
  import opened Wrappers
  import opened Seq

  trait {:termination false} Enumerator<T> extends Validatable {
    
    ghost var enumerated: seq<T>

    // Any enumerator that produces one value at a time
    // and provably terminates is equivalent to an enumerator
    // that produces a specific seq<T>. This value may be underspecified
    // such that it is not known, even its length, until after all
    // values have been produced.
    // Dafny doesn't let you pass around an underspecified value though,
    // so we don't define a "to be enumerated" field or function.

    // TODO: Change into `Next() returns T` so we don't need a separate Current() method
    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]

    // Would be better as an arbitrary termination clause somehow instead
    // https://github.com/dafny-lang/dafny/issues/762
    function Decreases(): nat
      reads Repr
      decreases Repr
      requires Valid()

    predicate method Done() 
      reads Repr
      requires Valid()
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
  }

  class SeqEnumerator<T> extends Enumerator<T> {

    const elements: seq<T>
    var index: nat

    constructor(s: seq<T>) 
      ensures Valid()
      ensures fresh(Repr - {this})
    {
      elements := s;
      index := 0;

      enumerated := [];
      Repr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
      && 0 <= index <= |elements|
      && enumerated == elements[0..index]
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
    {
      |elements| - index
    }

    predicate method Done() 
      reads Repr
      requires Valid()
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
      ensures Done() ==> enumerated == elements
    {
      index == |elements|
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];
      index := index + 1;
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
    {
      elements[index]
    }
  }

  class SetEnumerator<T(==)> extends Enumerator<T> {
    ghost const original: set<T>
    var remaining: set<T>
    var current: Option<T>

    constructor(s: set<T>) 
      ensures Valid() 
      ensures fresh(Repr)
    {
      this.original := s;
      this.remaining := s;
      new;
      if |remaining| > 0 {
        var element: T :| element in remaining;
        current := Some(element);
        remaining := remaining - {element};
      } else {
        current := None;
      }

      enumerated := [];
      Repr := {this};
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
    {
      && this in Repr
      && (current.None? ==> |remaining| == 0)
    }

    predicate method Done()
      requires Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
    {
      current.None?
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];

      if |remaining| > 0 {
        var element: T :| element in remaining;
        current := Some(element);
        remaining := remaining - {element};
      } else {
        current := None;
      }
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
    {
      current.value
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
    {
      |remaining| + (if current.Some? then 1 else 0)
    }
  }

  class ConcatEnumerator<T(0)> extends Enumerator<T> {

    const first: Enumerator<T>
    const second: Enumerator<T>

    constructor(first: Enumerator<T>, second: Enumerator<T>)
      requires first.Valid()
      requires second.Valid()
      requires first.Repr !! second.Repr
      ensures Valid() 
      ensures fresh(Repr - first.Repr - second.Repr) 
    {
      this.first := first;
      this.second := second;
      
      enumerated := first.enumerated + second.enumerated;
      Repr := {this} + first.Repr + second.Repr;
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
      && enumerated == first.enumerated + second.enumerated
    }

    predicate method Done()
      requires Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
    {
      first.Done() && second.Done()
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];

      if !first.Done() {
        first.Step();
      } else {
        second.Step();
      }
      Repr := {this} + first.Repr + second.Repr;
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
    {
      if !first.Done() then 
        first.Current() 
      else
        second.Current()
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid() 
    {
      first.Decreases() + second.Decreases()
    }
  }

  // TODO: Prove the semantics!
  class Filter<T(0)> extends Enumerator<T> {
    const wrapped: Enumerator<T>
    const filter: T -> bool

    constructor(wrapped: Enumerator<T>, filter: T -> bool) 
      requires wrapped.Valid()
      ensures Valid() 
    {
      this.wrapped := wrapped;
      this.filter := filter;
      Repr := {this} + wrapped.Repr;
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && ValidComponent(wrapped)
    }

    predicate method Done()
      reads Repr
      requires Valid()
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
    {
      wrapped.Done()
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures Valid()
      ensures Repr <= old(Repr)
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];

      wrapped.Step();
      while (!wrapped.Done() && !filter(wrapped.Current()))
        invariant Valid()
        invariant wrapped.Repr < old(Repr)
        invariant Repr == old(Repr)
        invariant enumerated == old(enumerated) + [old(Current())]
        decreases wrapped.Decreases()
      {
        wrapped.Step();
      }
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done() 
    {
      wrapped.Current() 
    }

    function Decreases(): nat 
      reads this, Repr
      requires Valid() 
    {
      wrapped.Decreases()
    }
  }

  // method Max(s: set<int>) returns (max: int)
  //   requires |s| > 0
  //   ensures max in s
  //   ensures forall x | x in s :: max >= x
  // {
  //   var first: int :| first in s;
  //   max := first;
  //   var sEnum: SetEnumerator<int> := new SetEnumerator(s - {max});
  //   assert fresh(sEnum.Repr);
  //   label start:
  //   var more := true;
  //   while (!sEnum.Done()) 
  //     invariant sEnum.Valid()
  //     invariant fresh(sEnum.Repr)
  //     invariant max == Seq.Max([first] + sEnum.enumerated)
  //     decreases more, sEnum.Decreases()
  //   {
  //     var more := sEnum.MoveNext();
  //     if !more { break; }

  //     if sEnum.Current() > max {
  //       max := sEnum.Current();
  //     }
  //   }
  // }

  method Example1() {
    var numbers := [1, 2, 3, 4, 5];

    var e: Enumerator<int> := new SeqEnumerator(numbers);
    while (!e.Done()) 
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      print e.Current(), "\n";

      e.Step();
    }
  }

  method Example2() {
    var first := [1, 2, 3, 4, 5];
    var second := [6, 7, 8];
    var e1 := new SeqEnumerator(first);
    var e2 := new SeqEnumerator(second);
    var e := new ConcatEnumerator(e1, e2);
   
    while (!e.Done()) 
      invariant e.Valid() && fresh(e.Repr)
      decreases e.Decreases()
    {
      print e.Current(), "\n";
      
      e.Step();
    }
  }

  // TODO: Explicit example of working with lazy iterators, more emphasis on `Done` being a pure function
  // TODO: Need to give background on Validatable, the fact that Valid() is the loop invariant
  // TODO: Mention `enumerated` ghost variable, proving semantics based on that
  // TODO: Fix Filter even before proving semantics?
}