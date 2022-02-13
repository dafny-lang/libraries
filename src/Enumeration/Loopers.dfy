
// include "../Actions.dfy"
include "../Frames.dfy"
include "../Wrappers.dfy"
include "../Collections/Sequences/Seq.dfy"

module Loopers {

  // import opened Actions
  import opened Frames
  import opened Wrappers

  import opened Seq

  trait InfiniteStepper extends Validatable {
    method Step() 
      requires Valid()
      ensures Valid()
  }

  method DoLoopStar(l: InfiniteStepper) 
    requires l.Valid()
    decreases *
  {
    while (true) decreases * {
      l.Step();
    }
  }

  // TODO: Merge this with Enumerator<T> - no point in having it separate
  // since you can always define Current() to be `this`.
   trait Stepper extends Validatable {
    method Step() 
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())

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
  }

  method DoLoop(l: Stepper)
    requires l.Valid()
    modifies l.Repr
    ensures l.Valid()
    ensures l.Done()
  {
    while (!l.Done())
      invariant l.ValidAndDisjoint()
      decreases l.Decreases()
    {
      l.Step();
    }
  }

  trait Enumerator<T> extends Stepper {

    // Any enumerator that produces one value at a time
    // and provably terminates is equivalent to an enumerator
    // that produces a specific seq<T>. This value may be underspecified
    // such that it is not known, even its length, until after all
    // values have been produced.
    // Dafny doesn't let you pass around an underspecified value though,
    // so we don't define a "to be enumerated" field or function.
    
    ghost var enumerated: seq<T>

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]

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
      ensures ValidAndDisjoint()
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

  // Wraps an enumerator that doesn't know if it has another value
  // until it tries to get the next value.
  // TODO: Equivalent to Filter?
  class TerminatedEnumerator<T> extends Enumerator<T> {
    const wrapped: Enumerator<Option<T>>

    constructor(wrapped: Enumerator<Option<T>>) 
      requires wrapped.Valid()
      ensures Valid()
      ensures fresh(Repr - {this} - wrapped.Repr)
    {
      this.wrapped := wrapped;
      enumerated := [];
      Repr := {this} + wrapped.Repr;
    }

    predicate Valid() 
      reads this, Repr 
      ensures Valid() ==> this in Repr 
      decreases Repr
    {
      && this in Repr
      && ValidComponent(wrapped)
    }

    function Decreases(): nat
      reads Repr
      requires Valid()
    {
      wrapped.Decreases()
    }

    predicate method Done() 
      reads Repr
      requires Valid()
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
    {
      wrapped.Done() || wrapped.Current().None?
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];
      wrapped.Step();
      Repr := {this} + wrapped.Repr;
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
    {
      wrapped.Current().value
    }
  }

  iterator SeqIterator<T(0)>(s: seq<T>) yields (element: T)
    yield ensures elements <= s
    ensures elements == s
  {
    for i := 0 to |s|
      invariant i == |elements|
      invariant elements <= s
    {
      yield s[i];
    }
  }

  class SeqIteratorEnumerator<T(0)> extends Enumerator<T> {

    const iter: SeqIterator<T>
    var done: bool

    ghost const original: seq<T>

    constructor(s: seq<T>) 
      ensures Valid() 
      ensures fresh(Repr) 
    {
      iter := new SeqIterator(s);
      original := s;
      enumerated := [];
      
      new;

      // Calling MoveNext() right away ensures we only enumerated yielded state.
      // Another version of this adaptor could not do this, and by consequence
      // enumerate the initial state of the iterator as well.
      var more := iter.MoveNext();
      done := !more;
      
      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && iter in Repr
      && this !in iter._modifies
      && this !in iter._reads
      && this !in iter._new
      && iter._modifies <= Repr
      && iter._reads <= Repr
      && iter._new <= Repr
      && (!done ==> iter.Valid())
      && iter.elements < iter.s
      && |enumerated| <= |original|
      && enumerated == original[0..|enumerated|]
    }

    predicate method Done()
      requires Valid()
      reads this, Repr
      decreases Repr, 0
      ensures Decreases() == 0 ==> Done()
      // ensures Done() ==> enumerated == original
    {
      done
    }

    method Step()
      requires Valid()
      requires !Done()
      modifies Repr
      decreases Repr
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];

      var more := iter.MoveNext();
      done := !more;

      Repr := {this, iter} + iter._modifies + iter._reads + iter._new;
    }

    function method Current(): T
      reads this, Repr
      requires Valid()
      requires !Done()
    {
      iter.element
    }

    function Decreases(): nat 
      reads this, Repr 
      requires Valid() 
    {
      assert iter.elements < iter.s;
      (|iter.s| - |iter.elements|) //+ (if done then 0 else 1)
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
      enumerated := [];
      
      Repr := {this} + first.Repr + second.Repr;
    }

    predicate Valid() reads this, Repr ensures Valid() ==> this in Repr {
      && this in Repr
      && ValidComponent(first)
      && ValidComponent(second)
      && first.Repr !! second.Repr
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
      ensures ValidAndDisjoint()
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
      if !first.Done() then first.Current() else second.Current()
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
      ensures ValidAndDisjoint()
      ensures Decreases() < old(Decreases())
      ensures enumerated == old(enumerated) + [old(Current())]
    {
      enumerated := enumerated + [Current()];
      while (!wrapped.Done() && !filter(wrapped.Current()))
        invariant wrapped.Valid()
        modifies Repr
        decreases wrapped.Decreases()
      {
        wrapped.Step();
      } 
      Repr := Repr + wrapped.Repr;
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

  method Example1() {
    var numbers := [1, 2, 3, 4, 5];
    var e: Enumerator<int> := new SeqEnumerator(numbers);
    label start:
    while (!e.Done()) 
      invariant e.Valid()
      invariant old@start(allocated(e)) && fresh(e.Repr)
      decreases e.Decreases()
    {
      print e.Current(), "\n";
      e.Step();
    }
  }

  method Example2() {
    var maybeNumbers := [Some(1), Some(2), Some(3), None, None];
    var e: Enumerator<Option<int>> := new SeqEnumerator(maybeNumbers);
    var e': Enumerator<int> := new TerminatedEnumerator(e);
    label start:
    while (!e'.Done()) 
      invariant e'.Valid()
      invariant old@start(allocated(e')) && fresh(e'.Repr)
      decreases e'.Decreases()
    {
      print e'.Current(), "\n";
      e'.Step();
    }
  }

  method Example3() {
    var first := [1, 2, 3, 4, 5];
    var second := [6, 7, 8];
    var e1 := new SeqEnumerator(first);
    var e2 := new SeqEnumerator(second);
    var e := new ConcatEnumerator(e1, e2);
   
    label start:
    while (!e.Done()) 
      invariant e.Valid()
      invariant fresh(e.Repr)
      decreases e.Decreases()
    {
      print e.Current(), "\n";
      
      e.Step();
    }
  }

  method Main() {
    Example3();
  }

  // TODO: Some similarities between this and composing
  // two Actions together.
  // One is:
  //   var r := action1.Invoke(a);
  //   var r2 := action2.Invoke(r);
  // Other is:
  //   var r := looper.Step();
  //   var _ := action.Invoke(r);
  //   var r2 := looper.Step();
  //   var _ := action.Invoke(r2);
  //   ...
  
  // class ForEach extends TerminatingLooper {
  //   const iter: TerminatingLooper
  //   const body: Action<TerminatingLooper, ()>

  //   constructor(iter: TerminatingLooper, body: Action<TerminatingLooper, ()>)
  //     requires iter.Valid()
  //     requires body.Valid()
  //     requires iter.Repr !! body.Repr
  //     requires iter.Valid() ==> body.Requires(iter)
  //     requires iter.Valid() ==> body.Modifies(iter) !! iter.Repr
  //     ensures Valid()
  //   {
  //     this.iter := iter;
  //     this.body := body;
  //     Repr := {this} + iter.Repr + body.Repr;
  //   }

  //   predicate Valid() 
  //     reads this, Repr
  //     decreases Repr
  //     ensures Valid() ==> this in Repr
  //   {
  //     && this in Repr
  //     && ValidComponent(iter)
  //     && ValidComponent(body)
  //     && iter.Repr !! body.Repr
  //     && (iter.Valid() ==> body.Requires(iter))
  //     // TODO: This needs to be a forall somehow
  //     && (iter.Valid() ==> body.Modifies(iter) !! iter.Repr)
  //   }

  //   function Decreases(): nat 
  //     reads Repr
  //     requires Valid()
  //   {
  //     iter.Decreases()
  //   }

  //   predicate method Done() 
  //     reads Repr
  //     requires Valid()
  //     ensures Decreases() == 0 ==> Done()
  //   {
  //     iter.Done()
  //   }

  //   method Step() 
  //     requires Valid()
  //     requires !Done()
  //     modifies Repr
  //     decreases Repr
  //     ensures ValidAndDisjoint()
  //     ensures Decreases() < old(Decreases())
  //   {
  //     iter.Step();
  //     Repr := Repr + iter.Repr;

  //     assert iter.Valid();
  //     assert  this in Repr;
  //     assert  ValidComponent(iter);
  //     assert  ValidComponent(body);
  //     assert  iter.Repr !! body.Repr;
  //     assert  (iter.Valid() ==> body.Requires(iter));
  //     assert  (iter.Valid() ==> body.Modifies(iter) !! iter.Repr);
  //     assert Valid();
      
  //     var _ := body.Invoke(iter);
  //     Repr := Repr + body.Repr;
  //   }
  // }

  // class SeqCollector<T> extends Action<T, ()> {

  //   var elements: seq<T>

  //   constructor() 
  //     ensures Valid()
  //     ensures fresh(Repr - {this})
  //   {
  //     elements := [];
  //     Repr := {this};
  //   }

  //   predicate Valid() 
  //     reads this, Repr 
  //     ensures Valid() ==> this in Repr 
  //     decreases Repr
  //   {
  //     && this in Repr
  //   }

  //   method Invoke(t: T) returns (nothing: ())
  //     requires Valid()
  //     requires Requires(t)
  //     modifies Modifies(t)
  //     decreases Decreases(t)
  //     ensures ValidAndDisjoint()
  //     ensures old(allocated(())) && Ensures(t, ())
  //   {
  //     elements := elements + [t];
  //   }

  //   predicate Requires(t: T) {
  //     true
  //   }

  //   // Need this separately from Repr for callers
  //   // Repr is the frame for Valid(), but callers
  //   // need to know what ELSE gets modified.
  //   function Modifies(t: T): set<object> requires Requires(t) {
  //     {this}
  //   }

  //   function Decreases(t: T): nat {
  //     0
  //   }
    
  //   twostate predicate Ensures(t: T, nothing: ()) {
  //     true
  //   }
  // }


  // method Main() {
  //   var numbers := [1, 2, 3, 4, 5];
  //   var numbersIter := new SeqLooper(numbers);
  //   var numbersPrinterLooper := new SeqCollector();
  //   var forEachLoop := new ForEach(numbersIter, numbersPrinterLooper);
  //   DoLoop(forEachLoop);
  // }
}