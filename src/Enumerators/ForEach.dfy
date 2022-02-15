
// module ForEach {
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
// }