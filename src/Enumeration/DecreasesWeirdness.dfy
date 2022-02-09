module DecreasesWeirdness {

  trait Thing {
    var Repr: set<object>
    predicate Valid()
      reads this, Repr 
      ensures Valid() ==> this in Repr
    method Foo() 
      requires Valid()
      decreases Repr 
  }

  class MyThing extends Thing {
    var d: int
    var wrapped: Thing
    constructor(wrapped: Thing) 
    {
      this.wrapped := wrapped;
      Repr := {this} + wrapped.Repr;
    }
    predicate Valid()
      reads this, Repr 
      ensures Valid() ==> this in Repr
    {
      && this in Repr
      && wrapped in Repr
      && wrapped.Repr <= Repr
      && this !in wrapped.Repr
      && wrapped.Valid()
    }
    
    method Foo() 
      requires Valid()
      decreases Repr 
    {
      var n := 5;
      while (n > 0) decreases n
      {
        assert wrapped.Repr < Repr;
        wrapped.Foo();
        print n;
        n := n - 1;
      }
    }
  }

  

}