
// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../src/Frames.dfy"

module ValidatableExample {

  import opened Frames

  // Example loosely based on Chapters 8 and 9 of "Using Dafny, an Automatic Program Verifier":
  // http://leino.science/papers/krml221.pdf

  class Cell extends Validatable {
    // public variables
    var Data: int;    

    function Valid(): bool
      reads this, Repr
    {
      Repr == {this}
    }

    constructor()
      ensures Valid() && fresh(Repr - {this})
      ensures Data == 0
    {
      Data := 0;
      Repr := {this};
    }

    method Inc() 
      requires Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Data == old(Data) + 1
    {
      Data := Data + 1;
    }
  }

  class Counter extends Validatable {
    // public variables
    ghost var Value: int;
    // private variables
    var incs: Cell;
    var decs: Cell;

    function Valid(): bool
      reads this, Repr
    {
      && this in Repr
      && ValidComponent(incs)
      && ValidComponent(decs)
      && incs.Repr !! decs.Repr
      && Value == incs.Data - decs.Data
    }

    constructor()
      ensures Valid() && fresh(Repr - {this} - incs.Repr - decs.Repr)
      ensures Value == 0
    {
      incs := new Cell();
      decs := new Cell();
      Value := 0;
      new;
      Repr := {this} + incs.Repr + decs.Repr;
    }

    method GetValue() returns (x: int)
      requires Valid()
      ensures x == Value
    {
      x := incs.Data - decs.Data;
    }

    method Inc()
      requires Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value == old(Value) + 1
    {
      incs.Inc();
      Value := Value + 1;
      Repr := {this} + incs.Repr + decs.Repr;
    }

    method Dec()
      requires Valid()
      modifies Repr
      ensures ValidAndDisjoint()
      ensures Value == old(Value) - 1
    {
      decs.Inc();
      Value := Value - 1;
      Repr := {this} + incs.Repr + decs.Repr;
    }
  }
}
