
include "../Frames.dfy"

module JavaStyle {

  import opened Frames

  class JavaStyleIterator<T> {
    const s: seq<T>
    var index: nat

    constructor(s: seq<T>) 
      ensures Valid()
    {
      this.s := s;
      this.index := 0;
    }

    predicate Valid()
      reads this
    {
      && 0 <= index <= |s|
    }

    function method HasNext(): (res: bool)
      reads this
      ensures res == (index < |s|)
    {
      index < |s|
    }

    method Next() returns (res: T)
      requires Valid()
      requires HasNext()
      modifies this
      // ensures Valid()
      ensures index == old(index) + 1
    {
      res := s[index];
      index := index + 1;
    }
  }

  method Main() {
    var s := [1, 2, 3, 4, 5];
    var iter := new JavaStyleIterator(s);
    while (iter.HasNext())
      decreases |iter.s| - iter.index
    {
      var n := iter.Next();
      print n;
    }
  }

}