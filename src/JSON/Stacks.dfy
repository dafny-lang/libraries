include "../BoundedInts.dfy"
include "../Wrappers.dfy"

module {:options "/functionSyntax:4"} Stacks {
  import opened BoundedInts
  import opened Wrappers

  datatype Error = OutOfMemory

  class Stack<A> {
    ghost var Repr : seq<A>

    const a: A
    var size: uint32
    var capacity: uint32
    var data: array<A>

    const MAX_CAPACITY: uint32 := UINT32_MAX
    const MAX_CAPACITY_BEFORE_DOUBLING: uint32 := UINT32_MAX / 2

    ghost predicate Valid?()
      reads this, data
    {
      && capacity != 0
      && data.Length == capacity as int
      && size <= capacity
      && Repr == data[..size]
    }

    constructor(a0: A, initial_capacity: uint32 := 8)
      requires initial_capacity > 0
      ensures Valid?()
    {
      a := a0;
      Repr := [];
      size := 0;
      capacity := initial_capacity;
      data := new A[initial_capacity](_ => a0);
    }

    method At(idx: uint32) returns (a: A)
      requires idx < size
      requires Valid?()
      ensures a == data[idx] == Repr[idx]
    {
      return data[idx];
    }

    method Blit(new_data: array<A>, count: uint32)
      requires count as int <= new_data.Length
      requires count <= capacity
      requires data.Length == capacity as int
      modifies data
      ensures data[..count] == new_data[..count]
      ensures data[count..] == old(data[count..])
    {
      for idx: uint32 := 0 to count
        invariant idx <= capacity
        invariant data.Length == capacity as int
        invariant data[..idx] == new_data[..idx]
        invariant data[count..] == old(data[count..])
      {
        data[idx] := new_data[idx];
      }
    }

    method Realloc(new_capacity: uint32)
      requires Valid?()
      requires new_capacity > capacity
      modifies this, data
      ensures Valid?()
      ensures Repr == old(Repr)
      ensures size == old(size)
      ensures capacity == new_capacity
      ensures fresh(data)
    {
      var old_data, old_capacity := data, capacity;
      data, capacity := new A[new_capacity](_ => a), new_capacity;
      Blit(old_data, old_capacity);
    }

    method PopFast(a: A)
      requires Valid?()
      requires size > 0
      modifies this, data
      ensures Valid?()
      ensures size == old(size) - 1
      ensures Repr == old(Repr[..|Repr| - 1])
    {
      size := size - 1;
      Repr := Repr[..|Repr| - 1];
    }

    method PushFast(a: A)
      requires Valid?()
      requires size < capacity
      modifies this, data
      ensures Valid?()
      ensures size == old(size) + 1
      ensures Repr == old(Repr) + [a]
    {
      data[size] := a;
      size := size + 1;
      Repr := Repr + [a];
    }

    method Push(a: A) returns (o: Outcome<Error>)
      requires Valid?()
      modifies this, data
      ensures Valid?()
      ensures o.Fail? ==>
        && unchanged(this)
        && unchanged(data)
      ensures o.Pass? ==>
        && old(size) < MAX_CAPACITY
        && size == old(size) + 1
        && Repr == old(Repr) + [a]
    {
      if size == capacity {
        if capacity < MAX_CAPACITY_BEFORE_DOUBLING {
          Realloc(2 * capacity);
        } else {
          if capacity == MAX_CAPACITY {
            return Fail(OutOfMemory);
          }
          Realloc(MAX_CAPACITY);
        }
      }
      PushFast(a);
      return Pass;
    }
  }
}
