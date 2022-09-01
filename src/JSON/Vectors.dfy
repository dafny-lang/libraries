include "../BoundedInts.dfy"
include "../Wrappers.dfy"

module {:options "-functionSyntax:4"} Vectors {
  import opened BoundedInts
  import opened Wrappers

  datatype VectorError = OutOfMemory

  class Vector<A> {
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
      modifies this, `data
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

    function DefaultNewCapacity(capacity: uint32) : uint32 {
      if capacity < MAX_CAPACITY_BEFORE_DOUBLING
      then 2 * capacity
      else MAX_CAPACITY
    }

    method ReallocDefault() returns (o: Outcome<VectorError>)
      requires Valid?()
      modifies this, `data
      ensures Valid?()
      ensures Repr == old(Repr)
      ensures size == old(size)
      ensures old(capacity) == MAX_CAPACITY <==> o.Fail?
      ensures o.Fail? ==>
        && unchanged(this)
        && unchanged(data)
      ensures o.Pass? ==>
        && fresh(data)
        && old(capacity) < MAX_CAPACITY
        && capacity == old(if capacity < MAX_CAPACITY_BEFORE_DOUBLING
                          then 2 * capacity else MAX_CAPACITY)

    {
      if capacity == MAX_CAPACITY {
        return Fail(OutOfMemory);
      }
      Realloc(DefaultNewCapacity(capacity));
      return Pass;
    }

    method Ensure(reserved: uint32) returns (o: Outcome<VectorError>)
      requires Valid?()
      modifies this, `data
      ensures Valid?()
      ensures Repr == old(Repr)
      ensures size == old(size)
      ensures reserved <= capacity - size ==>
        o.Pass?
      ensures o.Pass? ==>
        old(size as int + reserved as int) <= capacity as int
      ensures o.Fail? ==>
        reserved > MAX_CAPACITY - size
    {
      if reserved > MAX_CAPACITY - size {
        return Fail(OutOfMemory);
      }
      if reserved <= capacity - size {
        return Pass;
      }
      var new_capacity := capacity;
      while reserved > new_capacity - size
        decreases MAX_CAPACITY - new_capacity
        invariant new_capacity >= capacity
      {
        new_capacity := DefaultNewCapacity(new_capacity);
      }
      Realloc(new_capacity);
      return Pass;
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

    method Push(a: A) returns (o: Outcome<VectorError>)
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
        var d := ReallocDefault();
        if d.Fail? { return d; }
      }
      PushFast(a);
      return Pass;
    }
  }
}
