include "../Errors.dfy"
include "../LowLevel.Spec.dfy"
include "../LowLevel.SpecProperties.dfy"
include "../Utils/Views.Writers.dfy"

module {:options "-functionSyntax:4"} JSON.ZeroCopy.Serializer {
  import opened BoundedInts
  import opened Wrappers

  import opened Errors
  import LowLevel.Spec
  import LowLevel.SpecProperties
  import opened Grammar
  import opened Utils.Views.Writers
  import opened Vs = Utils.Views.Core // DISCUSS: Module naming convention?

  method Serialize(js: JSON) returns (rbs: SerializationResult<array<byte>>)
    ensures rbs.Success? ==> fresh(rbs.value)
    ensures rbs.Success? ==> rbs.value[..] == Spec.JSON(js)
  {
    var writer := Text(js);
    :- Need(writer.Unsaturated?, OutOfMemory);
    var bs := writer.ToArray();
    return Success(bs);
  }

  method SerializeTo(js: JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
    modifies bs
    ensures len.Success? ==> len.value as int <= bs.Length
    ensures len.Success? ==> bs[..len.value] == Spec.JSON(js)
    ensures len.Success? ==> bs[len.value..] == old(bs[len.value..])
    ensures len.Failure? ==> unchanged(bs)
  {
    var writer := Text(js);
    :- Need(writer.Unsaturated?, OutOfMemory);
    :- Need(writer.length as int <= bs.Length, OutOfMemory);
    writer.Blit(bs);
    return Success(writer.length);
  }

  function {:opaque} Text(js: JSON) : (wr: Writer)
    ensures wr.Bytes() == Spec.JSON(js)
  {
    JSON(js)
  }

  function {:opaque} JSON(js: JSON, writer: Writer := Writer.Empty) : (wr: Writer)
    ensures wr.Bytes() == writer.Bytes() + Spec.JSON(js)
  {
    writer
      .Append(js.before)
      .Then(wr => Value(js.t, wr))
      .Append(js.after)
  }

  function {:opaque} Value(v: Value, writer: Writer) : (wr: Writer)
    decreases v, 4
    ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
  {
    match v
      case Null(n) => writer.Append(n)
      case Bool(b) => writer.Append(b)
      case String(str) => String(str, writer)
      case Number(num) => Number(num, writer)
      case Object(obj) => Object(obj, writer)
      case Array(arr) => Array(arr, writer)
  }

  function {:opaque} String(str: jstring, writer: Writer) : (wr: Writer)
    decreases str, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.String(str)
  {
    writer
      .Append(str.lq)
      .Append(str.contents)
      .Append(str.rq)
  }

  function {:opaque} Number(num: jnumber, writer: Writer) : (wr: Writer)
    decreases num, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Number(num)
  {
    var writer := writer.Append(num.minus).Append(num.num);
    var writer := if num.frac.NonEmpty? then
        writer.Append(num.frac.t.period).Append(num.frac.t.num)
      else writer;
    var writer := if num.exp.NonEmpty? then
        writer.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num)
      else writer;
    writer
  }

  // DISCUSS: Can't be opaque, due to the lambda
  function StructuralView(st: Structural<View>, writer: Writer) : (wr: Writer)
    ensures wr.Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
  {
    writer.Append(st.before).Append(st.t).Append(st.after)
  }

  lemma {:axiom} Assume(b: bool) ensures b

  // FIXME refactor below to merge

  function {:opaque} Object(obj: jobject, writer: Writer) : (wr: Writer)
    decreases obj, 3
    ensures wr.Bytes() == writer.Bytes() + Spec.Object(obj)
  {
    var writer := StructuralView(obj.l, writer);
    var writer := Members(obj, writer);
    var writer := StructuralView(obj.r, writer);

    // We call ``ConcatBytes`` with ``Spec.Member``, whereas the spec calls it
    // with ``(d: jmember) requires d in obj.data => Spec.Member(d)``.  That's
    // why we need an explicit cast, which is performed by the lemma below.
    SpecProperties.Bracketed_Morphism(obj);
    assert Spec.Object(obj) == Spec.Bracketed(obj, Spec.Member);
    writer
  }

  function {:opaque} Array(arr: jarray, writer: Writer) : (wr: Writer)
    decreases arr, 3
    ensures wr.Bytes() == writer.Bytes() + Spec.Array(arr)
  {
    var writer := StructuralView(arr.l, writer);
    var writer := Items(arr, writer);
    var writer := StructuralView(arr.r, writer);

    // We call ``ConcatBytes`` with ``Spec.Item``, whereas the spec calls it
    // with ``(d: jitem) requires d in arr.data => Spec.Item(d)``.  That's
    // why we need an explicit cast, which is performed by the lemma below.
    SpecProperties.Bracketed_Morphism(arr); // DISCUSS
    assert Spec.Array(arr) == Spec.Bracketed(arr, Spec.Item);
    writer
  }

  function {:opaque} Members(obj: jobject, writer: Writer) : (wr: Writer)
    decreases obj, 2
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(obj.data, Spec.Member)
  {
    MembersSpec(obj, obj.data, writer)
  } by method {
    wr := MembersImpl(obj, writer);
    Assume(false); // BUG(https://github.com/dafny-lang/dafny/issues/2180)
  }

  function {:opaque} Items(arr: jarray, writer: Writer) : (wr: Writer)
    decreases arr, 2
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(arr.data, Spec.Item)
  {
    ItemsSpec(arr, arr.data, writer)
  } by method {
    wr := ItemsImpl(arr, writer);
    Assume(false); // BUG(https://github.com/dafny-lang/dafny/issues/2180)
  }

  ghost function MembersSpec(obj: jobject, members: seq<jmember>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |members| :: members[j] < obj
    decreases obj, 1, members
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(members, Spec.Member)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Members.
    if members == [] then writer
    else
      var writer := MembersSpec(obj, members[..|members|-1], writer);
      assert members == members[..|members|-1] + [members[|members|-1]];
      SpecProperties.ConcatBytes_Linear(members[..|members|-1], [members[|members|-1]], Spec.Member);
      Member(obj, members[|members|-1], writer)
  } // No by method block here, because the loop invariant in the method version
    // needs to call MembersSpec and the termination checker gets confused by
    // that.  Instead, see Members above. // DISCUSS

  // DISCUSS: Is there a way to avoid passing the ghost `v` around while
  // maintaining the termination argument?  Maybe the lambda for elements will be enough?

  ghost function SequenceSpec<T>(v: Value, items: seq<T>,
                                 spec: T -> bytes, impl: (ghost Value, T, Writer) --> Writer,
                                 writer: Writer)
    : (wr: Writer)
    requires forall item, wr | item in items :: impl.requires(v, item, wr)
    requires forall item, wr | item in items :: impl(v, item, wr).Bytes() == wr.Bytes() + spec(item)
    decreases v, 1, items
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, spec)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Items.
    if items == [] then writer
    else
      var writer := SequenceSpec(v, items[..|items|-1], spec, impl, writer);
      assert items == items[..|items|-1] + [items[|items|-1]];
      SpecProperties.ConcatBytes_Linear(items[..|items|-1], [items[|items|-1]], spec);
      impl(v, items[|items|-1], writer)
  } // No by method block here, because the loop invariant in the method version
    // needs to call `SequenceSpec` and the termination checker gets confused by
    // that.  Instead, see `Sequence`Items above. // DISCUSS


  ghost function ItemsSpec(arr: jarray, items: seq<jitem>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |items| :: items[j] < arr
    decreases arr, 1, items
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, Spec.Item)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Items.
    if items == [] then writer
    else
      var writer := ItemsSpec(arr, items[..|items|-1], writer);
      assert items == items[..|items|-1] + [items[|items|-1]];
      SpecProperties.ConcatBytes_Linear(items[..|items|-1], [items[|items|-1]], Spec.Item);
      Item(arr, items[|items|-1], writer)
  } // No by method block here, because the loop invariant in the method version
    // needs to call ItemsSpec and the termination checker gets confused by
    // that.  Instead, see Items above. // DISCUSS

  method MembersImpl(obj: jobject, writer: Writer) returns (wr: Writer)
    decreases obj, 1
    ensures wr == MembersSpec(obj, obj.data, writer);
  {
    wr := writer;
    var members := obj.data;
    assert wr == MembersSpec(obj, members[..0], writer);
    for i := 0 to |members| // FIXME uint32
      invariant wr == MembersSpec(obj, members[..i], writer)
    {
      assert members[..i+1][..i] == members[..i];
      wr := Member(obj, members[i], wr);
    }
    assert members[..|members|] == members;
  }

  method ItemsImpl(arr: jarray, writer: Writer) returns (wr: Writer)
    decreases arr, 1
    ensures wr == ItemsSpec(arr, arr.data, writer);
  {
    wr := writer;
    var items := arr.data;
    assert wr == ItemsSpec(arr, items[..0], writer);
    for i := 0 to |items| // FIXME uint32
      invariant wr == ItemsSpec(arr, items[..i], writer)
    {
      assert items[..i+1][..i] == items[..i];
      wr := Item(arr, items[i], wr);
    }
    assert items[..|items|] == items;
  }

  function {:opaque} Member(ghost obj: jobject, m: jmember, writer: Writer) : (wr: Writer)
    requires m < obj
    decreases obj, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Member(m)
  {
    var writer := String(m.t.k, writer);
    var writer := StructuralView(m.t.colon, writer);
    var writer := Value(m.t.v, writer);
    if m.suffix.Empty? then writer else StructuralView(m.suffix.t, writer)
  }

  function {:opaque} Item(ghost arr: jarray, m: jitem, writer: Writer) : (wr: Writer)
    requires m < arr
    decreases arr, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Item(m)
  {
    var writer := Value(m.t, writer);
    if m.suffix.Empty? then writer else StructuralView(m.suffix.t, writer)
  }
}
