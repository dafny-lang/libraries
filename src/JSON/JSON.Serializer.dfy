include "JSON.Spec.dfy"
include "JSON.SpecProperties.dfy"
include "Views.Writers.dfy"

module {:options "-functionSyntax:4"} JSON.Serializer {
  import opened BoundedInts
  import opened Wrappers

  import Spec
  import SpecProperties
  import opened Grammar
  import opened Views.Writers
  import opened Vs = Views.Core // DISCUSS: Module naming convention?

  datatype Error = OutOfMemory

  method Serialize(js: JSON) returns (bsr: Result<array<byte>, Error>)
    ensures bsr.Success? ==> bsr.value[..] == Spec.JSON(js)
  {
    var writer := JSON(js);
    :- Need(writer.Unsaturated?, OutOfMemory);
    var bs := writer.ToArray();
    return Success(bs);
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
      case Null(n) =>
        writer.Append(n)
      case Bool(b) =>
        writer.Append(b)
      case String(str) =>
        writer.Append(str)
      case Number(minus, num, frac, exp) =>
        Number(v, writer)
      case Object(obj) =>
        Object(v, obj, writer)
      case Array(arr) =>
        Array(v, arr, writer)
  }

  function {:opaque} Number(v: Value, writer: Writer) : (wr: Writer)
    requires v.Number?
    decreases v, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
  {
    var writer := writer.Append(v.minus).Append(v.num);
    var writer := if v.frac.NonEmpty? then
        writer.Append(v.frac.t.period).Append(v.frac.t.num)
      else writer;
    var writer := if v.exp.NonEmpty? then
        writer.Append(v.exp.t.e).Append(v.exp.t.sign).Append(v.exp.t.num)
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

  function {:opaque} Object(v: Value, obj: jobject, writer: Writer) : (wr: Writer)
    requires v.Object? && obj == v.obj
    decreases v, 3
    ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
  {
    var writer := StructuralView(obj.l, writer);
    var writer := Members(v, obj, writer);
    var writer := StructuralView(obj.r, writer);

    // We call ``ConcatBytes`` with ``Spec.Member``, whereas the spec calls it
    // with ``(d: jmember) requires d in obj.data => Spec.Member(d)``.  That's
    // why we need an explicit cast, which is performed by the lemma below.
    SpecProperties.Bracketed_Morphism(obj);
    assert Spec.Value(v) == Spec.Bracketed(obj, Spec.Member);
    writer
  }

  function {:opaque} Array(v: Value, arr: jarray, writer: Writer) : (wr: Writer)
    requires v.Array? && arr == v.arr
    decreases v, 3
    ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
  {
    var writer := StructuralView(arr.l, writer);
    var writer := Items(v, arr, writer);
    var writer := StructuralView(arr.r, writer);

    // We call ``ConcatBytes`` with ``Spec.Item``, whereas the spec calls it
    // with ``(d: jitem) requires d in arr.data => Spec.Item(d)``.  That's
    // why we need an explicit cast, which is performed by the lemma below.
    SpecProperties.Bracketed_Morphism(arr); // DISCUSS
    assert Spec.Value(v) == Spec.Bracketed(arr, Spec.Item);
    writer
  }

  function {:opaque} Members(ghost v: Value, obj: jobject, writer: Writer) : (wr: Writer)
    requires obj < v
    decreases v, 2
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(obj.data, Spec.Member)
  {
    MembersSpec(v, obj.data, writer)
  } by method {
    wr := MembersImpl(v, obj, writer);
    Assume(false); // FIXME
  }

  function {:opaque} Items(ghost v: Value, arr: jarray, writer: Writer) : (wr: Writer)
    requires arr < v
    decreases v, 2
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(arr.data, Spec.Item)
  {
    ItemsSpec(v, arr.data, writer)
  } by method {
    wr := ItemsImpl(v, arr, writer);
    Assume(false); // FIXME
  }

  ghost function MembersSpec(v: Value, members: seq<jmember>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |members| :: members[j] < v
    decreases v, 1, members
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(members, Spec.Member)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Members.
    if members == [] then writer
    else
      var writer := MembersSpec(v, members[..|members|-1], writer);
      assert members == members[..|members|-1] + [members[|members|-1]];
      SpecProperties.ConcatBytes_Linear(members[..|members|-1], [members[|members|-1]], Spec.Member);
      Member(v, members[|members|-1], writer)
  } // No by method block here, because the loop invariant in the method version
    // needs to call MembersSpec and the termination checker gets confused by
    // that.  Instead, see Members above. // DISCUSS

  ghost function ItemsSpec(v: Value, items: seq<jitem>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |items| :: items[j] < v
    decreases v, 1, items
    ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, Spec.Item)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Items.
    if items == [] then writer
    else
      var writer := ItemsSpec(v, items[..|items|-1], writer);
      assert items == items[..|items|-1] + [items[|items|-1]];
      SpecProperties.ConcatBytes_Linear(items[..|items|-1], [items[|items|-1]], Spec.Item);
      Item(v, items[|items|-1], writer)
  } // No by method block here, because the loop invariant in the method version
    // needs to call ItemsSpec and the termination checker gets confused by
    // that.  Instead, see Items above. // DISCUSS

  method MembersImpl(ghost v: Value, obj: jobject, writer: Writer) returns (wr: Writer)
    requires obj < v
    decreases v, 1
    ensures wr == MembersSpec(v, obj.data, writer);
  {
    wr := writer;
    var members := obj.data;
    assert wr == MembersSpec(v, members[..0], writer);
    for i := 0 to |members| // FIXME uint32
      invariant wr == MembersSpec(v, members[..i], writer)
    {
      assert members[..i+1][..i] == members[..i];
      wr := Member(v, members[i], wr);
    }
    assert members[..|members|] == members;
  }

  method ItemsImpl(ghost v: Value, arr: jarray, writer: Writer) returns (wr: Writer)
    requires arr < v
    decreases v, 1
    ensures wr == ItemsSpec(v, arr.data, writer);
  {
    wr := writer;
    var items := arr.data;
    assert wr == ItemsSpec(v, items[..0], writer);
    for i := 0 to |items| // FIXME uint32
      invariant wr == ItemsSpec(v, items[..i], writer)
    {
      assert items[..i+1][..i] == items[..i];
      wr := Item(v, items[i], wr);
    }
    assert items[..|items|] == items;
  }

  function {:opaque} Member(ghost v: Value, m: jmember, writer: Writer) : (wr: Writer)
    requires m < v
    decreases v, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Member(m)
  {
    var writer := if m.prefix.Empty? then writer else StructuralView(m.prefix.t, writer);
    var writer := writer.Append(m.t.k);
    var writer := StructuralView(m.t.colon, writer);
    Value(m.t.v, writer)
  }

  function {:opaque} Item(ghost v: Value, m: jitem, writer: Writer) : (wr: Writer)
    requires m < v
    decreases v, 0
    ensures wr.Bytes() == writer.Bytes() + Spec.Item(m)
  {
    var wr := if m.prefix.Empty? then writer else StructuralView(m.prefix.t, writer);
    Value(m.t, wr)
  }
}
