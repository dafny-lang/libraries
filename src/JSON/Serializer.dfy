include "../BoundedInts.dfy"
include "../Wrappers.dfy"
include "Grammar.dfy"
include "Views.Writers.dfy"
include "Stacks.dfy"

module {:options "/functionSyntax:4"} JSON.Serializer {
  import opened BoundedInts
  import opened Wrappers

  import opened Grammar
  import opened Views.Writers
  import opened Vs = Views.Core // DISCUSS: Module naming convention?

  datatype Error = OutOfMemory

  method Serialize(js: JSON) returns (bsr: Result<array<byte>, Error>)
    ensures bsr.Success? ==> bsr.value[..] == Bytes(js)
  {
    var writer := JSON(js);
    :- Need(writer.Unsaturated?, OutOfMemory);
    var bs := writer.ToArray();
    return Success(bs);
  }

  function {:opaque} JSON(js: JSON, writer: Writer := Writer.Empty) : (wr: Writer)
    ensures wr.Bytes() == writer.Bytes() + Bytes(js)
  {
    // DISCUSS: This doesn't work:
    // writer
    //   .Append(js.before)
    //   .Then(wr => Value(js.t, wr))
    //   .Append(js.after)
    // … but this does:
    var wr := writer;
    var wr := wr.Append(js.before);
    var wr := Value(js.t, wr);
    var wr := wr.Append(js.after);
    wr
  }

  function {:opaque} Value(v: Value, writer: Writer) : (wr: Writer)
    decreases v, 4
    ensures wr.Bytes() == writer.Bytes() + v.Bytes()
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
    ensures wr.Bytes() == writer.Bytes() + v.Bytes()
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
  function Structural(st: Structural<View>, writer: Writer) : (wr: Writer)
    // FIXME ensures writer.Length() + |st.Bytes((v: View) => v.Bytes())| < TWO_TO_THE_32 ==> rwr.Success?
    ensures wr.Bytes() == writer.Bytes() + st.Bytes((v: View) => v.Bytes())
  {
    writer.Append(st.before).Append(st.t).Append(st.after)
  }

  lemma Bracketed_Morphism<L, S, D, R>(bracketed: Bracketed<L, S, D, R>) // DISCUSS
    ensures forall
        pl0: L -> bytes,  pd0: Prefixed<S, D> --> bytes,  pr0:  R -> bytes,
        pl1: L -> bytes, pd1: Prefixed<S, D> --> bytes, pr1: R -> bytes
      | && (forall d | d in bracketed.data :: pd0.requires(d))
        && (forall d | d in bracketed.data :: pd1.requires(d))
        && (forall d | d in bracketed.data :: pd0(d) == pd1(d))
        && (forall l :: pl0(l) == pl1(l))
        && (forall r :: pr0(r) == pr1(r))
      :: bracketed.Bytes(pl0, pd0, pr0) == bracketed.Bytes(pl1, pd1, pr1)
  {
    forall pl0: L -> bytes,  pd0: Prefixed<S, D> --> bytes,  pr0:  R -> bytes,
           pl1: L -> bytes, pd1: Prefixed<S, D> --> bytes, pr1: R -> bytes
      | && (forall d | d in bracketed.data :: pd0.requires(d))
        && (forall d | d in bracketed.data :: pd1.requires(d))
        && (forall d | d in bracketed.data :: pd0(d) == pd1(d))
        && (forall l :: pl0(l) == pl1(l))
        && (forall r :: pr0(r) == pr1(r))
    {
      calc {
        bracketed.Bytes(pl0, pd0, pr0);
        { ConcatBytes_Morphism(bracketed.data, pd0, pd1); }
        bracketed.Bytes(pl1, pd1, pr1);
      }
    }
  }

  lemma {:induction ts} ConcatBytes_Morphism<T>(ts: seq<T>, pt0: T --> bytes, pt1: T --> bytes)
    requires forall d | d in ts :: pt0.requires(d)
    requires forall d | d in ts :: pt1.requires(d)
    requires forall d | d in ts :: pt0(d) == pt1(d)
    ensures ConcatBytes(ts, pt0) == ConcatBytes(ts, pt1)
  {}

  lemma {:induction ts0} ConcatBytes_Linear<T>(ts0: seq<T>, ts1: seq<T>, pt: T --> bytes)
    requires forall d | d in ts0 :: pt.requires(d)
    requires forall d | d in ts1 :: pt.requires(d)
    ensures ConcatBytes(ts0 + ts1, pt) == ConcatBytes(ts0, pt) + ConcatBytes(ts1, pt)
  {
    if |ts0| == 0 {
      assert [] + ts1 == ts1;
    } else {
      assert ts0 + ts1 == [ts0[0]] + (ts0[1..] + ts1);
    }
  }

  lemma {:axiom} Assume(b: bool) ensures b

  function {:opaque} Object(v: Value, obj: jobject, writer: Writer) : (wr: Writer)
    requires v.Object? && obj == v.obj
    decreases v, 3
    ensures wr.Bytes() == writer.Bytes() + v.Bytes()
  {
    var writer := Structural(obj.l, writer);
    var writer := Members(v, obj, writer);
    var writer := Structural(obj.r, writer);

    Bracketed_Morphism(obj); // DISCUSS
    assert v.Bytes() == obj.Bytes(((l: jlbrace) => l.Bytes()), Grammar.Member, ((r: jrbrace) => r.Bytes()));

    writer
  }

  function {:opaque} Array(v: Value, arr: jarray, writer: Writer) : (wr: Writer)
    requires v.Array? && arr == v.arr
    decreases v, 3
    ensures wr.Bytes() == writer.Bytes() + v.Bytes()
  {
    var writer := Structural(arr.l, writer);
    var writer := Items(v, arr, writer);
    var writer := Structural(arr.r, writer);

    Bracketed_Morphism(arr); // DISCUSS
    assert v.Bytes() == arr.Bytes(((l: jlbracket) => l.Bytes()), Grammar.Item, ((r: jrbracket) => r.Bytes()));

    writer
  }

  function {:opaque} Members(ghost v: Value, obj: jobject, writer: Writer) : (wr: Writer)
    requires obj < v
    decreases v, 2
    ensures wr.Bytes() == writer.Bytes() + ConcatBytes(obj.data, Grammar.Member)
    ensures wr == MembersSpec(v, obj.data, writer)
  {
    MembersSpec(v, obj.data, writer)
  } by method {
    wr := MembersImpl(v, obj, writer);
    Assume(false); // FIXME
  }

  ghost function MembersSpec(v: Value, members: seq<jmember>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |members| :: members[j] < v
    decreases v, 1, members
    ensures wr.Bytes() == writer.Bytes() + ConcatBytes(members, Grammar.Member)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Members.
    if members == [] then writer
    else
      var writer := MembersSpec(v, members[..|members|-1], writer);
      assert members == members[..|members|-1] + [members[|members|-1]];
      ConcatBytes_Linear(members[..|members|-1], [members[|members|-1]], Grammar.Member);
      Member(v, members[|members|-1], writer)
  } // No by method block here, because the loop invariant in the method version
    // needs to call MembersSpec and the termination checker gets confused by
    // that.  Instead, see Members above. // DISCUSS

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

  function {:opaque} Member(ghost v: Value, m: jmember, writer: Writer) : (wr: Writer)
    requires m < v
    decreases v, 0
    ensures wr.Bytes() == writer.Bytes() + Grammar.Member(m)
  {
    var writer := if m.prefix.NonEmpty? then Structural(m.prefix.t, writer) else writer;
    var writer := writer.Append(m.t.k);
    var writer := Structural(m.t.colon, writer);
    Value(m.t.v, writer)
  }
  function {:opaque} Items(ghost v: Value, arr: jarray, writer: Writer) : (wr: Writer)
    requires arr < v
    decreases v, 2
    ensures wr.Bytes() == writer.Bytes() + ConcatBytes(arr.data, Grammar.Item)
    ensures wr == ItemsSpec(v, arr.data, writer)
  {
    ItemsSpec(v, arr.data, writer)
  } by method {
    wr := ItemsImpl(v, arr, writer);
    Assume(false); // FIXME
  }

  ghost function ItemsSpec(v: Value, items: seq<jitem>, writer: Writer) : (wr: Writer)
    requires forall j | 0 <= j < |items| :: items[j] < v
    decreases v, 1, items
    ensures wr.Bytes() == writer.Bytes() + ConcatBytes(items, Grammar.Item)
  { // TR elimination doesn't work for mutually recursive methods, so this
    // function is only used as a spec for Items.
    if items == [] then writer
    else
      var writer := ItemsSpec(v, items[..|items|-1], writer);
      assert items == items[..|items|-1] + [items[|items|-1]];
      ConcatBytes_Linear(items[..|items|-1], [items[|items|-1]], Grammar.Item);
      Item(v, items[|items|-1], writer)
  } // No by method block here, because the loop invariant in the method version
    // needs to call ItemsSpec and the termination checker gets confused by
    // that.  Instead, see Items above. // DISCUSS

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

  function {:opaque} Item(ghost v: Value, m: jitem, writer: Writer) : (wr: Writer)
    requires m < v
    decreases v, 0
    ensures wr.Bytes() == writer.Bytes() + Grammar.Item(m)
  {
    var writer := if m.prefix.NonEmpty? then Structural(m.prefix.t, writer) else writer;
    Value(m.t, writer)
  }


}
