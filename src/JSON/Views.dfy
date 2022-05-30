include "../BoundedInts.dfy"

module {:options "-functionSyntax:4"} Views.Core {
  import opened BoundedInts

  type View = v: View_ | v.Valid? witness View([], 0, 0)
  datatype View_ = View(s: bytes, beg: uint32, end: uint32) {
    ghost const Valid?: bool :=
      0 <= beg as int <= end as int <= |s| < TWO_TO_THE_32;

    static const Empty: View :=
      View([], 0, 0)

    const Empty? :=
      beg == end

    function Length(): uint32 requires Valid? {
      end - beg
    }

    function Bytes(): bytes requires Valid? {
      s[beg..end]
    }

    static function OfBytes(bs: bytes) : (v: View)
      requires |bs| < TWO_TO_THE_32
      ensures v.Bytes() == bs
    {
      View(bs, 0 as uint32, |bs| as uint32)
    }

    ghost predicate Byte?(c: byte)
      requires Valid?
    {
      Bytes() == [c]
    }

    ghost predicate Char?(c: char)
      requires Valid?
      requires c as int < 256
    {
      Byte?(c as byte)
    }

    ghost predicate ValidIndex?(idx: uint32) {
      beg as int + idx as int < end as int
    }

    function At(idx: uint32) : byte
      requires Valid?
      requires ValidIndex?(idx)
    {
      s[beg + idx]
    }

    method Blit(bs: array<byte>, start: uint32 := 0)
      requires Valid?
      requires start as int + Length() as int <= bs.Length
      requires start as int + Length() as int < TWO_TO_THE_32
      modifies bs
      ensures bs[start..start + Length()] == Bytes()
      ensures bs[start + Length()..] == old(bs[start + Length()..])
    {
      for idx := 0 to Length()
        invariant bs[start..start + idx] == Bytes()[..idx]
        invariant bs[start + Length()..] == old(bs[start + Length()..])
      {
        bs[start + idx] := s[beg + idx];
      }
    }
  }

  predicate Adjacent(lv: View, rv: View) {
    lv.s == rv.s &&
    lv.end == rv.beg
  }

  function Merge(lv: View, rv: View) : View
    requires Adjacent(lv, rv)
  {
    lv.(end := rv.end)
  }
}
