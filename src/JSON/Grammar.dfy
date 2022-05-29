include "../BoundedInts.dfy"
include "Views.dfy"

module {:options "/functionSyntax:4"} JSON.Grammar {
  import opened BoundedInts
  import opened Views.Core

  type jchar = v: View | v.Length() == 1 witness View.OfBytes(['b' as byte])
  type jperiod = v: View | v.Char?('.') witness View.OfBytes(['.' as byte])
  type je = v: View | v.Char?('e') || v.Char?('E') witness View.OfBytes(['e' as byte])
  type jcolon = v: View | v.Char?(':') witness View.OfBytes([':' as byte])
  type jcomma = v: View | v.Char?(',') witness View.OfBytes([',' as byte])
  type jlbrace = v: View | v.Char?('{') witness View.OfBytes(['{' as byte])
  type jrbrace = v: View | v.Char?('}') witness View.OfBytes(['}' as byte])
  type jlbracket = v: View | v.Char?('[') witness View.OfBytes(['[' as byte])
  type jrbracket = v: View | v.Char?(']') witness View.OfBytes([']' as byte])
  type jminus = v: View | v.Char?('-') || v.Empty? witness View.OfBytes([])
  type jsign = v: View | v.Char?('-') || v.Char?('+') || v.Empty? witness View.OfBytes([])

  predicate Blank?(b: byte) { b == 0x20 || b == 0x09 || b == 0x0A || b == 0x0D }
  ghost predicate Blanks?(v: View) { forall b | b in v.Bytes() :: Blank?(b) }
  type jblanks = v: View | Blanks?(v) witness View.OfBytes([])

  datatype Structural<+T> =
    Structural(before: jblanks, t: T, after: jblanks)
  {
    function Bytes(pt: T -> bytes): bytes { // LATER: Trait
      before.Bytes() + pt(t) + after.Bytes()
    }
  }

  function ConcatBytes<T>(ts: seq<T>, pt: T --> bytes) : bytes
    requires forall d | d in ts :: pt.requires(d)
  {
    if |ts| == 0 then []
    else pt(ts[0]) + ConcatBytes(ts[1..], pt)
  }

  // FIXME remove empty
  datatype Maybe<+T> = Empty() | NonEmpty(t: T) {
    function Bytes(pt: T --> bytes): bytes
      requires NonEmpty? ==> pt.requires(t)
    { // LATER: Trait
      match this
        case Empty() => []
        case NonEmpty(t) => pt(t)
    }
  }

  datatype Prefixed<+S, +T> =
    Prefixed(before: Maybe<Structural<S>>, t: T)
  {
    function Bytes(psep: S -> bytes, pt: T --> bytes): bytes
      requires pt.requires(t)
    { // LATER: Trait
      before.Bytes((s: Structural<S>) => s.Bytes(psep)) + pt(t)
    }
  }

  type PrefixedSequence<+S, +D> = s: seq<Prefixed<S, D>> | NoLeadingPrefix(s)
  ghost predicate NoLeadingPrefix<S, D>(s: seq<Prefixed<S, D>>) {
    forall idx | 0 <= idx < |s| :: s[idx].before.Empty? <==> idx == 0
  }

  datatype Bracketed<+L, +S, +D, +R> =
    Bracketed(l: Structural<L>, data: PrefixedSequence<S, D>, r: Structural<R>)
  {
    function Bytes(pl: L -> bytes, pdatum: Prefixed<S, D> --> bytes, pr: R -> bytes): bytes
      requires forall d | d in data :: pdatum.requires(d)
    { // LATER: Trait
      l.Bytes(pl) +
      ConcatBytes(data, pdatum) +
      r.Bytes(pr)
    }
  }

  function BytesOfString(str: string) : bytes
    requires forall c | c in str :: c as int < 256
  {
    seq(|str|, idx requires 0 <= idx < |str| => assert str[idx] in str; str[idx] as byte)
  }

  const NULL: bytes := BytesOfString("null")
  const TRUE: bytes := BytesOfString("true")
  const FALSE: bytes := BytesOfString("false")

  ghost predicate Null?(v: View) { v.Bytes() == NULL }
  ghost predicate Bool?(v: View) { v.Bytes() in {TRUE, FALSE} }
  predicate Digit?(b: byte) { '0' as byte <= b <= '9' as byte }
  ghost predicate Digits?(v: View) { forall b | b in v.Bytes() :: Digit?(b) }
  ghost predicate Num?(v: View) { Digits?(v) && !v.Empty? }
  ghost predicate Int?(v: View) { v.Char?('0') || (Num?(v) && v.At(0) != '0' as byte) }

  type jstring = v: View | true witness View.OfBytes([]) // TODO: Enforce correct escaping
  type jnull = v: View | Null?(v) witness View.OfBytes(NULL)
  type jbool = v: View | Bool?(v) witness View.OfBytes(TRUE)
  type jdigits = v: View | Digits?(v) witness View.OfBytes([])
  type jnum = v: View | Num?(v) witness View.OfBytes(['0' as byte])
  type jint = v: View | Int?(v) witness View.OfBytes(['0' as byte])

  datatype jkv = KV(k: jstring, colon: Structural<jcolon>, v: Value) {
    function Bytes(): bytes {
      k.Bytes() + colon.Bytes((c: jcolon) => c.Bytes()) + v.Bytes()
    }
  }

  type jobject = Bracketed<jlbrace, jcomma, jkv, jrbrace>
  type jarray = Bracketed<jlbracket, jcomma, Value, jrbracket>

  datatype jfrac = JFrac(period: jperiod, num: jnum) {
    function Bytes(): bytes {
      period.Bytes() + num.Bytes()
    }
  }
  datatype jexp = JExp(e: je, sign: jsign, num: jnum) {
    function Bytes(): bytes {
      e.Bytes() + sign.Bytes() + num.Bytes()
    }
  }

  datatype Value =
    | Null(n: jnull)
    | Bool(b: jbool)
    | String(str: jstring)
    | Number(minus: jminus, num: jnum, frac: Maybe<jfrac>, exp: Maybe<jexp>)
    | Object(obj: jobject)
    | Array(arr: jarray)
  {
    function Bytes(): bytes {
      match this {
        case Null(n) =>
          n.Bytes()
        case Bool(b) =>
          b.Bytes()
        case String(str) =>
          str.Bytes()
        case Number(minus, num, frac, exp) =>
          minus.Bytes() + num.Bytes() +
          frac.Bytes((f: jfrac) => f.Bytes()) +
          exp.Bytes((e: jexp) => e.Bytes())
        case Object(o) =>
          o.Bytes((l: jlbrace) => l.Bytes(),
                  (d: Prefixed<jcomma, jkv>) requires d in o.data =>
                    d.Bytes((s: jcomma) => s.Bytes(), // BUG(https://github.com/dafny-lang/dafny/issues/2170)
                            var pt := (kv: jkv) requires kv == d.t => d.t.Bytes();
                            assert pt.requires(d.t);
                            pt),
                  (r: jrbrace) => r.Bytes())
        case Array(a) =>
          a.Bytes((l: jlbracket) => l.Bytes(),
                  (d: Prefixed<jcomma, Value>) requires d in a.data =>
                    d.Bytes((s: jcomma) => s.Bytes(),
                            var pt := (v: Value) requires v == d.t => v.Bytes();
                            assert pt.requires(d.t);
                            pt),
                  (r: jrbracket) => r.Bytes())
      }
    }
  }

  type JSON = Structural<Value>
  function Bytes(js: JSON) : bytes { // TODO: TR
    js.Bytes((v: Value) => v.Bytes())
  }
}
