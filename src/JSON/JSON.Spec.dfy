include "JSON.Grammar.dfy"

module {:options "/functionSyntax:4"} JSON.Spec {
  import opened BoundedInts

  import Vs = Views.Core
  import opened Grammar

  function View(v: Vs.View) : bytes {
    v.Bytes()
  }

  function Structural<T>(self: Structural<T>, pt: T -> bytes): bytes {
    View(self.before) + pt(self.t) + View(self.after)
  }

  function StructuralView(self: Structural<Vs.View>): bytes {
    Structural<Vs.View>(self, View)
  }

  function Maybe<T>(self: Maybe<T>, pt: T -> bytes): (bs: bytes)
    ensures self.Empty? ==> bs == []
    ensures self.NonEmpty? ==> bs == pt(self.t)
  {
    if self.Empty? then [] else pt(self.t)
  }

  function ConcatBytes<T>(ts: seq<T>, pt: T --> bytes) : bytes
    requires forall d | d in ts :: pt.requires(d)
  {
    if |ts| == 0 then []
    else pt(ts[0]) + ConcatBytes(ts[1..], pt)
  }

  function Bracketed<S, D>(self: Bracketed<Vs.View, S, D, Vs.View>, pdatum: Prefixed<S, D> --> bytes): bytes
    requires forall d | d in self.data :: pdatum.requires(d)
  {
    StructuralView(self.l) +
    ConcatBytes(self.data, pdatum) +
    StructuralView(self.r)
  }

  function KV(self: jkv): bytes {
    View(self.k) + StructuralView(self.colon) + Value(self.v)
  }

  function Frac(self: jfrac): bytes {
    View(self.period) + View(self.num)
  }

  function Exp(self: jexp): bytes {
    View(self.e) + View(self.sign) + View(self.num)
  }

  function Member(self: jmember) : bytes {
    // BUG(https://github.com/dafny-lang/dafny/issues/2179)
    Maybe<Structural<Vs.View>>(self.prefix, StructuralView) + KV(self.t)
  }

  function Item(self: jitem) : bytes {
    // BUG(https://github.com/dafny-lang/dafny/issues/2179)
    Maybe<Structural<Vs.View>>(self.prefix, StructuralView) + Value(self.t)
  }

  function Value(self: Value): bytes {
    match self {
      case Null(n) =>
        View(n)
      case Bool(b) =>
        View(b)
      case String(str) =>
        View(str)
      case Number(minus, num, frac, exp) =>
        View(minus) + View(num) + Maybe(frac, Frac) + Maybe(exp, Exp)
      case Object(obj) =>
        Bracketed(obj, (d: jmember) requires d in obj.data => Member(d))
      case Array(arr) =>
        Bracketed(arr, (d: jitem) requires d in arr.data => Item(d))
    }
  }

  function JSON(js: JSON) : bytes {
    Structural(js, Value)
  }
}
