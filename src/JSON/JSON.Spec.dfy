include "JSON.Grammar.dfy"

module {:options "-functionSyntax:4"} JSON.Spec {
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

  function Bracketed<D, S>(self: Bracketed<Vs.View, D, S, Vs.View>, pdatum: Suffixed<D, S> --> bytes): bytes
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

  function Number(self: jnumber): bytes {
    View(self.minus) + View(self.num) + Maybe(self.frac, Frac) + Maybe(self.exp, Exp)
  }

  function String(self: jstring): bytes {
    View(self)
  }

  function CommaSuffix(c: Maybe<Structural<jcomma>>): bytes {
    // BUG(https://github.com/dafny-lang/dafny/issues/2179)
    Maybe<Structural<Vs.View>>(c, StructuralView)
  }

  function Member(self: jmember) : bytes {
    KV(self.t) + CommaSuffix(self.suffix)
  }

  function Item(self: jitem) : bytes {
    Value(self.t) + CommaSuffix(self.suffix)
  }

  function Object(obj: jobject) : bytes {
    Bracketed(obj, (d: jmember) requires d in obj.data => Member(d))
  }

  function Array(arr: jarray) : bytes {
    Bracketed(arr, (d: jitem) requires d in arr.data => Item(d))
  }

  function Value(self: Value) : bytes {
    match self {
      case Null(n) => View(n)
      case Bool(b) => View(b)
      case String(str) => String(str)
      case Number(num) => Number(num)
      case Object(obj) => Object(obj)
      case Array(arr) => Array(arr)
    }
  }

  function JSON(js: JSON) : bytes {
    Structural(js, Value)
  }
}
