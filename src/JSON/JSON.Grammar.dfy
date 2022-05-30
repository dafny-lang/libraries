include "../BoundedInts.dfy"
include "Views.dfy"

module {:options "-functionSyntax:4"} JSON.Grammar {
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

  datatype Maybe<+T> = Empty() | NonEmpty(t: T)

  datatype Prefixed<+S, +T> =
    Prefixed(prefix: Maybe<Structural<S>>, t: T)

  type PrefixedSequence<+S, +D> = s: seq<Prefixed<S, D>> | NoLeadingPrefix(s)
  ghost predicate NoLeadingPrefix<S, D>(s: seq<Prefixed<S, D>>) {
    forall idx | 0 <= idx < |s| :: s[idx].prefix.Empty? <==> idx == 0
  }

  datatype Bracketed<+L, +S, +D, +R> =
    Bracketed(l: Structural<L>, data: PrefixedSequence<S, D>, r: Structural<R>)

  const NULL: bytes := ['n' as byte, 'u' as byte, 'l' as byte, 'l' as byte]
  const TRUE: bytes := ['t' as byte, 'r' as byte, 'u' as byte, 'e' as byte]
  const FALSE: bytes := ['f' as byte, 'a' as byte, 'l' as byte, 's' as byte, 'e' as byte]

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
  datatype jkv = KV(k: jstring, colon: Structural<jcolon>, v: Value)

  type jobject = Bracketed<jlbrace, jcomma, jkv, jrbrace>
  type jarray = Bracketed<jlbracket, jcomma, Value, jrbracket>
  type jmembers = PrefixedSequence<jcomma, jkv>
  type jmember = Prefixed<jcomma, jkv>
  type jitems = PrefixedSequence<jcomma, Value>
  type jitem = Prefixed<jcomma, Value>

  datatype jfrac = JFrac(period: jperiod, num: jnum)
  datatype jexp = JExp(e: je, sign: jsign, num: jnum)

  datatype Value =
    | Null(n: jnull)
    | Bool(b: jbool)
    | String(str: jstring)
    | Number(minus: jminus, num: jnum, frac: Maybe<jfrac>, exp: Maybe<jexp>)
    | Object(obj: jobject)
    | Array(arr: jarray)

  type JSON = Structural<Value>
}
