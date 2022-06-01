// Dafny program Benchmark.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
[assembly: DafnyAssembly.DafnySourceAttribute(@"// Dafny 3.6.0.40511
// Command Line Options: Benchmark.dfy /useRuntimeLib /noVerify /spillTargetCode:3
// Benchmark.dfy


module {:extern ""Benchmarks""} Benchmarks {

  import opened BoundedInts

  import opened Grammar = JSON.Grammar

  import Serializer = JSON.ZeroCopy.Serializer

  import Deserializer = JSON.ZeroCopy.Deserializer

  import API = JSON.ZeroCopy.API
  class {:extern} {:compile false} Interop {
    static method {:extern} ReadInput() returns (s: array<byte>)
      ensures fresh(s)

    static method {:extern} StartTimer()

    static method {:extern} ReportTimer(lbl: string, nBytes: int, repeats: uint32)
      decreases lbl, nBytes, repeats
  }

  const WARMUP: uint32 := 0
  const REPEATS: uint32 := 10

  method Serialize(bytes: seq<byte>)
    decreases bytes
  {
    for i: uint32 := 0 to WARMUP {
      var _ := API.Deserialize(bytes);
    }
    Interop.StartTimer();
    for i: uint32 := 0 to REPEATS {
      var _ := API.Deserialize(bytes);
    }
    Interop.ReportTimer(""Serialize"", |bytes|, REPEATS);
  }

  method Deserialize(js: JSON, target: array<byte>)
    modifies target
    decreases js, target
  {
    for i: uint32 := 0 to WARMUP {
      var _ := API.SerializeBlit(js, target);
    }
    Interop.StartTimer();
    for i: uint32 := 0 to REPEATS {
      var _ := API.SerializeBlit(js, target);
    }
    Interop.ReportTimer(""Deserialize"", target.Length, REPEATS);
  }

  method Main()
  {
    var input_array := Interop.ReadInput();
    var output_array := new byte[input_array.Length];
    var bytes := input_array[..];
    var jsr := API.Deserialize(bytes);
    expect jsr.Success?, ""expectation violation""
    var js := jsr.value;
    var output := API.SerializeAlloc(js);
    expect output.Success?, ""expectation violation""
    Serialize(bytes);
    Deserialize(js, output_array);
  }
}

module BoundedInts {
  newtype uint8 = x: int
    | 0 <= x < TWO_TO_THE_8

  newtype uint16 = x: int
    | 0 <= x < TWO_TO_THE_16

  newtype uint32 = x: int
    | 0 <= x < TWO_TO_THE_32

  newtype uint64 = x: int
    | 0 <= x < TWO_TO_THE_64

  newtype int8 = x: int
    | -128 <= x < 128

  newtype int16 = x: int
    | -32768 <= x < 32768

  newtype int32 = x: int
    | -2147483648 <= x < 2147483648

  newtype int64 = x: int
    | -9223372036854775808 <= x < 9223372036854775808

  newtype nat8 = x: int
    | 0 <= x < 128

  newtype nat16 = x: int
    | 0 <= x < 32768

  newtype nat32 = x: int
    | 0 <= x < 2147483648

  newtype nat64 = x: int
    | 0 <= x < 9223372036854775808

  type byte = uint8

  type bytes = seq<byte>

  newtype opt_byte = c: int
    | -1 <= c < TWO_TO_THE_8

  const TWO_TO_THE_0: int := 1
  const TWO_TO_THE_1: int := 2
  const TWO_TO_THE_2: int := 4
  const TWO_TO_THE_4: int := 16
  const TWO_TO_THE_5: int := 32
  const TWO_TO_THE_8: int := 256
  const TWO_TO_THE_16: int := 65536
  const TWO_TO_THE_24: int := 16777216
  const TWO_TO_THE_32: int := 4294967296
  const TWO_TO_THE_40: int := 1099511627776
  const TWO_TO_THE_48: int := 281474976710656
  const TWO_TO_THE_56: int := 72057594037927936
  const TWO_TO_THE_64: int := 18446744073709551616
  const TWO_TO_THE_128: int := 340282366920938463463374607431768211456
  const TWO_TO_THE_256: int := 115792089237316195423570985008687907853269984665640564039457584007913129639936
  const TWO_TO_THE_512: int := 13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096
  const UINT8_MAX: uint8 := 255
  const UINT16_MAX: uint16 := 65535
  const UINT32_MAX: uint32 := 4294967295
  const UINT64_MAX: uint64 := 18446744073709551615
  const INT8_MIN: int8 := -128
  const INT8_MAX: int8 := 127
  const INT16_MIN: int16 := -32768
  const INT16_MAX: int16 := 32767
  const INT32_MIN: int32 := -2147483648
  const INT32_MAX: int32 := 2147483647
  const INT64_MIN: int64 := -9223372036854775808
  const INT64_MAX: int64 := 9223372036854775807
  const NAT8_MAX: nat8 := 127
  const NAT16_MAX: nat16 := 32767
  const NAT32_MAX: nat32 := 2147483647
  const NAT64_MAX: nat64 := 9223372036854775807
}

module {:options ""/functionSyntax:4""} Parsers {

  import opened BoundedInts

  import opened Wrappers

  import opened Core = Views.Core

  import opened Cursors
  type SplitResult<+T, +R> = CursorResult<Split<T>, R>

  type Parser<!T, +R> = p: Parser_<T, R>
    | p.Valid?()
    witness ParserWitness<T, R>()

  datatype Parser_<!T, +R> = Parser(fn: FreshCursor -> SplitResult<T, R>, ghost spec: T -> bytes) {
    predicate Valid?()
      decreases this
    {
      forall cs': FreshCursor :: 
        fn(cs').Success? ==>
          fn(cs').value.StrictlySplitFrom?(cs', spec)
    }
  }

  datatype SubParser_<!T, +R> = SubParser(ghost cs: Cursor, ghost pre: FreshCursor -> bool, fn: FreshCursor --> SplitResult<T, R>, ghost spec: T -> bytes) {
    predicate Valid?()
      decreases this
    {
      (forall cs': FreshCursor | pre(cs') :: 
        fn.requires(cs')) &&
      (forall cs': FreshCursor | cs'.StrictlySplitFrom?(cs) :: 
        pre(cs')) &&
      forall cs': FreshCursor | pre(cs') :: 
        fn(cs').Success? ==>
          fn(cs').value.StrictlySplitFrom?(cs', spec)
    }
  }

  type SubParser<!T, +R> = p: SubParser_<T, R>
    | p.Valid?()
    witness SubParserWitness<T, R>()

  function method {:opaque} {:fuel 0, 0} ParserWitness<T, R>(): (p: Parser_<T, R>)
    ensures p.Valid?()
  {
    Parser((_: FreshCursor) => Failure(EOF), (_: T) => [])
  }

  function method {:opaque} {:fuel 0, 0} SubParserWitness<T, R>(): (subp: SubParser_<T, R>)
    ensures subp.Valid?()
  {
    SubParser(Cursor([], 0, 0, 0), (cs: FreshCursor) => false, (cs: FreshCursor) => Failure(EOF), (_: T) => [])
  }
}

module Wrappers {
  datatype Option<+T> = None | Some(value: T) {
    function method ToResult(): Result<T, string>
      decreases this
    {
      match this
      case Some(v) =>
        Success(v)
      case None() =>
        Failure(""Option is None"")
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Some(v) =>
        v
      case None() =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      None?
    }

    function method PropagateFailure<U>(): Option<U>
      requires None?
      decreases this
    {
      None
    }

    function method Extract(): T
      requires Some?
      decreases this
    {
      value
    }
  }

  datatype Result<+T, +R> = Success(value: T) | Failure(error: R) {
    function method ToOption(): Option<T>
      decreases this
    {
      match this
      case Success(s) =>
        Some(s)
      case Failure(e) =>
        None()
    }

    function method UnwrapOr(default: T): T
      decreases this
    {
      match this
      case Success(s) =>
        s
      case Failure(e) =>
        default
    }

    predicate method IsFailure()
      decreases this
    {
      Failure?
    }

    function method PropagateFailure<U>(): Result<U, R>
      requires Failure?
      decreases this
    {
      Failure(this.error)
    }

    function method MapFailure<NewR>(reWrap: R -> NewR): Result<T, NewR>
      decreases this
    {
      match this
      case Success(s) =>
        Success(s)
      case Failure(e) =>
        Failure(reWrap(e))
    }

    function method Extract(): T
      requires Success?
      decreases this
    {
      value
    }
  }

  datatype Outcome<E> = Pass | Fail(error: E) {
    predicate method IsFailure()
      decreases this
    {
      Fail?
    }

    function method PropagateFailure<U>(): Result<U, E>
      requires Fail?
      decreases this
    {
      Failure(this.error)
    }
  }

  function method Need<E>(condition: bool, error: E): (result: Outcome<E>)
    decreases condition
  {
    if condition then
      Pass
    else
      Fail(error)
  }
}

module {:options ""/functionSyntax:4""} Cursors {

  import opened BoundedInts

  import opened Wrappers

  import opened Vs = Views.Core

  import opened Lx = Lexers.Core
  datatype Split<+T> = SP(t: T, cs: FreshCursor) {
    predicate BytesSplitFrom?(cs0: Cursor, spec: T -> bytes)
      decreases this, cs0
    {
      cs0.Bytes() == spec(t) + cs.Bytes()
    }

    predicate SplitFrom?(cs0: Cursor, spec: T -> bytes)
      decreases this, cs0
    {
      cs.SplitFrom?(cs0) &&
      BytesSplitFrom?(cs0, spec)
    }

    predicate StrictlySplitFrom?(cs0: Cursor, spec: T -> bytes)
      decreases this, cs0
    {
      cs.StrictlySplitFrom?(cs0) &&
      BytesSplitFrom?(cs0, spec)
    }
  }

  type Cursor = ps: Cursor_
    | ps.Valid?
    witness Cursor([], 0, 0, 0)

  type FreshCursor = ps: Cursor
    | ps.BOF?
    witness Cursor([], 0, 0, 0)

  datatype CursorError<+R> = EOF | ExpectingByte(expected: byte, b: opt_byte) | ExpectingAnyByte(expected_sq: seq<byte>, b: opt_byte) | OtherError(err: R) {
    function method ToString(pr: R -> string): string
      decreases this
    {
      match this
      case EOF() =>
        ""Reached EOF""
      case ExpectingByte(b0, b) =>
        var c := if b > 0 then ""'"" + [b as char] + ""'"" else ""EOF"";
        ""Expecting '"" + [b0 as char] + ""', read "" + c
      case ExpectingAnyByte(bs0, b) =>
        var c := if b > 0 then ""'"" + [b as char] + ""'"" else ""EOF"";
        var c0s := seq(|bs0|, idx requires 0 <= idx < |bs0| => bs0[idx] as char);
        ""Expecting one of '"" + c0s + ""', read "" + c
      case OtherError(err) =>
        pr(err)
    }
  }

  type CursorResult<+T, +R> = Result<T, CursorError<R>>

  datatype Cursor_ = Cursor(s: bytes, beg: uint32, point: uint32, end: uint32) {
    ghost const Valid?: bool := 0 <= beg as int <= point as int <= end as int <= |s| < TWO_TO_THE_32
    const BOF? := point == beg
    const EOF? := point == end

    static function method OfView(v: View): FreshCursor
      decreases v
    {
      Cursor(v.s, v.beg, v.beg, v.end)
    }

    static function method OfBytes(bs: bytes): FreshCursor
      requires |bs| < TWO_TO_THE_32
      decreases bs
    {
      Cursor(bs, 0, |bs| as uint32, |bs| as uint32)
    }

    function method Bytes(): bytes
      requires Valid?
      decreases this
    {
      s[beg .. end]
    }

    function StrictlyAdvancedFrom?(other: Cursor): (b: bool)
      requires Valid?
      ensures b ==> SuffixLength() < other.SuffixLength()
      ensures b ==> beg == other.beg && end == other.end ==> forall idx: uint32 | beg <= idx < point :: s[idx] == other.s[idx]
      decreases this, other
    {
      s == other.s &&
      beg == other.beg &&
      end == other.end &&
      point > other.point
    }

    predicate AdvancedFrom?(other: Cursor)
      requires Valid?
      decreases this, other
    {
      this == other || StrictlyAdvancedFrom?(other)
    }

    predicate StrictSuffixOf?(other: Cursor)
      requires Valid?
      ensures StrictSuffixOf?(other) ==> Length() < other.Length()
      decreases this, other
    {
      s == other.s &&
      beg > other.beg &&
      end == other.end
    }

    predicate SuffixOf?(other: Cursor)
      requires Valid?
      decreases this, other
    {
      this == other || StrictSuffixOf?(other)
    }

    predicate StrictlySplitFrom?(other: Cursor)
      requires Valid?
      decreases this, other
    {
      BOF? &&
      StrictSuffixOf?(other)
    }

    predicate SplitFrom?(other: Cursor)
      requires Valid?
      decreases this, other
    {
      this == other || StrictlySplitFrom?(other)
    }

    function method Prefix(): View
      requires Valid?
      decreases this
    {
      View(s, beg, point)
    }

    function method Suffix(): Cursor
      requires Valid?
      decreases this
    {
      this.(beg := point)
    }

    function method Split(): (sp: Split<View>)
      requires Valid?
      ensures sp.SplitFrom?(this, (v: View) => v.Bytes())
      ensures beg != point ==> sp.StrictlySplitFrom?(this, (v: View) => v.Bytes())
      decreases this
    {
      SP(this.Prefix(), this.Suffix())
    }

    function method PrefixLength(): uint32
      requires Valid?
      decreases this
    {
      point - beg
    }

    function method SuffixLength(): uint32
      requires Valid?
      decreases this
    {
      end - point
    }

    function method Length(): uint32
      requires Valid?
      decreases this
    {
      end - beg
    }

    predicate ValidIndex?(idx: uint32)
      decreases this, idx
    {
      beg as int + idx as int < end as int
    }

    function method At(idx: uint32): byte
      requires Valid?
      requires ValidIndex?(idx)
      decreases this, idx
    {
      s[beg + idx]
    }

    predicate ValidSuffixIndex?(idx: uint32)
      decreases this, idx
    {
      point as int + idx as int < end as int
    }

    function method SuffixAt(idx: uint32): byte
      requires Valid?
      requires ValidSuffixIndex?(idx)
      decreases this, idx
    {
      s[point + idx]
    }

    function method Peek(): (r: opt_byte)
      requires Valid?
      ensures r < 0 <==> EOF?
      decreases this
    {
      if EOF? then
        -1
      else
        SuffixAt(0) as opt_byte
    }

    function method LookingAt(c: char): (b: bool)
      requires Valid?
      requires c as int < 256
      ensures b <==> !EOF? && SuffixAt(0) == c as byte
      decreases this, c
    {
      Peek() == c as opt_byte
    }

    function method Skip(n: uint32): (ps: Cursor)
      requires Valid?
      requires point as int + n as int <= end as int
      ensures n == 0 ==> ps == this
      ensures n > 0 ==> ps.StrictlyAdvancedFrom?(this)
      decreases this, n
    {
      this.(point := point + n)
    }

    function method Unskip(n: uint32): Cursor
      requires Valid?
      requires beg as int <= point as int - n as int
      decreases this, n
    {
      this.(point := point - n)
    }

    function method Get<R>(err: R): (ppr: CursorResult<Cursor, R>)
      requires Valid?
      ensures ppr.Success? ==> ppr.value.StrictlyAdvancedFrom?(this)
      decreases this
    {
      if EOF? then
        Failure(OtherError(err))
      else
        Success(Skip(1))
    }

    function method AssertByte<R>(b: byte): (pr: CursorResult<Cursor, R>)
      requires Valid?
      ensures pr.Success? ==> !EOF?
      ensures pr.Success? ==> s[point] == b
      ensures pr.Success? ==> pr.value.StrictlyAdvancedFrom?(this)
      decreases this, b
    {
      var nxt: opt_byte := Peek();
      if nxt == b as opt_byte then
        Success(Skip(1))
      else
        Failure(ExpectingByte(b, nxt))
    }

    function method {:tailrecursion} AssertBytes<R>(bs: bytes, offset: uint32 := 0): (pr: CursorResult<Cursor, R>)
      requires Valid?
      requires |bs| < TWO_TO_THE_32
      requires offset <= |bs| as uint32
      requires forall b: uint8 | b in bs :: b as int < 256
      ensures pr.Success? ==> pr.value.AdvancedFrom?(this)
      ensures pr.Success? && offset < |bs| as uint32 ==> pr.value.StrictlyAdvancedFrom?(this)
      ensures pr.Success? ==> s[point .. pr.value.point] == bs[offset..]
      decreases SuffixLength()
    {
      if offset == |bs| as uint32 then
        Success(this)
      else
        var ps: Cursor :- AssertByte(bs[offset] as byte); ps.AssertBytes(bs, offset + 1)
    }

    function method AssertChar<R>(c0: char): (pr: CursorResult<Cursor, R>)
      requires Valid?
      requires c0 as int < 256
      ensures pr.Success? ==> pr.value.StrictlyAdvancedFrom?(this)
      decreases this, c0
    {
      AssertByte(c0 as byte)
    }

    function method SkipByte(): (ps: Cursor)
      requires Valid?
      ensures ps.AdvancedFrom?(this)
      ensures !EOF? ==> ps.StrictlyAdvancedFrom?(this)
      decreases SuffixLength()
    {
      if EOF? then
        this
      else
        Skip(1)
    }

    function method SkipIf(p: byte -> bool): (ps: Cursor)
      requires Valid?
      ensures ps.AdvancedFrom?(this)
      ensures !EOF? && p(SuffixAt(0)) ==> ps.StrictlyAdvancedFrom?(this)
      decreases SuffixLength()
    {
      if EOF? || !p(SuffixAt(0)) then
        this
      else
        Skip(1)
    }

    function method SkipWhile(p: byte -> bool): (ps: Cursor)
      requires Valid?
      ensures ps.AdvancedFrom?(this)
      ensures forall idx: uint32 | point <= idx < ps.point :: p(ps.s[idx])
      decreases SuffixLength()
    {
      if EOF? || !p(SuffixAt(0)) then
        this
      else
        Skip(1).SkipWhile(p)
    }

    function method SkipWhileLexer<A, R>(step: Lexer<A, R>, st: LexerState<A, R>): (pr: CursorResult<Cursor, R>)
      requires Valid?
      ensures pr.Success? ==> pr.value.AdvancedFrom?(this)
      decreases SuffixLength()
    {
      match step(st, Peek())
      case Accept() =>
        Success(this)
      case Reject(err) =>
        Failure(OtherError(err))
      case partial =>
        if EOF? then
          Failure(EOF)
        else
          Skip(1).SkipWhileLexer(step, partial)
    }
  }
}

module {:options ""/functionSyntax:4""} Lexers {

  module Core {

    import opened Wrappers

    import opened BoundedInts
    datatype LexerState<+T, +R> = Accept | Reject(err: R) | Partial(st: T)

    type Lexer<!T, !R> = (LexerState<T, R>, opt_byte) -> LexerState<T, R>
  }

  module Strings {

    import opened Core

    import opened BoundedInts
    type StringBodyLexerState = bool

    datatype StringLexerState = Start | Body(escaped: bool) | End

    const StringBodyLexerStart: StringBodyLexerState := false

    function method StringBody<R>(st: LexerState<StringBodyLexerState, R>, byte: opt_byte): LexerState<StringBodyLexerState, R>
      decreases st, byte
    {
      match st
      case Partial(escaped) =>
        if byte == '\\' as opt_byte then
          Partial(!escaped)
        else if byte == '\""' as opt_byte && !escaped then
          Accept
        else
          Partial(false)
      case _ =>
        st
    }

    const StringLexerStart: StringLexerState := Start

    function method String(st: LexerState<StringLexerState, string>, byte: opt_byte): LexerState<StringLexerState, string>
      decreases st, byte
    {
      match st
      case Partial(Start()) =>
        if byte == '\""' as opt_byte then
          Partial(Body(false))
        else
          Reject(""String must start with double quote"")
      case Partial(End()) =>
        Accept
      case Partial(Body(escaped)) =>
        if byte == '\\' as opt_byte then
          Partial(Body(!escaped))
        else if byte == '\""' as opt_byte && !escaped then
          Partial(End)
        else
          Partial(Body(false))
      case _ =>
        st
    }
  }
}

module JSON {

  module {:options ""/functionSyntax:4""} Grammar {

    import opened BoundedInts

    import opened Core = Views.Core
    type jchar = v: View
      | v.Length() == 1
      witness View.OfBytes(['b' as byte])

    type jperiod = v: View
      | v.Char?('.')
      witness View.OfBytes(['.' as byte])

    type je = v: View
      | v.Char?('e') || v.Char?('E')
      witness View.OfBytes(['e' as byte])

    type jcolon = v: View
      | v.Char?(':')
      witness View.OfBytes([':' as byte])

    type jcomma = v: View
      | v.Char?(',')
      witness View.OfBytes([',' as byte])

    type jlbrace = v: View
      | v.Char?('{')
      witness View.OfBytes(['{' as byte])

    type jrbrace = v: View
      | v.Char?('}')
      witness View.OfBytes(['}' as byte])

    type jlbracket = v: View
      | v.Char?('[')
      witness View.OfBytes(['[' as byte])

    type jrbracket = v: View
      | v.Char?(']')
      witness View.OfBytes([']' as byte])

    type jminus = v: View
      | v.Char?('-') || v.Empty?
      witness View.OfBytes([])

    type jsign = v: View
      | v.Char?('-') || v.Char?('+') || v.Empty?
      witness View.OfBytes([])

    type jblanks = v: View
      | Blanks?(v)
      witness View.OfBytes([])

    datatype Structural<+T> = Structural(before: jblanks, t: T, after: jblanks)

    datatype Maybe<+T> = Empty | NonEmpty(t: T)

    datatype Suffixed<+T, +S> = Suffixed(t: T, suffix: Maybe<Structural<S>>)

    type SuffixedSequence<+D, +S> = s: seq<Suffixed<D, S>>
      | NoTrailingSuffix(s)

    datatype Bracketed<+L, +D, +S, +R> = Bracketed(l: Structural<L>, data: SuffixedSequence<D, S>, r: Structural<R>)

    type jstring = v: View
      | true
      witness View.OfBytes([])

    type jnull = v: View
      | Null?(v)
      witness View.OfBytes(NULL)

    type jbool = v: View
      | Bool?(v)
      witness View.OfBytes(TRUE)

    type jdigits = v: View
      | Digits?(v)
      witness View.OfBytes([])

    type jnum = v: View
      | Num?(v)
      witness View.OfBytes(['0' as byte])

    type jint = v: View
      | Int?(v)
      witness View.OfBytes(['0' as byte])

    datatype jkv = KV(k: jstring, colon: Structural<jcolon>, v: Value)

    type jobject = Bracketed<jlbrace, jkv, jcomma, jrbrace>

    type jarray = Bracketed<jlbracket, Value, jcomma, jrbracket>

    type jmembers = SuffixedSequence<jkv, jcomma>

    type jmember = Suffixed<jkv, jcomma>

    type jitems = SuffixedSequence<Value, jcomma>

    type jitem = Suffixed<Value, jcomma>

    datatype jfrac = JFrac(period: jperiod, num: jnum)

    datatype jexp = JExp(e: je, sign: jsign, num: jnum)

    datatype jnumber = JNumber(minus: jminus, num: jnum, frac: Maybe<jfrac>, exp: Maybe<jexp>)

    datatype Value = Null(n: jnull) | Bool(b: jbool) | String(str: jstring) | Number(num: jnumber) | Object(obj: jobject) | Array(arr: jarray)

    type JSON = Structural<Value>

    predicate method Blank?(b: byte)
      decreases b
    {
      b == 32 || b == 9 || b == 10 || b == 13
    }

    predicate Blanks?(v: View)
      decreases v
    {
      forall b: uint8 | b in v.Bytes() :: 
        Blank?(b)
    }

    predicate NoTrailingSuffix<S, D>(s: seq<Suffixed<D, S>>)
      decreases s
    {
      forall idx: int | 0 <= idx < |s| :: 
        s[idx].suffix.Empty? <==> idx == |s| - 1
    }

    const NULL: bytes := ['n' as byte, 'u' as byte, 'l' as byte, 'l' as byte]
    const TRUE: bytes := ['t' as byte, 'r' as byte, 'u' as byte, 'e' as byte]
    const FALSE: bytes := ['f' as byte, 'a' as byte, 'l' as byte, 's' as byte, 'e' as byte]

    predicate Null?(v: View)
      decreases v
    {
      v.Bytes() == NULL
    }

    predicate Bool?(v: View)
      decreases v
    {
      v.Bytes() in {TRUE, FALSE}
    }

    predicate method Digit?(b: byte)
      decreases b
    {
      '0' as byte <= b <= '9' as byte
    }

    predicate Digits?(v: View)
      decreases v
    {
      forall b: uint8 | b in v.Bytes() :: 
        Digit?(b)
    }

    predicate Num?(v: View)
      decreases v
    {
      Digits?(v) &&
      !v.Empty?
    }

    predicate Int?(v: View)
      decreases v
    {
      v.Char?('0') || (Num?(v) && v.At(0) != '0' as byte)
    }
  }

  module {:options ""/functionSyntax:4""} Spec {

    import opened BoundedInts

    import Vs = Views.Core

    import opened Grammar
    function method View(v: Vs.View): bytes
      decreases v
    {
      v.Bytes()
    }

    function method Structural<T>(self: Structural<T>, pt: T -> bytes): bytes
      decreases self
    {
      View(self.before) + pt(self.t) + View(self.after)
    }

    function method StructuralView(self: Structural<Vs.View>): bytes
      decreases self
    {
      Structural<Vs.View>(self, View)
    }

    function method Maybe<T>(self: Maybe<T>, pt: T -> bytes): (bs: bytes)
      ensures self.Empty? ==> bs == []
      ensures self.NonEmpty? ==> bs == pt(self.t)
      decreases self
    {
      if self.Empty? then
        []
      else
        pt(self.t)
    }

    function method ConcatBytes<T>(ts: seq<T>, pt: T --> bytes): bytes
      requires forall d: T | d in ts :: pt.requires(d)
      decreases ts
    {
      if |ts| == 0 then
        []
      else
        pt(ts[0]) + ConcatBytes(ts[1..], pt)
    }

    function method Bracketed<D, S>(self: Bracketed<Vs.View, D, S, Vs.View>, pdatum: Suffixed<D, S> --> bytes): bytes
      requires forall d: Suffixed<D, S> | d < self :: pdatum.requires(d)
      decreases self
    {
      StructuralView(self.l) + ConcatBytes(self.data, pdatum) + StructuralView(self.r)
    }

    function method KV(self: jkv): bytes
      decreases self
    {
      View(self.k) + StructuralView(self.colon) + Value(self.v)
    }

    function method Frac(self: jfrac): bytes
      decreases self
    {
      View(self.period) + View(self.num)
    }

    function method Exp(self: jexp): bytes
      decreases self
    {
      View(self.e) + View(self.sign) + View(self.num)
    }

    function method Number(self: jnumber): bytes
      decreases self
    {
      View(self.minus) + View(self.num) + Maybe(self.frac, Frac) + Maybe(self.exp, Exp)
    }

    function method String(self: jstring): bytes
      decreases self
    {
      View(self)
    }

    function method CommaSuffix(c: Maybe<Structural<jcomma>>): bytes
      decreases c
    {
      Maybe<Structural<Vs.View>>(c, StructuralView)
    }

    function method Member(self: jmember): bytes
      decreases self
    {
      KV(self.t) + CommaSuffix(self.suffix)
    }

    function method Item(self: jitem): bytes
      decreases self
    {
      Value(self.t) + CommaSuffix(self.suffix)
    }

    function method Object(obj: jobject): bytes
      decreases obj
    {
      Bracketed(obj, (d: jmember) requires d < obj => Member(d))
    }

    function method Array(arr: jarray): bytes
      decreases arr
    {
      Bracketed(arr, (d: jitem) requires d < arr => Item(d))
    }

    function method Value(self: Value): bytes
      decreases self
    {
      match self {
        case Null(n) =>
          View(n)
        case Bool(b) =>
          View(b)
        case String(str) =>
          String(str)
        case Number(num) =>
          Number(num)
        case Object(obj) =>
          Object(obj)
        case Array(arr) =>
          Array(arr)
      }
    }

    function method JSON(js: JSON): bytes
      decreases js
    {
      Structural(js, Value)
    }
  }

  module {:options ""/functionSyntax:4""} SpecProperties {

    import opened BoundedInts

    import Vs = Views.Core

    import opened Grammar

    import Spec
    lemma Bracketed_Morphism<D, S>(bracketed: Bracketed<Vs.View, D, S, Vs.View>)
      ensures forall pd0: Suffixed<D, S> --> bytes, pd1: Suffixed<D, S> --> bytes | (forall d: Suffixed<D, S> | d < bracketed :: pd0.requires(d)) && (forall d: Suffixed<D, S> | d < bracketed :: pd1.requires(d)) && forall d: Suffixed<D, S> | d < bracketed :: pd0(d) == pd1(d) :: Spec.Bracketed(bracketed, pd0) == Spec.Bracketed(bracketed, pd1)
      decreases bracketed
    {
    }

    lemma {:induction ts} /*{:_induction ts}*/ ConcatBytes_Morphism<T>(ts: seq<T>, pt0: T --> bytes, pt1: T --> bytes)
      requires forall d: T | d in ts :: pt0.requires(d)
      requires forall d: T | d in ts :: pt1.requires(d)
      requires forall d: T | d in ts :: pt0(d) == pt1(d)
      ensures Spec.ConcatBytes(ts, pt0) == Spec.ConcatBytes(ts, pt1)
      decreases ts
    {
    }

    lemma {:induction ts0} /*{:_induction ts0}*/ ConcatBytes_Linear<T>(ts0: seq<T>, ts1: seq<T>, pt: T --> bytes)
      requires forall d: T | d in ts0 :: pt.requires(d)
      requires forall d: T | d in ts1 :: pt.requires(d)
      ensures Spec.ConcatBytes(ts0 + ts1, pt) == Spec.ConcatBytes(ts0, pt) + Spec.ConcatBytes(ts1, pt)
      decreases ts0, ts1
    {
    }
  }

  module ZeroCopy {

    module {:options ""/functionSyntax:4""} API {

      import opened BoundedInts

      import opened Wrappers

      import Vs = Views.Core

      import opened Grammar

      import Spec

      import Serializer

      import Deserializer
      function method {:opaque} {:fuel 0, 0} Serialize(js: JSON): (bs: seq<byte>)
        ensures bs == Spec.JSON(js)
        decreases js
      {
        Serializer.Text(js).Bytes()
      }

      method SerializeAlloc(js: JSON) returns (bs: Result<array<byte>, Serializer.Error>)
        ensures bs.Success? ==> fresh(bs.value)
        ensures bs.Success? ==> bs.value[..] == Spec.JSON(js)
        decreases js
      {
        bs := Serializer.Serialize(js);
      }

      method SerializeBlit(js: JSON, bs: array<byte>) returns (len: Result<uint32, Serializer.Error>)
        modifies bs
        ensures len.Success? ==> len.value as int <= bs.Length
        ensures len.Success? ==> bs[..len.value] == Spec.JSON(js)
        ensures len.Success? ==> bs[len.value..] == old(bs[len.value..])
        ensures len.Failure? ==> unchanged(bs)
        decreases js, bs
      {
        len := Serializer.SerializeTo(js, bs);
      }

      function method {:opaque} {:fuel 0, 0} Deserialize(bs: seq<byte>): (js: Result<JSON, Deserializer.Error>)
        ensures js.Success? ==> bs == Spec.JSON(js.value)
        decreases bs
      {
        Deserializer.API.OfBytes(bs)
      }
    }

    module {:options ""/functionSyntax:4""} Serializer {

      import opened BoundedInts

      import opened Wrappers

      import Spec

      import SpecProperties

      import opened Grammar

      import opened Writers = Views.Writers

      import opened Vs = Views.Core
      datatype Error = OutOfMemory

      method Serialize(js: JSON) returns (rbs: Result<array<byte>, Error>)
        ensures rbs.Success? ==> fresh(rbs.value)
        ensures rbs.Success? ==> rbs.value[..] == Spec.JSON(js)
        decreases js
      {
        var writer := Text(js);
        :- Need(writer.Unsaturated?, OutOfMemory);
        var bs := writer.ToArray();
        return Success(bs);
      }

      method SerializeTo(js: JSON, bs: array<byte>) returns (len: Result<uint32, Error>)
        modifies bs
        ensures len.Success? ==> len.value as int <= bs.Length
        ensures len.Success? ==> bs[..len.value] == Spec.JSON(js)
        ensures len.Success? ==> bs[len.value..] == old(bs[len.value..])
        ensures len.Failure? ==> unchanged(bs)
        decreases js, bs
      {
        var writer := Text(js);
        :- Need(writer.Unsaturated?, OutOfMemory);
        :- Need(writer.length as int <= bs.Length, OutOfMemory);
        writer.Blit(bs);
        return Success(writer.length);
      }

      function method {:opaque} {:fuel 0, 0} Text(js: JSON): (wr: Writer)
        ensures wr.Bytes() == Spec.JSON(js)
        decreases js
      {
        JSON(js)
      }

      function method {:opaque} {:fuel 0, 0} JSON(js: JSON, writer: Writer := Writer.Empty): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.JSON(js)
        decreases js, writer
      {
        writer.Append(js.before).Then((wr: Writer) => Value(js.t, wr)).Append(js.after)
      }

      function method {:opaque} {:fuel 0, 0} Value(v: Value, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Value(v)
        decreases v, 4
      {
        match v
        case Null(n) =>
          writer.Append(n)
        case Bool(b) =>
          writer.Append(b)
        case String(str) =>
          String(str, writer)
        case Number(num) =>
          Number(num, writer)
        case Object(obj) =>
          Object(obj, writer)
        case Array(arr) =>
          Array(arr, writer)
      }

      function method {:opaque} {:fuel 0, 0} String(str: jstring, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.String(str)
        decreases str, 0
      {
        writer.Append(str)
      }

      function method {:opaque} {:fuel 0, 0} Number(num: jnumber, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Number(num)
        decreases num, 0
      {
        var writer: Writer := writer.Append(num.minus).Append(num.num);
        var writer: Writer_ := if num.frac.NonEmpty? then writer.Append(num.frac.t.period).Append(num.frac.t.num) else writer;
        var writer: Writer_ := if num.exp.NonEmpty? then writer.Append(num.exp.t.e).Append(num.exp.t.sign).Append(num.exp.t.num) else writer;
        writer
      }

      function method StructuralView(st: Structural<View>, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Structural(st, Spec.View)
        decreases st, writer
      {
        writer.Append(st.before).Append(st.t).Append(st.after)
      }

      lemma {:axiom} Assume(b: bool)
        ensures b
        decreases b

      function method {:opaque} {:fuel 0, 0} Object(obj: jobject, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Object(obj)
        decreases obj, 3
      {
        var writer: Writer := StructuralView(obj.l, writer);
        var writer: Writer := Members(obj, writer);
        var writer: Writer := StructuralView(obj.r, writer);
        SpecProperties.Bracketed_Morphism(obj);
        assert Spec.Object(obj) == Spec.Bracketed(obj, Spec.Member);
        writer
      }

      function method {:opaque} {:fuel 0, 0} Array(arr: jarray, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.Array(arr)
        decreases arr, 3
      {
        var writer: Writer := StructuralView(arr.l, writer);
        var writer: Writer := Items(arr, writer);
        var writer: Writer := StructuralView(arr.r, writer);
        SpecProperties.Bracketed_Morphism(arr);
        assert Spec.Array(arr) == Spec.Bracketed(arr, Spec.Item);
        writer
      }

      function {:opaque} {:fuel 0, 0} Members(obj: jobject, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(obj.data, Spec.Member)
        decreases obj, 2
      {
        MembersSpec(obj, obj.data, writer)
      } by method {
        wr := MembersImpl(obj, writer);
        Assume(false);
      }

      function {:opaque} {:fuel 0, 0} Items(arr: jarray, writer: Writer): (wr: Writer)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(arr.data, Spec.Item)
        decreases arr, 2
      {
        ItemsSpec(arr, arr.data, writer)
      } by method {
        wr := ItemsImpl(arr, writer);
        Assume(false);
      }

      function MembersSpec(obj: jobject, members: seq<jmember>, writer: Writer): (wr: Writer)
        requires forall j: int | 0 <= j < |members| :: members[j] < obj
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(members, Spec.Member)
        decreases obj, 1, members
      {
        if members == [] then
          writer
        else
          ghost var writer: Writer := MembersSpec(obj, members[..|members| - 1], writer); assert members == members[..|members| - 1] + [members[|members| - 1]]; SpecProperties.ConcatBytes_Linear(members[..|members| - 1], [members[|members| - 1]], Spec.Member); Member(obj, members[|members| - 1], writer)
      }

      function SequenceSpec<T>(v: Value, items: seq<T>, spec: T -> bytes, impl: (Value, T, Writer) --> Writer, writer: Writer): (wr: Writer)
        requires forall item: T, wr: Writer | item in items :: impl.requires(v, item, wr)
        requires forall item: T, wr: Writer | item in items :: impl(v, item, wr).Bytes() == wr.Bytes() + spec(item)
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, spec)
        decreases v, 1, items
      {
        if items == [] then
          writer
        else
          ghost var writer: Writer := SequenceSpec(v, items[..|items| - 1], spec, impl, writer); assert items == items[..|items| - 1] + [items[|items| - 1]]; SpecProperties.ConcatBytes_Linear(items[..|items| - 1], [items[|items| - 1]], spec); impl(v, items[|items| - 1], writer)
      }

      function ItemsSpec(arr: jarray, items: seq<jitem>, writer: Writer): (wr: Writer)
        requires forall j: int | 0 <= j < |items| :: items[j] < arr
        ensures wr.Bytes() == writer.Bytes() + Spec.ConcatBytes(items, Spec.Item)
        decreases arr, 1, items
      {
        if items == [] then
          writer
        else
          ghost var writer: Writer := ItemsSpec(arr, items[..|items| - 1], writer); assert items == items[..|items| - 1] + [items[|items| - 1]]; SpecProperties.ConcatBytes_Linear(items[..|items| - 1], [items[|items| - 1]], Spec.Item); Item(arr, items[|items| - 1], writer)
      }

      method MembersImpl(obj: jobject, writer: Writer) returns (wr: Writer)
        ensures wr == MembersSpec(obj, obj.data, writer)
        decreases obj, 1
      {
        wr := writer;
        var members := obj.data;
        assert wr == MembersSpec(obj, members[..0], writer);
        for i: int := 0 to |members|
          invariant wr == MembersSpec(obj, members[..i], writer)
        {
          assert members[..i + 1][..i] == members[..i];
          wr := Member(obj, members[i], wr);
        }
        assert members[..|members|] == members;
      }

      method ItemsImpl(arr: jarray, writer: Writer) returns (wr: Writer)
        ensures wr == ItemsSpec(arr, arr.data, writer)
        decreases arr, 1
      {
        wr := writer;
        var items := arr.data;
        assert wr == ItemsSpec(arr, items[..0], writer);
        for i: int := 0 to |items|
          invariant wr == ItemsSpec(arr, items[..i], writer)
        {
          assert items[..i + 1][..i] == items[..i];
          wr := Item(arr, items[i], wr);
        }
        assert items[..|items|] == items;
      }

      function method {:opaque} {:fuel 0, 0} Member(ghost obj: jobject, m: jmember, writer: Writer): (wr: Writer)
        requires m < obj
        ensures wr.Bytes() == writer.Bytes() + Spec.Member(m)
        decreases obj, 0
      {
        var writer: Writer := writer.Append(m.t.k);
        var writer: Writer := StructuralView(m.t.colon, writer);
        var writer: Writer := Value(m.t.v, writer);
        if m.suffix.Empty? then
          writer
        else
          StructuralView(m.suffix.t, writer)
      }

      function method {:opaque} {:fuel 0, 0} Item(ghost arr: jarray, m: jitem, writer: Writer): (wr: Writer)
        requires m < arr
        ensures wr.Bytes() == writer.Bytes() + Spec.Item(m)
        decreases arr, 0
      {
        var writer: Writer := Value(m.t, writer);
        if m.suffix.Empty? then
          writer
        else
          StructuralView(m.suffix.t, writer)
      }
    }

    module {:options ""/functionSyntax:4""} Deserializer {

      module Core {

        import opened BoundedInts

        import opened Wrappers

        import Spec

        import Vs = Views.Core

        import opened Cursors

        import opened Parsers

        import opened Grammar
        datatype JSONError = UnterminatedSequence | EmptyNumber | ExpectingEOF | IntOverflow {
          function method ToString(): string
            decreases this
          {
            match this
            case UnterminatedSequence() =>
              ""Unterminated sequence""
            case EmptyNumber() =>
              ""Number must contain at least one digit""
            case ExpectingEOF() =>
              ""Expecting EOF""
            case IntOverflow() =>
              ""Input length does not fit in a 32-bit counter""
          }
        }

        type Error = CursorError<JSONError>

        type ParseResult<+T> = SplitResult<T, JSONError>

        type Parser<!T> = Parsers.Parser<T, JSONError>

        type SubParser<!T> = Parsers.SubParser<T, JSONError>

        type jopt = v: Vs.View
          | v.Length() <= 1
          witness Vs.View.OfBytes([])

        type ValueParser = sp: SubParser<Value>
          | forall t: Value :: sp.spec(t) == Spec.Value(t)
          witness *

        const SpecView := (v: Vs.View) => Spec.View(v)

        function method {:opaque} {:fuel 0, 0} Get(cs: FreshCursor, err: JSONError): (pr: ParseResult<jchar>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs, err
        {
          var cs: Cursor :- cs.Get(err); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} WS(cs: FreshCursor): (sp: Split<jblanks>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipWhile(Blank?).Split()
        }

        function method {:opaque} {:fuel 0, 0} Structural<T>(cs: FreshCursor, parser: Parser<T>): (pr: ParseResult<Structural<T>>)
          requires forall cs: FreshCursor :: parser.fn.requires(cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (st: Structural<T>) => Spec.Structural(st, parser.spec))
          decreases cs, parser
        {
          var SP(before: jblanks, cs: FreshCursor) := WS(cs);
          var SP(val: T, cs: FreshCursor) :- parser.fn(cs); var SP(after: jblanks, cs: FreshCursor) := WS(cs); Success(SP(Grammar.Structural(before, val, after), cs))
        }

        function method {:opaque} {:fuel 0, 0} TryStructural(cs: FreshCursor): (sp: Split<Structural<jopt>>)
          ensures sp.SplitFrom?(cs, (st: Structural<jopt>) => Spec.Structural(st, SpecView))
          decreases cs
        {
          var SP(before: jblanks, cs: FreshCursor) := WS(cs);
          var SP(val: View, cs: FreshCursor) := cs.SkipByte().Split();
          var SP(after: jblanks, cs: FreshCursor) := WS(cs);
          SP(Grammar.Structural(before, val, after), cs)
        }
      }
      type Error = Core.Error

      abstract module SequenceParams {

        import opened BoundedInts

        import opened Grammar

        import opened Cursors

        import opened Core
        type TElement

        const OPEN: byte
        const CLOSE: byte

        function ElementSpec(t: TElement): bytes

        function method Element(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TElement>)
          requires cs.StrictlySplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, ElementSpec)
          decreases cs.Length()
      }

      abstract module Sequences {

        import opened Wrappers

        import opened BoundedInts

        import opened Params : SequenceParams

        import SpecProperties

        import opened Vs = Views.Core

        import opened Grammar

        import opened Cursors

        import Parsers

        import opened Core
        type jopen = v: Vs.View
          | v.Byte?(OPEN)
          witness Vs.View.OfBytes([OPEN])

        type jclose = v: Vs.View
          | v.Byte?(CLOSE)
          witness Vs.View.OfBytes([CLOSE])

        type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>

        type TSuffixedElement = Suffixed<TElement, jcomma>

        const SEPARATOR: byte := ',' as byte

        function SuffixedElementSpec(e: TSuffixedElement): bytes
          decreases e
        {
          ElementSpec(e.t) + Spec.CommaSuffix(e.suffix)
        }

        function BracketedSpec(ts: TBracketed): bytes
          decreases ts
        {
          Spec.Bracketed(ts, SuffixedElementSpec)
        }

        function SuffixedElementsSpec(ts: seq<TSuffixedElement>): bytes
          decreases ts
        {
          Spec.ConcatBytes(ts, SuffixedElementSpec)
        }

        function method {:opaque} {:fuel 0, 0} Open(cs: FreshCursor): (pr: ParseResult<jopen>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_: View_) => [OPEN])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(OPEN); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} Close(cs: FreshCursor): (pr: ParseResult<jclose>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_: View_) => [CLOSE])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(CLOSE); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} BracketedFromParts(ghost cs: Cursor, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>, close: Split<Structural<jclose>>): (sp: Split<TBracketed>)
          requires Grammar.NoTrailingSuffix(elems.t)
          requires open.StrictlySplitFrom?(cs, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires close.StrictlySplitFrom?(elems.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          ensures sp.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, open, elems, close
        {
          var sp: Split<Bracketed<jopen, TElement, jcomma, jclose>> := SP(Grammar.Bracketed(open.t, elems.t, close.t), close.cs);
          calc {
            cs.Bytes();
            Spec.Structural(open.t, SpecView) + open.cs.Bytes();
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
          }
          sp
        }

        function method {:opaque} {:fuel 0, 0} AppendWithSuffix(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jcomma>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jcomma>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures forall e: Suffixed<TElement, jcomma> | e in elems'.t :: e.suffix.NonEmpty?
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, NonEmpty(sep.t));
          var elems': Split<seq<Suffixed<TElement, jcomma>>> := SP(elems.t + [suffixed], sep.cs);
          SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
          elems'
        }

        function method {:opaque} {:fuel 0, 0} AppendLast(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jclose>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures NoTrailingSuffix(elems'.t)
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          ensures sep.StrictlySplitFrom?(elems'.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, Empty());
          var elems': Split<seq<Suffixed<TElement, jcomma>>> := SP(elems.t + [suffixed], elem.cs);
          SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
          elems'
        }

        function method {:opaque} {:tailrecursion} {:fuel 0, 0} Elements(ghost cs0: FreshCursor, json: ValueParser, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>): (pr: ParseResult<TBracketed>)
          requires open.StrictlySplitFrom?(cs0, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs0, BracketedSpec)
          decreases elems.cs.Length()
        {
          var elem: Split<TElement> :- Element(elems.cs, json); var sep: Split<Structural<jopt>> := Core.TryStructural(elem.cs); var s0: opt_byte := sep.t.t.Peek(); if s0 == SEPARATOR as opt_byte then var elems: Split<seq<TSuffixedElement>> := AppendWithSuffix(open.cs, json, elems, elem, sep); Elements(cs0, json, open, elems) else if s0 == CLOSE as opt_byte then var elems: Split<seq<TSuffixedElement>> := AppendLast(open.cs, json, elems, elem, sep); Success(BracketedFromParts(cs0, open, elems, sep)) else Failure(ExpectingAnyByte([CLOSE, SEPARATOR], s0))
        }

        function method {:opaque} {:fuel 0, 0} Bracketed(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TBracketed>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, json
        {
          var open: Split<Structural<jopen>> :- Core.Structural(cs, Parsers.Parser(Open, SpecView)); assert open.cs.StrictlySplitFrom?(json.cs); var elems: Split<seq<Suffixed<TElement, jcomma>>> := SP([], open.cs); if open.cs.Peek() == CLOSE as opt_byte then var close: Split<Structural<jclose>> :- Core.Structural(open.cs, Parsers.Parser(Close, SpecView)); Success(BracketedFromParts(cs, open, elems, close)) else Elements(cs, json, open, elems)
        }

        lemma Valid(x: TBracketed)
          ensures x.l.t.Byte?(OPEN)
          ensures x.r.t.Byte?(CLOSE)
          ensures NoTrailingSuffix(x.data)
          ensures forall pf: Suffixed<TElement, jcomma> | pf in x.data :: pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          decreases x
        {
        }
      }

      module API {

        import opened BoundedInts

        import opened Wrappers

        import opened Vs = Views.Core

        import opened Grammar

        import opened Cursors

        import opened Core

        import Values
        function method {:opaque} {:fuel 0, 0} JSON(cs: FreshCursor): (pr: ParseResult<JSON>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.JSON)
          decreases cs
        {
          Core.Structural(cs, Parsers.Parser(Values.Value, Spec.Value))
        }

        function method {:opaque} {:fuel 0, 0} Text(v: View): (jsr: Result<JSON, Error>)
          ensures jsr.Success? ==> v.Bytes() == Spec.JSON(jsr.value)
          decreases v
        {
          var SP(text: JSON, cs: FreshCursor) :- JSON(Cursor.OfView(v)); Need(cs.EOF?, OtherError(ExpectingEOF)); Success(text)
        }

        function method {:opaque} {:fuel 0, 0} OfBytes(bs: bytes): (jsr: Result<JSON, Error>)
          ensures jsr.Success? ==> bs == Spec.JSON(jsr.value)
          decreases bs
        {
          Need(|bs| < TWO_TO_THE_32, OtherError(IntOverflow)); Text(Vs.View.OfBytes(bs))
        }
      }

      module Values {

        import opened BoundedInts

        import opened Wrappers

        import opened Grammar

        import opened Cursors

        import opened Core

        import Strings

        import Numbers

        import Objects

        import Arrays

        import Constants

        import SpecProperties
        function method {:opaque} {:fuel 0, 0} Value(cs: FreshCursor): (pr: ParseResult<Value>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Value)
          decreases cs.Length(), 1
        {
          var c: opt_byte := cs.Peek();
          if c == '{' as opt_byte then
            var SP(obj: jobject, cs: FreshCursor) :- Objects.Object(cs, ValueParser(cs)); Success(SP(Grammar.Object(obj), cs))
          else if c == '[' as opt_byte then
            var SP(arr: jarray, cs: FreshCursor) :- Arrays.Array(cs, ValueParser(cs)); Success(SP(Grammar.Array(arr), cs))
          else if c == '\""' as opt_byte then
            var SP(str: jstring, cs: FreshCursor) :- Strings.String(cs); Success(SP(Grammar.String(str), cs))
          else if c == 't' as opt_byte then
            var SP(cst: jstring, cs: FreshCursor) :- Constants.Constant(cs, TRUE); Success(SP(Grammar.Bool(cst), cs))
          else if c == 'f' as opt_byte then
            var SP(cst: jstring, cs: FreshCursor) :- Constants.Constant(cs, FALSE); Success(SP(Grammar.Bool(cst), cs))
          else if c == 'n' as opt_byte then
            var SP(cst: jstring, cs: FreshCursor) :- Constants.Constant(cs, NULL); Success(SP(Grammar.Null(cst), cs))
          else
            var SP(num: jnumber, cs: FreshCursor) :- Numbers.Number(cs); Success(SP(Grammar.Number(num), cs))
        }

        function method {:opaque} {:fuel 0, 0} ValueParser(cs: FreshCursor): (p: ValueParser)
          ensures cs.SplitFrom?(p.cs)
          decreases cs.Length(), 0
        {
          var pre: FreshCursor -> bool := (ps': FreshCursor) => ps'.Length() < cs.Length();
          var fn: FreshCursor --> ParseResult<Value> := (ps': FreshCursor) requires pre(ps') => Value(ps');
          Parsers.SubParser(cs, pre, fn, Spec.Value)
        }
      }

      module Constants {

        import opened BoundedInts

        import opened Wrappers

        import opened Grammar

        import opened Core

        import opened Cursors
        function method {:opaque} {:fuel 0, 0} Constant(cs: FreshCursor, expected: bytes): (pr: ParseResult<jstring>)
          requires |expected| < TWO_TO_THE_32
          ensures pr.Success? ==> pr.value.t.Bytes() == expected
          ensures pr.Success? ==> pr.value.SplitFrom?(cs, (_: View_) => expected)
          decreases cs, expected
        {
          var cs: Cursor :- cs.AssertBytes(expected); Success(cs.Split())
        }
      }

      module Strings {

        import opened Wrappers

        import opened Grammar

        import opened Cursors

        import opened LC = Lexers.Core

        import opened Strings = Lexers.Strings

        import opened Parsers

        import opened Core
        function method {:opaque} {:fuel 0, 0} String(cs: FreshCursor): (pr: ParseResult<jstring>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.String)
          decreases cs
        {
          var cs: Cursor :- cs.AssertChar('\""'); var cs: Cursor :- cs.SkipWhileLexer(StringBody, Partial(StringBodyLexerStart)); var cs: Cursor :- cs.AssertChar('\""'); Success(cs.Split())
        }
      }

      module Numbers {

        import opened BoundedInts

        import opened Wrappers

        import opened Grammar

        import opened Cursors

        import opened Core
        function method {:opaque} {:fuel 0, 0} Digits(cs: FreshCursor): (sp: Split<jdigits>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipWhile(Digit?).Split()
        }

        function method {:opaque} {:fuel 0, 0} NonEmptyDigits(cs: FreshCursor): (pr: ParseResult<jnum>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          var sp: Split<jdigits> := Digits(cs);
          Need(!sp.t.Empty?, OtherError(EmptyNumber)); Success(sp)
        }

        function method {:opaque} {:fuel 0, 0} NonZeroInt(cs: FreshCursor): (pr: ParseResult<jint>)
          requires cs.Peek() != '0' as opt_byte
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          NonEmptyDigits(cs)
        }

        function method {:opaque} {:fuel 0, 0} OptionalMinus(cs: FreshCursor): (sp: Split<jminus>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipIf((c: uint8) => c == '-' as byte).Split()
        }

        function method {:opaque} {:fuel 0, 0} OptionalSign(cs: FreshCursor): (sp: Split<jsign>)
          ensures sp.SplitFrom?(cs, SpecView)
          decreases cs
        {
          cs.SkipIf((c: uint8) => c == '-' as byte || c == '+' as byte).Split()
        }

        function method {:opaque} {:fuel 0, 0} TrimmedInt(cs: FreshCursor): (pr: ParseResult<jint>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          var sp: Split<View> := cs.SkipIf((c: uint8) => c == '0' as byte).Split();
          if sp.t.Empty? then
            NonZeroInt(sp.cs)
          else
            Success(sp)
        }

        function method {:opaque} {:fuel 0, 0} Exp(cs: FreshCursor): (pr: ParseResult<Maybe<jexp>>)
          ensures pr.Success? ==> pr.value.SplitFrom?(cs, (exp: Maybe<jexp>) => Spec.Maybe(exp, Spec.Exp))
          decreases cs
        {
          var SP(e: View, cs: FreshCursor) := cs.SkipIf((c: uint8) => c == 'e' as byte || c == 'E' as byte).Split();
          if e.Empty? then
            Success(SP(Empty(), cs))
          else
            assert e.Char?('e') || e.Char?('E'); var SP(sign: jsign, cs: FreshCursor) := OptionalSign(cs); var SP(num: jnum, cs: FreshCursor) :- NonEmptyDigits(cs); Success(SP(NonEmpty(JExp(e, sign, num)), cs))
        }

        function method {:opaque} {:fuel 0, 0} Frac(cs: FreshCursor): (pr: ParseResult<Maybe<jfrac>>)
          ensures pr.Success? ==> pr.value.SplitFrom?(cs, (frac: Maybe<jfrac>) => Spec.Maybe(frac, Spec.Frac))
          decreases cs
        {
          var SP(period: View, cs: FreshCursor) := cs.SkipIf((c: uint8) => c == '.' as byte).Split();
          if period.Empty? then
            Success(SP(Empty(), cs))
          else
            var SP(num: jnum, cs: FreshCursor) :- NonEmptyDigits(cs); Success(SP(NonEmpty(JFrac(period, num)), cs))
        }

        function method {:opaque} {:fuel 0, 0} NumberFromParts(ghost cs: Cursor, minus: Split<jminus>, num: Split<jint>, frac: Split<Maybe<jfrac>>, exp: Split<Maybe<jexp>>): (sp: Split<jnumber>)
          requires minus.SplitFrom?(cs, SpecView)
          requires num.StrictlySplitFrom?(minus.cs, SpecView)
          requires frac.SplitFrom?(num.cs, (frac: Maybe<jfrac>) => Spec.Maybe(frac, Spec.Frac))
          requires exp.SplitFrom?(frac.cs, (exp: Maybe<jexp>) => Spec.Maybe(exp, Spec.Exp))
          ensures sp.StrictlySplitFrom?(cs, Spec.Number)
          decreases cs, minus, num, frac, exp
        {
          var sp: Split<jnumber> := SP(Grammar.JNumber(minus.t, num.t, frac.t, exp.t), exp.cs);
          calc {
            cs.Bytes();
            Spec.View(minus.t) + minus.cs.Bytes();
            Spec.View(minus.t) + Spec.View(num.t) + num.cs.Bytes();
            Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac) + frac.cs.Bytes();
            Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac) + Spec.Maybe(exp.t, Spec.Exp) + exp.cs.Bytes();
            Spec.Number(sp.t) + exp.cs.Bytes();
          }
          sp
        }

        function method {:opaque} {:fuel 0, 0} Number(cs: FreshCursor): (pr: ParseResult<jnumber>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Number)
          decreases cs
        {
          var minus: Split<jminus> := OptionalMinus(cs);
          var num: Split<jint> :- TrimmedInt(minus.cs); var frac: Split<Maybe<jfrac>> :- Frac(num.cs); var exp: Split<Maybe<jexp>> :- Exp(frac.cs); Success(NumberFromParts(cs, minus, num, frac, exp))
        }
      }

      module ArrayParams refines SequenceParams {

        import opened Strings

        import opened Wrappers
        type TElement = Value

        const OPEN: byte := '[' as byte
        const CLOSE: byte := ']' as byte

        function method ElementSpec(t: TElement): bytes
          decreases t
        {
          Spec.Value(t)
        }

        function method {:opaque} {:fuel 0, 0} Element(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TElement>)
          requires cs.StrictlySplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, ElementSpec)
          decreases cs.Length()
        {
          json.fn(cs)
        }

        import opened BoundedInts

        import opened Grammar

        import opened Cursors

        import opened Core
      }

      module Arrays refines Sequences {

        import opened Params = ArrayParams
        function method {:opaque} {:fuel 0, 0} Array(cs: FreshCursor, json: ValueParser): (pr: ParseResult<jarray>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Array)
          decreases cs, json
        {
          var sp: Split<TBracketed> :- Bracketed(cs, json); SpecProperties.Bracketed_Morphism(sp.t); assert Spec.Bracketed(sp.t, SuffixedElementSpec) == Spec.Array(sp.t); Success(sp)
        }

        const SEPARATOR: byte := ',' as byte

        function SuffixedElementSpec(e: TSuffixedElement): bytes
          decreases e
        {
          ElementSpec(e.t) + Spec.CommaSuffix(e.suffix)
        }

        function BracketedSpec(ts: TBracketed): bytes
          decreases ts
        {
          Spec.Bracketed(ts, SuffixedElementSpec)
        }

        function SuffixedElementsSpec(ts: seq<TSuffixedElement>): bytes
          decreases ts
        {
          Spec.ConcatBytes(ts, SuffixedElementSpec)
        }

        function method {:opaque} {:fuel 0, 0} Open(cs: FreshCursor): (pr: ParseResult<jopen>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_: View_) => [OPEN])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(OPEN); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} Close(cs: FreshCursor): (pr: ParseResult<jclose>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_: View_) => [CLOSE])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(CLOSE); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} BracketedFromParts(ghost cs: Cursor, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>, close: Split<Structural<jclose>>): (sp: Split<TBracketed>)
          requires Grammar.NoTrailingSuffix(elems.t)
          requires open.StrictlySplitFrom?(cs, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires close.StrictlySplitFrom?(elems.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          ensures sp.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, open, elems, close
        {
          var sp: Split<Bracketed<jopen, TElement, jcomma, jclose>> := SP(Grammar.Bracketed(open.t, elems.t, close.t), close.cs);
          calc {
            cs.Bytes();
            Spec.Structural(open.t, SpecView) + open.cs.Bytes();
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
          }
          sp
        }

        function method {:opaque} {:fuel 0, 0} AppendWithSuffix(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jcomma>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jcomma>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures forall e: Suffixed<TElement, jcomma> | e in elems'.t :: e.suffix.NonEmpty?
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, NonEmpty(sep.t));
          var elems': Split<seq<Suffixed<Value, jcomma>>> := SP(elems.t + [suffixed], sep.cs);
          SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
          elems'
        }

        function method {:opaque} {:fuel 0, 0} AppendLast(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jclose>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures NoTrailingSuffix(elems'.t)
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          ensures sep.StrictlySplitFrom?(elems'.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, Empty());
          var elems': Split<seq<Suffixed<Value, jcomma>>> := SP(elems.t + [suffixed], elem.cs);
          SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
          elems'
        }

        function method {:opaque} {:tailrecursion} {:fuel 0, 0} Elements(ghost cs0: FreshCursor, json: ValueParser, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>): (pr: ParseResult<TBracketed>)
          requires open.StrictlySplitFrom?(cs0, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs0, BracketedSpec)
          decreases elems.cs.Length()
        {
          var elem: Split<TElement> :- Element(elems.cs, json); var sep: Split<Structural<jopt>> := Core.TryStructural(elem.cs); var s0: opt_byte := sep.t.t.Peek(); if s0 == SEPARATOR as opt_byte then var elems: Split<seq<TSuffixedElement>> := AppendWithSuffix(open.cs, json, elems, elem, sep); Elements(cs0, json, open, elems) else if s0 == CLOSE as opt_byte then var elems: Split<seq<TSuffixedElement>> := AppendLast(open.cs, json, elems, elem, sep); Success(BracketedFromParts(cs0, open, elems, sep)) else Failure(ExpectingAnyByte([CLOSE, SEPARATOR], s0))
        }

        function method {:opaque} {:fuel 0, 0} Bracketed(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TBracketed>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, json
        {
          var open: Split<Structural<jopen>> :- Core.Structural(cs, Parsers.Parser(Open, SpecView)); assert open.cs.StrictlySplitFrom?(json.cs); var elems: Split<seq<Suffixed<Value, jcomma>>> := SP([], open.cs); if open.cs.Peek() == CLOSE as opt_byte then var close: Split<Structural<jclose>> :- Core.Structural(open.cs, Parsers.Parser(Close, SpecView)); Success(BracketedFromParts(cs, open, elems, close)) else Elements(cs, json, open, elems)
        }

        lemma Valid(x: TBracketed)
          ensures x.l.t.Byte?(OPEN)
          ensures x.r.t.Byte?(CLOSE)
          ensures NoTrailingSuffix(x.data)
          ensures forall pf: Suffixed<TElement, jcomma> | pf in x.data :: pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          decreases x
        {
          ghost var xlt: jopen := x.l.t;
          ghost var xrt: jclose := x.r.t;
          forall pf: Suffixed<TElement, jcomma> | pf in x.data
            ensures pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          {
            if pf.suffix.NonEmpty? {
              ghost var xtt := pf.suffix.t.t;
            }
          }
        }

        import opened Wrappers

        import opened BoundedInts

        import SpecProperties

        import opened Vs = Views.Core

        import opened Grammar

        import opened Cursors

        import Parsers

        import opened Core

        type jopen = v: Vs.View
          | v.Byte?(OPEN)
          witness Vs.View.OfBytes([OPEN])

        type jclose = v: Vs.View
          | v.Byte?(CLOSE)
          witness Vs.View.OfBytes([CLOSE])

        type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>

        type TSuffixedElement = Suffixed<TElement, jcomma>
      }

      module ObjectParams refines SequenceParams {

        import opened Wrappers

        import Strings
        type TElement = jkv

        const OPEN: byte := '{' as byte
        const CLOSE: byte := '}' as byte

        function method Colon(cs: FreshCursor): (pr: ParseResult<jcolon>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
          decreases cs
        {
          var cs: Cursor :- cs.AssertChar(':'); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} KVFromParts(ghost cs: Cursor, k: Split<jstring>, colon: Split<Structural<jcolon>>, v: Split<Value>): (sp: Split<jkv>)
          requires k.StrictlySplitFrom?(cs, Spec.String)
          requires colon.StrictlySplitFrom?(k.cs, (c: Structural<jcolon>) => Spec.Structural(c, SpecView))
          requires v.StrictlySplitFrom?(colon.cs, Spec.Value)
          ensures sp.StrictlySplitFrom?(cs, Spec.KV)
          decreases cs, k, colon, v
        {
          var sp: Split<jkv> := SP(Grammar.KV(k.t, colon.t, v.t), v.cs);
          calc {
            cs.Bytes();
            Spec.String(k.t) + k.cs.Bytes();
            Spec.String(k.t) + Spec.Structural(colon.t, SpecView) + colon.cs.Bytes();
            Spec.String(k.t) + Spec.Structural(colon.t, SpecView) + Spec.Value(v.t) + v.cs.Bytes();
            Spec.KV(sp.t) + v.cs.Bytes();
          }
          sp
        }

        function method ElementSpec(t: TElement): bytes
          decreases t
        {
          Spec.KV(t)
        }

        function method {:opaque} {:fuel 0, 0} Element(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TElement>)
          requires cs.StrictlySplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, ElementSpec)
          decreases cs.Length()
        {
          var k: Split<jstring> :- Strings.String(cs); var colon: Split<Structural<jcolon>> :- Core.Structural(k.cs, Parsers.Parser(Colon, SpecView)); var v: Split<Value> :- json.fn(colon.cs); Success(KVFromParts(cs, k, colon, v))
        }

        import opened BoundedInts

        import opened Grammar

        import opened Cursors

        import opened Core
      }

      module Objects refines Sequences {

        import opened Params = ObjectParams
        function method {:opaque} {:fuel 0, 0} Object(cs: FreshCursor, json: ValueParser): (pr: ParseResult<jobject>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Object)
          decreases cs, json
        {
          var sp: Split<TBracketed> :- Bracketed(cs, json); SpecProperties.Bracketed_Morphism(sp.t); assert Spec.Bracketed(sp.t, SuffixedElementSpec) == Spec.Object(sp.t); Success(sp)
        }

        const SEPARATOR: byte := ',' as byte

        function SuffixedElementSpec(e: TSuffixedElement): bytes
          decreases e
        {
          ElementSpec(e.t) + Spec.CommaSuffix(e.suffix)
        }

        function BracketedSpec(ts: TBracketed): bytes
          decreases ts
        {
          Spec.Bracketed(ts, SuffixedElementSpec)
        }

        function SuffixedElementsSpec(ts: seq<TSuffixedElement>): bytes
          decreases ts
        {
          Spec.ConcatBytes(ts, SuffixedElementSpec)
        }

        function method {:opaque} {:fuel 0, 0} Open(cs: FreshCursor): (pr: ParseResult<jopen>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_: View_) => [OPEN])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(OPEN); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} Close(cs: FreshCursor): (pr: ParseResult<jclose>)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, (_: View_) => [CLOSE])
          decreases cs
        {
          var cs: Cursor :- cs.AssertByte(CLOSE); Success(cs.Split())
        }

        function method {:opaque} {:fuel 0, 0} BracketedFromParts(ghost cs: Cursor, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>, close: Split<Structural<jclose>>): (sp: Split<TBracketed>)
          requires Grammar.NoTrailingSuffix(elems.t)
          requires open.StrictlySplitFrom?(cs, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires close.StrictlySplitFrom?(elems.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          ensures sp.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, open, elems, close
        {
          var sp: Split<Bracketed<jopen, TElement, jcomma, jclose>> := SP(Grammar.Bracketed(open.t, elems.t, close.t), close.cs);
          calc {
            cs.Bytes();
            Spec.Structural(open.t, SpecView) + open.cs.Bytes();
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
            Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
          }
          sp
        }

        function method {:opaque} {:fuel 0, 0} AppendWithSuffix(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jcomma>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jcomma>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures forall e: Suffixed<TElement, jcomma> | e in elems'.t :: e.suffix.NonEmpty?
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, NonEmpty(sep.t));
          var elems': Split<seq<Suffixed<jkv, jcomma>>> := SP(elems.t + [suffixed], sep.cs);
          SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
          elems'
        }

        function method {:opaque} {:fuel 0, 0} AppendLast(ghost cs0: FreshCursor, ghost json: ValueParser, elems: Split<seq<TSuffixedElement>>, elem: Split<TElement>, sep: Split<Structural<jclose>>): (elems': Split<seq<TSuffixedElement>>)
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
          requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
          requires sep.StrictlySplitFrom?(elem.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
          ensures NoTrailingSuffix(elems'.t)
          ensures elems'.cs.Length() < elems.cs.Length()
          ensures elems'.cs.StrictlySplitFrom?(json.cs)
          ensures sep.StrictlySplitFrom?(elems'.cs, (c: Structural<jclose>) => Spec.Structural(c, SpecView))
          decreases cs0, json, elems, elem, sep
        {
          var suffixed: Suffixed<TElement, jcomma> := Suffixed(elem.t, Empty());
          var elems': Split<seq<Suffixed<jkv, jcomma>>> := SP(elems.t + [suffixed], elem.cs);
          SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
          elems'
        }

        function method {:opaque} {:tailrecursion} {:fuel 0, 0} Elements(ghost cs0: FreshCursor, json: ValueParser, open: Split<Structural<jopen>>, elems: Split<seq<TSuffixedElement>>): (pr: ParseResult<TBracketed>)
          requires open.StrictlySplitFrom?(cs0, (c: Structural<jopen>) => Spec.Structural(c, SpecView))
          requires elems.cs.StrictlySplitFrom?(json.cs)
          requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
          requires forall e: Suffixed<TElement, jcomma> | e in elems.t :: e.suffix.NonEmpty?
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs0, BracketedSpec)
          decreases elems.cs.Length()
        {
          var elem: Split<TElement> :- Element(elems.cs, json); var sep: Split<Structural<jopt>> := Core.TryStructural(elem.cs); var s0: opt_byte := sep.t.t.Peek(); if s0 == SEPARATOR as opt_byte then var elems: Split<seq<TSuffixedElement>> := AppendWithSuffix(open.cs, json, elems, elem, sep); Elements(cs0, json, open, elems) else if s0 == CLOSE as opt_byte then var elems: Split<seq<TSuffixedElement>> := AppendLast(open.cs, json, elems, elem, sep); Success(BracketedFromParts(cs0, open, elems, sep)) else Failure(ExpectingAnyByte([CLOSE, SEPARATOR], s0))
        }

        function method {:opaque} {:fuel 0, 0} Bracketed(cs: FreshCursor, json: ValueParser): (pr: ParseResult<TBracketed>)
          requires cs.SplitFrom?(json.cs)
          ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, BracketedSpec)
          decreases cs, json
        {
          var open: Split<Structural<jopen>> :- Core.Structural(cs, Parsers.Parser(Open, SpecView)); assert open.cs.StrictlySplitFrom?(json.cs); var elems: Split<seq<Suffixed<jkv, jcomma>>> := SP([], open.cs); if open.cs.Peek() == CLOSE as opt_byte then var close: Split<Structural<jclose>> :- Core.Structural(open.cs, Parsers.Parser(Close, SpecView)); Success(BracketedFromParts(cs, open, elems, close)) else Elements(cs, json, open, elems)
        }

        lemma Valid(x: TBracketed)
          ensures x.l.t.Byte?(OPEN)
          ensures x.r.t.Byte?(CLOSE)
          ensures NoTrailingSuffix(x.data)
          ensures forall pf: Suffixed<TElement, jcomma> | pf in x.data :: pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          decreases x
        {
          ghost var xlt: jopen := x.l.t;
          ghost var xrt: jclose := x.r.t;
          forall pf: Suffixed<TElement, jcomma> | pf in x.data
            ensures pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
          {
            if pf.suffix.NonEmpty? {
              ghost var xtt := pf.suffix.t.t;
            }
          }
        }

        import opened Wrappers

        import opened BoundedInts

        import SpecProperties

        import opened Vs = Views.Core

        import opened Grammar

        import opened Cursors

        import Parsers

        import opened Core

        type jopen = v: Vs.View
          | v.Byte?(OPEN)
          witness Vs.View.OfBytes([OPEN])

        type jclose = v: Vs.View
          | v.Byte?(CLOSE)
          witness Vs.View.OfBytes([CLOSE])

        type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>

        type TSuffixedElement = Suffixed<TElement, jcomma>
      }
    }
  }
}

module Views {

  module {:options ""/functionSyntax:4""} Core {

    import opened BoundedInts
    type View = v: View_
      | v.Valid?
      witness View([], 0, 0)

    datatype View_ = View(s: bytes, beg: uint32, end: uint32) {
      ghost const Valid?: bool := 0 <= beg as int <= end as int <= |s| < TWO_TO_THE_32
      static const Empty: View := View([], 0, 0)
      const Empty? := beg == end

      function method Length(): uint32
        requires Valid?
        decreases this
      {
        end - beg
      }

      function method Bytes(): bytes
        requires Valid?
        decreases this
      {
        s[beg .. end]
      }

      static function method OfBytes(bs: bytes): (v: View)
        requires |bs| < TWO_TO_THE_32
        ensures v.Bytes() == bs
        decreases bs
      {
        View(bs, 0 as uint32, |bs| as uint32)
      }

      predicate Byte?(c: byte)
        requires Valid?
        decreases this, c
      {
        Bytes() == [c]
      }

      predicate Char?(c: char)
        requires Valid?
        requires c as int < 256
        decreases this, c
      {
        Byte?(c as byte)
      }

      predicate method ValidIndex?(idx: uint32)
        decreases this, idx
      {
        beg as int + idx as int < end as int
      }

      function method At(idx: uint32): byte
        requires Valid?
        requires ValidIndex?(idx)
        decreases this, idx
      {
        s[beg + idx]
      }

      function method Peek(): (r: opt_byte)
        requires Valid?
        ensures r < 0 <==> Empty?
        decreases this
      {
        if Empty? then
          -1
        else
          At(0) as opt_byte
      }

      method Blit(bs: array<byte>, start: uint32 := 0)
        requires Valid?
        requires start as int + Length() as int <= bs.Length
        requires start as int + Length() as int < TWO_TO_THE_32
        modifies bs
        ensures bs[start .. start + Length()] == Bytes()
        ensures bs[start + Length()..] == old(bs[start + Length()..])
        decreases this, bs, start
      {
        for idx: uint32 := 0 to Length()
          invariant bs[start .. start + idx] == Bytes()[..idx]
          invariant bs[start + Length()..] == old(bs[start + Length()..])
        {
          bs[start + idx] := s[beg + idx];
        }
      }
    }

    predicate method Adjacent(lv: View, rv: View)
      decreases lv, rv
    {
      lv.s == rv.s &&
      lv.end == rv.beg
    }

    function method Merge(lv: View, rv: View): View
      requires Adjacent(lv, rv)
      decreases lv, rv
    {
      lv.(end := rv.end)
    }
  }

  module {:options ""/functionSyntax:4""} Writers {

    import opened BoundedInts

    import opened Wrappers

    import opened Core
    datatype Chain = Empty | Chain(previous: Chain, v: View) {
      function method Length(): nat
        decreases this
      {
        if Empty? then
          0
        else
          previous.Length() + v.Length() as int
      }

      function method Count(): nat
        decreases this
      {
        if Empty? then
          0
        else
          previous.Count() + 1
      }

      function method Bytes(): (bs: bytes)
        ensures |bs| == Length()
        decreases this
      {
        if Empty? then
          []
        else
          previous.Bytes() + v.Bytes()
      }

      function method Append(v': View): (c: Chain)
        ensures c.Bytes() == Bytes() + v'.Bytes()
        decreases this, v'
      {
        if Chain? && Adjacent(v, v') then
          Chain(previous, Merge(v, v'))
        else
          Chain(this, v')
      }

      method {:tailrecursion} Blit(bs: array<byte>, end: uint32)
        requires end as int == Length() <= bs.Length
        modifies bs
        ensures bs[..end] == Bytes()
        ensures bs[end..] == old(bs[end..])
        decreases this, bs, end
      {
        if Chain? {
          var end := end - v.Length();
          v.Blit(bs, end);
          previous.Blit(bs, end);
        }
      }
    }

    type Writer = w: Writer_
      | w.Valid?
      witness Writer(0, Chain.Empty)

    datatype Writer_ = Writer(length: uint32, chain: Chain) {
      static const Empty: Writer := Writer(0, Chain.Empty)
      const Empty? := chain.Empty?
      const Unsaturated? := length != UINT32_MAX

      function Length(): nat
        decreases this
      {
        chain.Length()
      }

      ghost const Valid? := length == if chain.Length() >= TWO_TO_THE_32 then UINT32_MAX else chain.Length() as uint32

      function method Bytes(): (bs: bytes)
        ensures |bs| == Length()
        decreases this
      {
        chain.Bytes()
      }

      static function method SaturatedAddU32(a: uint32, b: uint32): uint32
        decreases a, b
      {
        if a <= UINT32_MAX - b then
          a + b
        else
          UINT32_MAX
      }

      function method {:opaque} {:fuel 0, 0} Append(v': View): (rw: Writer)
        requires Valid?
        ensures rw.Unsaturated? <==> v'.Length() < UINT32_MAX - length
        ensures rw.Bytes() == Bytes() + v'.Bytes()
        decreases this, v'
      {
        Writer(SaturatedAddU32(length, v'.Length()), chain.Append(v'))
      }

      function method Then(fn: Writer ~> Writer): Writer
        requires Valid?
        requires fn.requires(this)
        reads fn.reads
        decreases set _x0: Writer, _o0: object? | _o0 in fn.reads(_x0) :: _o0, this
      {
        fn(this)
      }

      method {:tailrecursion} Blit(bs: array<byte>)
        requires Valid?
        requires Unsaturated?
        requires Length() <= bs.Length
        modifies bs
        ensures bs[..length] == Bytes()
        ensures bs[length..] == old(bs[length..])
        decreases this, bs
      {
        chain.Blit(bs, length);
      }

      method ToArray() returns (bs: array<byte>)
        requires Valid?
        requires Unsaturated?
        ensures fresh(bs)
        ensures bs[..] == Bytes()
        decreases this
      {
        bs := new byte[length];
        Blit(bs);
      }
    }
  }
}
")]

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ITuple3GOO<out T1, out T2> {
    T1 dtor__0 { get; }
    T2 dtor__1 { get; }
    _ITuple3GOO<__T1, __T2> DowncastClone<__T1, __T2>(Func<T1, __T1> converter0, Func<T2, __T2> converter1);
  }
  public class Tuple3GOO<T1, T2> : _ITuple3GOO<T1, T2> {
    public readonly T1 _0;
    public readonly T2 _1;
    public Tuple3GOO(T1 _0, T2 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public _ITuple3GOO<__T1, __T2> DowncastClone<__T1, __T2>(Func<T1, __T1> converter0, Func<T2, __T2> converter1) {
      if (this is _ITuple3GOO<__T1, __T2> dt) { return dt; }
      return new Tuple3GOO<__T1, __T2>(converter0(_0), converter1(_1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3GOO<T1, T2>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static _ITuple3GOO<T1, T2> Default(T1 _default_T1, T2 _default_T2) {
      return create(_default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3GOO<T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3GOO<T1, T2>>(_System.Tuple3GOO<T1, T2>.Default(_td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3GOO<T1, T2> create(T1 _0, T2 _1) {
      return new Tuple3GOO<T1, T2>(_0, _1);
    }
    public T1 dtor__0 {
      get {
        return this._0;
      }
    }
    public T2 dtor__1 {
      get {
        return this._1;
      }
    }
  }

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace BoundedInts_Compile {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int8 {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class opt__byte {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static BigInteger TWO__TO__THE__8 { get {
      return new BigInteger(256);
    } }
    public static byte UINT8__MAX { get {
      return 255;
    } }
    public static BigInteger TWO__TO__THE__16 { get {
      return new BigInteger(65536);
    } }
    public static ushort UINT16__MAX { get {
      return 65535;
    } }
    public static BigInteger TWO__TO__THE__32 { get {
      return new BigInteger(4294967296L);
    } }
    public static uint UINT32__MAX { get {
      return 4294967295U;
    } }
    public static BigInteger TWO__TO__THE__64 { get {
      return BigInteger.Parse("18446744073709551616");
    } }
    public static ulong UINT64__MAX { get {
      return 18446744073709551615UL;
    } }
    public static sbyte INT8__MIN { get {
      return -128;
    } }
    public static sbyte INT8__MAX { get {
      return 127;
    } }
    public static short INT16__MIN { get {
      return -32768;
    } }
    public static short INT16__MAX { get {
      return 32767;
    } }
    public static int INT32__MIN { get {
      return -2147483648;
    } }
    public static int INT32__MAX { get {
      return 2147483647;
    } }
    public static long INT64__MIN { get {
      return -9223372036854775808L;
    } }
    public static long INT64__MAX { get {
      return 9223372036854775807L;
    } }
    public static byte NAT8__MAX { get {
      return 127;
    } }
    public static ushort NAT16__MAX { get {
      return 32767;
    } }
    public static uint NAT32__MAX { get {
      return 2147483647U;
    } }
    public static ulong NAT64__MAX { get {
      return 9223372036854775807UL;
    } }
    public static BigInteger TWO__TO__THE__0 { get {
      return BigInteger.One;
    } }
    public static BigInteger TWO__TO__THE__1 { get {
      return new BigInteger(2);
    } }
    public static BigInteger TWO__TO__THE__2 { get {
      return new BigInteger(4);
    } }
    public static BigInteger TWO__TO__THE__4 { get {
      return new BigInteger(16);
    } }
    public static BigInteger TWO__TO__THE__5 { get {
      return new BigInteger(32);
    } }
    public static BigInteger TWO__TO__THE__24 { get {
      return new BigInteger(16777216);
    } }
    public static BigInteger TWO__TO__THE__40 { get {
      return new BigInteger(1099511627776L);
    } }
    public static BigInteger TWO__TO__THE__48 { get {
      return new BigInteger(281474976710656L);
    } }
    public static BigInteger TWO__TO__THE__56 { get {
      return new BigInteger(72057594037927936L);
    } }
    public static BigInteger TWO__TO__THE__128 { get {
      return BigInteger.Parse("340282366920938463463374607431768211456");
    } }
    public static BigInteger TWO__TO__THE__256 { get {
      return BigInteger.Parse("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    } }
    public static BigInteger TWO__TO__THE__512 { get {
      return BigInteger.Parse("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096");
    } }
  }
} // end of namespace BoundedInts_Compile
namespace Views_mCore_Compile {

  public partial class View {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(Views_mCore_Compile.View.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IView__ {
    bool is_View { get; }
    Dafny.ISequence<byte> dtor_s { get; }
    uint dtor_beg { get; }
    uint dtor_end { get; }
    _IView__ DowncastClone();
    bool Empty_q { get; }
    uint Length();
    Dafny.ISequence<byte> Bytes();
    bool ValidIndex_q(uint idx);
    byte At(uint idx);
    short Peek();
    void Blit(byte[] bs, uint start);
  }
  public class View__ : _IView__ {
    public readonly Dafny.ISequence<byte> s;
    public readonly uint beg;
    public readonly uint end;
    public View__(Dafny.ISequence<byte> s, uint beg, uint end) {
      this.s = s;
      this.beg = beg;
      this.end = end;
    }
    public _IView__ DowncastClone() {
      if (this is _IView__ dt) { return dt; }
      return new View__(s, beg, end);
    }
    public override bool Equals(object other) {
      var oth = other as Views_mCore_Compile.View__;
      return oth != null && object.Equals(this.s, oth.s) && this.beg == oth.beg && this.end == oth.end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Views_mCore_Compile.View_.View";
      ss += "(";
      ss += Dafny.Helpers.ToString(this.s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.end);
      ss += ")";
      return ss;
    }
    private static readonly _IView__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0);
    public static _IView__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(Views_mCore_Compile.View__.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IView__ create(Dafny.ISequence<byte> s, uint beg, uint end) {
      return new View__(s, beg, end);
    }
    public bool is_View { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this.s;
      }
    }
    public uint dtor_beg {
      get {
        return this.beg;
      }
    }
    public uint dtor_end {
      get {
        return this.end;
      }
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public static Views_mCore_Compile._IView__ OfBytes(Dafny.ISequence<byte> bs) {
      return Views_mCore_Compile.View__.create(bs, (uint)(0U), (uint)(bs).LongCount);
    }
    public bool ValidIndex_q(uint idx) {
      return ((new BigInteger((this).dtor_beg)) + (new BigInteger(idx))) < (new BigInteger((this).dtor_end));
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public short Peek() {
      if ((this).Empty_q) {
        return -1;
      } else {
        return (short)((this).At(0U));
      }
    }
    public void Blit(byte[] bs, uint start)
    {
      uint _hi0 = (this).Length();
      for (uint _0_idx = 0U; _0_idx < _hi0; _0_idx++) {
        var _index0 = (start) + (_0_idx);
        (bs)[(int)(_index0)] = ((this).dtor_s).Select(((this).dtor_beg) + (_0_idx));
      }
    }
    public static Views_mCore_Compile._IView__ Empty { get {
      return Views_mCore_Compile.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    } }
    public bool Empty_q { get {
      return ((this).dtor_beg) == ((this).dtor_end);
    } }
  }

  public partial class __default {
    public static bool Adjacent(Views_mCore_Compile._IView__ lv, Views_mCore_Compile._IView__ rv)
    {
      return (((lv).dtor_s).Equals(((rv).dtor_s))) && (((lv).dtor_end) == ((rv).dtor_beg));
    }
    public static Views_mCore_Compile._IView__ Merge(Views_mCore_Compile._IView__ lv, Views_mCore_Compile._IView__ rv)
    {
      Views_mCore_Compile._IView__ _1_dt__update__tmp_h0 = lv;
      uint _2_dt__update_hend_h0 = (rv).dtor_end;
      return Views_mCore_Compile.View__.create((_1_dt__update__tmp_h0).dtor_s, (_1_dt__update__tmp_h0).dtor_beg, _2_dt__update_hend_h0);
    }
  }
} // end of namespace Views_mCore_Compile
namespace Wrappers_Compile {

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult();
    bool IsFailure();
    Wrappers_Compile._IOption<__U> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() { }
    public static _IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>>(Wrappers_Compile.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d).@value;
      }
    }
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile._IOption<T> _source0 = this;
      if (_source0.is_None) {
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _3___mcc_h0 = _source0.dtor_value;
        T _4_v = _3___mcc_h0;
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Success(_4_v);
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IOption<T> _this, T @default) {
      Wrappers_Compile._IOption<T> _source1 = _this;
      if (_source1.is_None) {
        return @default;
      } else {
        T _5___mcc_h0 = _source1.dtor_value;
        T _6_v = _5___mcc_h0;
        return _6_v;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers_Compile._IOption<__U> PropagateFailure<__U>() {
      return Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.None";
      return s;
    }
  }
  public class Option_Some<T> : Option<T> {
    public readonly T @value;
    public Option_Some(T @value) {
      this.@value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_Some<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

  public interface _IResult<out T, out R> {
    bool is_Success { get; }
    bool is_Failure { get; }
    T dtor_value { get; }
    R dtor_error { get; }
    _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    Wrappers_Compile._IOption<T> ToOption();
    bool IsFailure();
    Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Result<T, R> : _IResult<T, R> {
    public Result() { }
    public static _IResult<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    public static _IResult<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static _IResult<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d).@value;
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d).error;
      }
    }
    public abstract _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers_Compile._IOption<T> ToOption() {
      Wrappers_Compile._IResult<T, R> _source2 = this;
      if (_source2.is_Success) {
        T _7___mcc_h0 = _source2.dtor_value;
        T _8_s = _7___mcc_h0;
        return Wrappers_Compile.Option<T>.create_Some(_8_s);
      } else {
        R _9___mcc_h1 = _source2.dtor_error;
        R _10_e = _9___mcc_h1;
        return Wrappers_Compile.Option<T>.create_None();
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IResult<T, R> _this, T @default) {
      Wrappers_Compile._IResult<T, R> _source3 = _this;
      if (_source3.is_Success) {
        T _11___mcc_h0 = _source3.dtor_value;
        T _12_s = _11___mcc_h0;
        return _12_s;
      } else {
        R _13___mcc_h1 = _source3.dtor_error;
        R _14_e = _13___mcc_h1;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public static Wrappers_Compile._IResult<T, __NewR> MapFailure<__NewR>(Wrappers_Compile._IResult<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers_Compile._IResult<T, R> _source4 = _this;
      if (_source4.is_Success) {
        T _15___mcc_h0 = _source4.dtor_value;
        T _16_s = _15___mcc_h0;
        return Wrappers_Compile.Result<T, __NewR>.create_Success(_16_s);
      } else {
        R _17___mcc_h1 = _source4.dtor_error;
        R _18_e = _17___mcc_h1;
        return Wrappers_Compile.Result<T, __NewR>.create_Failure(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_18_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T @value;
    public Result_Success(T @value) {
      this.@value = @value;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Success<T, R>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R error;
    public Result_Failure(R error) {
      this.error = error;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Failure<T, R>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public interface _IOutcome<E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() { }
    public static _IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d).error;
      }
    }
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Pass";
      return s;
    }
  }
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E error;
    public Outcome_Fail(E error) {
      this.error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Fail<E>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IOutcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Wrappers_Compile.Outcome<__E>.create_Pass();
      } else {
        return Wrappers_Compile.Outcome<__E>.create_Fail(error);
      }
    }
  }
} // end of namespace Wrappers_Compile
namespace Views_mWriters_Compile {

  public interface _IChain {
    bool is_Empty { get; }
    bool is_Chain { get; }
    Views_mWriters_Compile._IChain dtor_previous { get; }
    Views_mCore_Compile._IView__ dtor_v { get; }
    _IChain DowncastClone();
    BigInteger Length();
    BigInteger Count();
    Dafny.ISequence<byte> Bytes();
    Views_mWriters_Compile._IChain Append(Views_mCore_Compile._IView__ v_k);
    void Blit(byte[] bs, uint end);
  }
  public abstract class Chain : _IChain {
    public Chain() { }
    private static readonly _IChain theDefault = create_Empty();
    public static _IChain Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile._IChain> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile._IChain>(Views_mWriters_Compile.Chain.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile._IChain> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IChain create_Empty() {
      return new Chain_Empty();
    }
    public static _IChain create_Chain(Views_mWriters_Compile._IChain previous, Views_mCore_Compile._IView__ v) {
      return new Chain_Chain(previous, v);
    }
    public bool is_Empty { get { return this is Chain_Empty; } }
    public bool is_Chain { get { return this is Chain_Chain; } }
    public Views_mWriters_Compile._IChain dtor_previous {
      get {
        var d = this;
        return ((Chain_Chain)d).previous;
      }
    }
    public Views_mCore_Compile._IView__ dtor_v {
      get {
        var d = this;
        return ((Chain_Chain)d).v;
      }
    }
    public abstract _IChain DowncastClone();
    public BigInteger Length() {
      BigInteger _19___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_19___accumulator);
      } else {
        _19___accumulator = (new BigInteger(((_this).dtor_v).Length())) + (_19___accumulator);
        var _in0 = (_this).dtor_previous;
        _this = _in0;
        goto TAIL_CALL_START;
      }
    }
    public BigInteger Count() {
      BigInteger _20___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_20___accumulator);
      } else {
        _20___accumulator = (BigInteger.One) + (_20___accumulator);
        var _in1 = (_this).dtor_previous;
        _this = _in1;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      Dafny.ISequence<byte> _21___accumulator = Dafny.Sequence<byte>.FromElements();
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(), _21___accumulator);
      } else {
        _21___accumulator = Dafny.Sequence<byte>.Concat(((_this).dtor_v).Bytes(), _21___accumulator);
        var _in2 = (_this).dtor_previous;
        _this = _in2;
        goto TAIL_CALL_START;
      }
    }
    public Views_mWriters_Compile._IChain Append(Views_mCore_Compile._IView__ v_k) {
      if (((this).is_Chain) && (Views_mCore_Compile.__default.Adjacent((this).dtor_v, v_k))) {
        return Views_mWriters_Compile.Chain.create_Chain((this).dtor_previous, Views_mCore_Compile.__default.Merge((this).dtor_v, v_k));
      } else {
        return Views_mWriters_Compile.Chain.create_Chain(this, v_k);
      }
    }
    public void Blit(byte[] bs, uint end)
    {
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Chain) {
        uint _22_end;
        _22_end = (end) - (((_this).dtor_v).Length());
        ((_this).dtor_v).Blit(bs, _22_end);
        var _in3 = (_this).dtor_previous;
        byte[] _in4 = bs;
        uint _in5 = _22_end;
        _this = _in3;
        bs = _in4;
        end = _in5;
        goto TAIL_CALL_START;
      }
    }
  }
  public class Chain_Empty : Chain {
    public Chain_Empty() {
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
      return new Chain_Empty();
    }
    public override bool Equals(object other) {
      var oth = other as Views_mWriters_Compile.Chain_Empty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Views_mWriters_Compile.Chain.Empty";
      return s;
    }
  }
  public class Chain_Chain : Chain {
    public readonly Views_mWriters_Compile._IChain previous;
    public readonly Views_mCore_Compile._IView__ v;
    public Chain_Chain(Views_mWriters_Compile._IChain previous, Views_mCore_Compile._IView__ v) {
      this.previous = previous;
      this.v = v;
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
      return new Chain_Chain(previous, v);
    }
    public override bool Equals(object other) {
      var oth = other as Views_mWriters_Compile.Chain_Chain;
      return oth != null && object.Equals(this.previous, oth.previous) && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.previous));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Views_mWriters_Compile.Chain.Chain";
      s += "(";
      s += Dafny.Helpers.ToString(this.previous);
      s += ", ";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
  }

  public partial class Writer {
    private static readonly Views_mWriters_Compile._IWriter__ Witness = Views_mWriters_Compile.Writer__.create(0U, Views_mWriters_Compile.Chain.create_Empty());
    public static Views_mWriters_Compile._IWriter__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__>(Views_mWriters_Compile.Writer.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IWriter__ {
    bool is_Writer { get; }
    uint dtor_length { get; }
    Views_mWriters_Compile._IChain dtor_chain { get; }
    _IWriter__ DowncastClone();
    bool Empty_q { get; }
    bool Unsaturated_q { get; }
    Dafny.ISequence<byte> Bytes();
    Views_mWriters_Compile._IWriter__ Append(Views_mCore_Compile._IView__ v_k);
    Views_mWriters_Compile._IWriter__ Then(Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__> fn);
    void Blit(byte[] bs);
    byte[] ToArray();
  }
  public class Writer__ : _IWriter__ {
    public readonly uint length;
    public readonly Views_mWriters_Compile._IChain chain;
    public Writer__(uint length, Views_mWriters_Compile._IChain chain) {
      this.length = length;
      this.chain = chain;
    }
    public _IWriter__ DowncastClone() {
      if (this is _IWriter__ dt) { return dt; }
      return new Writer__(length, chain);
    }
    public override bool Equals(object other) {
      var oth = other as Views_mWriters_Compile.Writer__;
      return oth != null && this.length == oth.length && object.Equals(this.chain, oth.chain);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.length));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.chain));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Views_mWriters_Compile.Writer_.Writer";
      s += "(";
      s += Dafny.Helpers.ToString(this.length);
      s += ", ";
      s += Dafny.Helpers.ToString(this.chain);
      s += ")";
      return s;
    }
    private static readonly _IWriter__ theDefault = create(0, Views_mWriters_Compile.Chain.Default());
    public static _IWriter__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__>(Views_mWriters_Compile.Writer__.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWriter__ create(uint length, Views_mWriters_Compile._IChain chain) {
      return new Writer__(length, chain);
    }
    public bool is_Writer { get { return true; } }
    public uint dtor_length {
      get {
        return this.length;
      }
    }
    public Views_mWriters_Compile._IChain dtor_chain {
      get {
        return this.chain;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_chain).Bytes();
    }
    public static uint SaturatedAddU32(uint a, uint b)
    {
      if ((a) <= ((BoundedInts_Compile.__default.UINT32__MAX) - (b))) {
        return (a) + (b);
      } else {
        return BoundedInts_Compile.__default.UINT32__MAX;
      }
    }
    public Views_mWriters_Compile._IWriter__ Append(Views_mCore_Compile._IView__ v_k) {
      return Views_mWriters_Compile.Writer__.create(Views_mWriters_Compile.Writer__.SaturatedAddU32((this).dtor_length, (v_k).Length()), ((this).dtor_chain).Append(v_k));
    }
    public Views_mWriters_Compile._IWriter__ Then(Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__> fn) {
      return Dafny.Helpers.Id<Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__>>(fn)(this);
    }
    public void Blit(byte[] bs)
    {
      ((this).dtor_chain).Blit(bs, (this).dtor_length);
    }
    public byte[] ToArray()
    {
      byte[] bs = new byte[0];
      byte[] _nw0 = new byte[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked((this).dtor_length, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      bs = _nw0;
      (this).Blit(bs);
      return bs;
    }
    public static Views_mWriters_Compile._IWriter__ Empty { get {
      return Views_mWriters_Compile.Writer__.create(0U, Views_mWriters_Compile.Chain.create_Empty());
    } }
    public bool Unsaturated_q { get {
      return ((this).dtor_length) != (BoundedInts_Compile.__default.UINT32__MAX);
    } }
    public bool Empty_q { get {
      return ((this).dtor_chain).is_Empty;
    } }
  }

} // end of namespace Views_mWriters_Compile
namespace Views_Compile {

} // end of namespace Views_Compile
namespace JSON_mGrammar_Compile {

  public partial class jchar {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('b')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jchar.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jperiod {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('.')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jperiod.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class je {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('e')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.je.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcolon {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(':')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jcolon.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcomma {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(',')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jcomma.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbrace {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('{')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jlbrace.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbrace {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('}')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jrbrace.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbracket {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('[')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jlbracket.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbracket {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(']')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jrbracket.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jminus {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jminus.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jsign {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jsign.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jblanks {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jblanks.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IStructural<out T> {
    bool is_Structural { get; }
    Views_mCore_Compile._IView__ dtor_before { get; }
    T dtor_t { get; }
    Views_mCore_Compile._IView__ dtor_after { get; }
    _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Structural<T> : _IStructural<T> {
    public readonly Views_mCore_Compile._IView__ before;
    public readonly T t;
    public readonly Views_mCore_Compile._IView__ after;
    public Structural(Views_mCore_Compile._IView__ before, T t, Views_mCore_Compile._IView__ after) {
      this.before = before;
      this.t = t;
      this.after = after;
    }
    public _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IStructural<__T> dt) { return dt; }
      return new Structural<__T>(before, converter0(t), after);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Structural<T>;
      return oth != null && object.Equals(this.before, oth.before) && object.Equals(this.t, oth.t) && object.Equals(this.after, oth.after);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.before));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.after));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Structural.Structural";
      s += "(";
      s += Dafny.Helpers.ToString(this.before);
      s += ", ";
      s += Dafny.Helpers.ToString(this.t);
      s += ", ";
      s += Dafny.Helpers.ToString(this.after);
      s += ")";
      return s;
    }
    public static _IStructural<T> Default(T _default_T) {
      return create(JSON_mGrammar_Compile.jblanks.Default(), _default_T, JSON_mGrammar_Compile.jblanks.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IStructural<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IStructural<T>>(JSON_mGrammar_Compile.Structural<T>.Default(_td_T.Default()));
    }
    public static _IStructural<T> create(Views_mCore_Compile._IView__ before, T t, Views_mCore_Compile._IView__ after) {
      return new Structural<T>(before, t, after);
    }
    public bool is_Structural { get { return true; } }
    public Views_mCore_Compile._IView__ dtor_before {
      get {
        return this.before;
      }
    }
    public T dtor_t {
      get {
        return this.t;
      }
    }
    public Views_mCore_Compile._IView__ dtor_after {
      get {
        return this.after;
      }
    }
  }

  public interface _IMaybe<out T> {
    bool is_Empty { get; }
    bool is_NonEmpty { get; }
    T dtor_t { get; }
    _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Maybe<T> : _IMaybe<T> {
    public Maybe() { }
    public static _IMaybe<T> Default() {
      return create_Empty();
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IMaybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IMaybe<T>>(JSON_mGrammar_Compile.Maybe<T>.Default());
    }
    public static _IMaybe<T> create_Empty() {
      return new Maybe_Empty<T>();
    }
    public static _IMaybe<T> create_NonEmpty(T t) {
      return new Maybe_NonEmpty<T>(t);
    }
    public bool is_Empty { get { return this is Maybe_Empty<T>; } }
    public bool is_NonEmpty { get { return this is Maybe_NonEmpty<T>; } }
    public T dtor_t {
      get {
        var d = this;
        return ((Maybe_NonEmpty<T>)d).t;
      }
    }
    public abstract _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Maybe_Empty<T> : Maybe<T> {
    public Maybe_Empty() {
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_Empty<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Maybe_Empty<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Maybe.Empty";
      return s;
    }
  }
  public class Maybe_NonEmpty<T> : Maybe<T> {
    public readonly T t;
    public Maybe_NonEmpty(T t) {
      this.t = t;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
      return new Maybe_NonEmpty<__T>(converter0(t));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Maybe_NonEmpty<T>;
      return oth != null && object.Equals(this.t, oth.t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Maybe.NonEmpty";
      s += "(";
      s += Dafny.Helpers.ToString(this.t);
      s += ")";
      return s;
    }
  }

  public interface _ISuffixed<out T, out S> {
    bool is_Suffixed { get; }
    T dtor_t { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> dtor_suffix { get; }
    _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1);
  }
  public class Suffixed<T, S> : _ISuffixed<T, S> {
    public readonly T t;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix;
    public Suffixed(T t, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix) {
      this.t = t;
      this.suffix = suffix;
    }
    public _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1) {
      if (this is _ISuffixed<__T, __S> dt) { return dt; }
      return new Suffixed<__T, __S>(converter0(t), (suffix).DowncastClone<JSON_mGrammar_Compile._IStructural<__S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile._IStructural<S>, JSON_mGrammar_Compile._IStructural<__S>>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Suffixed<T, S>;
      return oth != null && object.Equals(this.t, oth.t) && object.Equals(this.suffix, oth.suffix);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.suffix));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Suffixed.Suffixed";
      s += "(";
      s += Dafny.Helpers.ToString(this.t);
      s += ", ";
      s += Dafny.Helpers.ToString(this.suffix);
      s += ")";
      return s;
    }
    public static _ISuffixed<T, S> Default(T _default_T) {
      return create(_default_T, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<S>>.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._ISuffixed<T, S>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._ISuffixed<T, S>>(JSON_mGrammar_Compile.Suffixed<T, S>.Default(_td_T.Default()));
    }
    public static _ISuffixed<T, S> create(T t, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix) {
      return new Suffixed<T, S>(t, suffix);
    }
    public bool is_Suffixed { get { return true; } }
    public T dtor_t {
      get {
        return this.t;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> dtor_suffix {
      get {
        return this.suffix;
      }
    }
  }

  public partial class SuffixedSequence<D, S> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>>>(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<D, S>>.Empty);
    }
  }

  public interface _IBracketed<out L, out D, out S, out R> {
    bool is_Bracketed { get; }
    JSON_mGrammar_Compile._IStructural<L> dtor_l { get; }
    Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> dtor_data { get; }
    JSON_mGrammar_Compile._IStructural<R> dtor_r { get; }
    _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3);
  }
  public class Bracketed<L, D, S, R> : _IBracketed<L, D, S, R> {
    public readonly JSON_mGrammar_Compile._IStructural<L> l;
    public readonly Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data;
    public readonly JSON_mGrammar_Compile._IStructural<R> r;
    public Bracketed(JSON_mGrammar_Compile._IStructural<L> l, Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data, JSON_mGrammar_Compile._IStructural<R> r) {
      this.l = l;
      this.data = data;
      this.r = r;
    }
    public _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3) {
      if (this is _IBracketed<__L, __D, __S, __R> dt) { return dt; }
      return new Bracketed<__L, __D, __S, __R>((l).DowncastClone<__L>(Dafny.Helpers.CastConverter<L, __L>), (data).DowncastClone<JSON_mGrammar_Compile._ISuffixed<__D, __S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile._ISuffixed<D, S>, JSON_mGrammar_Compile._ISuffixed<__D, __S>>), (r).DowncastClone<__R>(Dafny.Helpers.CastConverter<R, __R>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Bracketed<L, D, S, R>;
      return oth != null && object.Equals(this.l, oth.l) && object.Equals(this.data, oth.data) && object.Equals(this.r, oth.r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.l));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.data));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.r));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Bracketed.Bracketed";
      s += "(";
      s += Dafny.Helpers.ToString(this.l);
      s += ", ";
      s += Dafny.Helpers.ToString(this.data);
      s += ", ";
      s += Dafny.Helpers.ToString(this.r);
      s += ")";
      return s;
    }
    public static _IBracketed<L, D, S, R> Default(L _default_L, R _default_R) {
      return create(JSON_mGrammar_Compile.Structural<L>.Default(_default_L), Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<D, S>>.Empty, JSON_mGrammar_Compile.Structural<R>.Default(_default_R));
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IBracketed<L, D, S, R>> _TypeDescriptor(Dafny.TypeDescriptor<L> _td_L, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IBracketed<L, D, S, R>>(JSON_mGrammar_Compile.Bracketed<L, D, S, R>.Default(_td_L.Default(), _td_R.Default()));
    }
    public static _IBracketed<L, D, S, R> create(JSON_mGrammar_Compile._IStructural<L> l, Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data, JSON_mGrammar_Compile._IStructural<R> r) {
      return new Bracketed<L, D, S, R>(l, data, r);
    }
    public bool is_Bracketed { get { return true; } }
    public JSON_mGrammar_Compile._IStructural<L> dtor_l {
      get {
        return this.l;
      }
    }
    public Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> dtor_data {
      get {
        return this.data;
      }
    }
    public JSON_mGrammar_Compile._IStructural<R> dtor_r {
      get {
        return this.r;
      }
    }
  }

  public partial class jstring {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jstring.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jnull {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(JSON_mGrammar_Compile.__default.NULL);
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jnull.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jbool {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(JSON_mGrammar_Compile.__default.TRUE);
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jbool.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jdigits {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jdigits.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jnum {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('0')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jnum.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jint {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('0')));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mGrammar_Compile.jint.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _Ijkv {
    bool is_KV { get; }
    Views_mCore_Compile._IView__ dtor_k { get; }
    JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__> dtor_colon { get; }
    JSON_mGrammar_Compile._IValue dtor_v { get; }
    _Ijkv DowncastClone();
  }
  public class jkv : _Ijkv {
    public readonly Views_mCore_Compile._IView__ k;
    public readonly JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__> colon;
    public readonly JSON_mGrammar_Compile._IValue v;
    public jkv(Views_mCore_Compile._IView__ k, JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__> colon, JSON_mGrammar_Compile._IValue v) {
      this.k = k;
      this.colon = colon;
      this.v = v;
    }
    public _Ijkv DowncastClone() {
      if (this is _Ijkv dt) { return dt; }
      return new jkv(k, colon, v);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jkv;
      return oth != null && object.Equals(this.k, oth.k) && object.Equals(this.colon, oth.colon) && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.k));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.colon));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jkv.KV";
      s += "(";
      s += Dafny.Helpers.ToString(this.k);
      s += ", ";
      s += Dafny.Helpers.ToString(this.colon);
      s += ", ";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
    private static readonly _Ijkv theDefault = create(JSON_mGrammar_Compile.jstring.Default(), JSON_mGrammar_Compile.Structural<Views_mCore_Compile._IView__>.Default(JSON_mGrammar_Compile.jcolon.Default()), JSON_mGrammar_Compile.Value.Default());
    public static _Ijkv Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijkv> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijkv>(JSON_mGrammar_Compile.jkv.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijkv> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijkv create(Views_mCore_Compile._IView__ k, JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__> colon, JSON_mGrammar_Compile._IValue v) {
      return new jkv(k, colon, v);
    }
    public bool is_KV { get { return true; } }
    public Views_mCore_Compile._IView__ dtor_k {
      get {
        return this.k;
      }
    }
    public JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__> dtor_colon {
      get {
        return this.colon;
      }
    }
    public JSON_mGrammar_Compile._IValue dtor_v {
      get {
        return this.v;
      }
    }
  }

  public interface _Ijfrac {
    bool is_JFrac { get; }
    Views_mCore_Compile._IView__ dtor_period { get; }
    Views_mCore_Compile._IView__ dtor_num { get; }
    _Ijfrac DowncastClone();
  }
  public class jfrac : _Ijfrac {
    public readonly Views_mCore_Compile._IView__ period;
    public readonly Views_mCore_Compile._IView__ num;
    public jfrac(Views_mCore_Compile._IView__ period, Views_mCore_Compile._IView__ num) {
      this.period = period;
      this.num = num;
    }
    public _Ijfrac DowncastClone() {
      if (this is _Ijfrac dt) { return dt; }
      return new jfrac(period, num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jfrac;
      return oth != null && object.Equals(this.period, oth.period) && object.Equals(this.num, oth.num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.period));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jfrac.JFrac";
      s += "(";
      s += Dafny.Helpers.ToString(this.period);
      s += ", ";
      s += Dafny.Helpers.ToString(this.num);
      s += ")";
      return s;
    }
    private static readonly _Ijfrac theDefault = create(JSON_mGrammar_Compile.jperiod.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static _Ijfrac Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac>(JSON_mGrammar_Compile.jfrac.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijfrac create(Views_mCore_Compile._IView__ period, Views_mCore_Compile._IView__ num) {
      return new jfrac(period, num);
    }
    public bool is_JFrac { get { return true; } }
    public Views_mCore_Compile._IView__ dtor_period {
      get {
        return this.period;
      }
    }
    public Views_mCore_Compile._IView__ dtor_num {
      get {
        return this.num;
      }
    }
  }

  public interface _Ijexp {
    bool is_JExp { get; }
    Views_mCore_Compile._IView__ dtor_e { get; }
    Views_mCore_Compile._IView__ dtor_sign { get; }
    Views_mCore_Compile._IView__ dtor_num { get; }
    _Ijexp DowncastClone();
  }
  public class jexp : _Ijexp {
    public readonly Views_mCore_Compile._IView__ e;
    public readonly Views_mCore_Compile._IView__ sign;
    public readonly Views_mCore_Compile._IView__ num;
    public jexp(Views_mCore_Compile._IView__ e, Views_mCore_Compile._IView__ sign, Views_mCore_Compile._IView__ num) {
      this.e = e;
      this.sign = sign;
      this.num = num;
    }
    public _Ijexp DowncastClone() {
      if (this is _Ijexp dt) { return dt; }
      return new jexp(e, sign, num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jexp;
      return oth != null && object.Equals(this.e, oth.e) && object.Equals(this.sign, oth.sign) && object.Equals(this.num, oth.num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.e));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.sign));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jexp.JExp";
      s += "(";
      s += Dafny.Helpers.ToString(this.e);
      s += ", ";
      s += Dafny.Helpers.ToString(this.sign);
      s += ", ";
      s += Dafny.Helpers.ToString(this.num);
      s += ")";
      return s;
    }
    private static readonly _Ijexp theDefault = create(JSON_mGrammar_Compile.je.Default(), JSON_mGrammar_Compile.jsign.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static _Ijexp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp>(JSON_mGrammar_Compile.jexp.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijexp create(Views_mCore_Compile._IView__ e, Views_mCore_Compile._IView__ sign, Views_mCore_Compile._IView__ num) {
      return new jexp(e, sign, num);
    }
    public bool is_JExp { get { return true; } }
    public Views_mCore_Compile._IView__ dtor_e {
      get {
        return this.e;
      }
    }
    public Views_mCore_Compile._IView__ dtor_sign {
      get {
        return this.sign;
      }
    }
    public Views_mCore_Compile._IView__ dtor_num {
      get {
        return this.num;
      }
    }
  }

  public interface _Ijnumber {
    bool is_JNumber { get; }
    Views_mCore_Compile._IView__ dtor_minus { get; }
    Views_mCore_Compile._IView__ dtor_num { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> dtor_frac { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> dtor_exp { get; }
    _Ijnumber DowncastClone();
  }
  public class jnumber : _Ijnumber {
    public readonly Views_mCore_Compile._IView__ minus;
    public readonly Views_mCore_Compile._IView__ num;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp;
    public jnumber(Views_mCore_Compile._IView__ minus, Views_mCore_Compile._IView__ num, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp) {
      this.minus = minus;
      this.num = num;
      this.frac = frac;
      this.exp = exp;
    }
    public _Ijnumber DowncastClone() {
      if (this is _Ijnumber dt) { return dt; }
      return new jnumber(minus, num, frac, exp);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jnumber;
      return oth != null && object.Equals(this.minus, oth.minus) && object.Equals(this.num, oth.num) && object.Equals(this.frac, oth.frac) && object.Equals(this.exp, oth.exp);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.minus));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.frac));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.exp));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jnumber.JNumber";
      s += "(";
      s += Dafny.Helpers.ToString(this.minus);
      s += ", ";
      s += Dafny.Helpers.ToString(this.num);
      s += ", ";
      s += Dafny.Helpers.ToString(this.frac);
      s += ", ";
      s += Dafny.Helpers.ToString(this.exp);
      s += ")";
      return s;
    }
    private static readonly _Ijnumber theDefault = create(JSON_mGrammar_Compile.jminus.Default(), JSON_mGrammar_Compile.jnum.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.Default());
    public static _Ijnumber Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber>(JSON_mGrammar_Compile.jnumber.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijnumber create(Views_mCore_Compile._IView__ minus, Views_mCore_Compile._IView__ num, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp) {
      return new jnumber(minus, num, frac, exp);
    }
    public bool is_JNumber { get { return true; } }
    public Views_mCore_Compile._IView__ dtor_minus {
      get {
        return this.minus;
      }
    }
    public Views_mCore_Compile._IView__ dtor_num {
      get {
        return this.num;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> dtor_frac {
      get {
        return this.frac;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> dtor_exp {
      get {
        return this.exp;
      }
    }
  }

  public interface _IValue {
    bool is_Null { get; }
    bool is_Bool { get; }
    bool is_String { get; }
    bool is_Number { get; }
    bool is_Object { get; }
    bool is_Array { get; }
    Views_mCore_Compile._IView__ dtor_n { get; }
    Views_mCore_Compile._IView__ dtor_b { get; }
    Views_mCore_Compile._IView__ dtor_str { get; }
    JSON_mGrammar_Compile._Ijnumber dtor_num { get; }
    JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> dtor_obj { get; }
    JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> dtor_arr { get; }
    _IValue DowncastClone();
  }
  public abstract class Value : _IValue {
    public Value() { }
    private static readonly _IValue theDefault = create_Null(JSON_mGrammar_Compile.jnull.Default());
    public static _IValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue>(JSON_mGrammar_Compile.Value.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IValue create_Null(Views_mCore_Compile._IView__ n) {
      return new Value_Null(n);
    }
    public static _IValue create_Bool(Views_mCore_Compile._IView__ b) {
      return new Value_Bool(b);
    }
    public static _IValue create_String(Views_mCore_Compile._IView__ str) {
      return new Value_String(str);
    }
    public static _IValue create_Number(JSON_mGrammar_Compile._Ijnumber num) {
      return new Value_Number(num);
    }
    public static _IValue create_Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> obj) {
      return new Value_Object(obj);
    }
    public static _IValue create_Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> arr) {
      return new Value_Array(arr);
    }
    public bool is_Null { get { return this is Value_Null; } }
    public bool is_Bool { get { return this is Value_Bool; } }
    public bool is_String { get { return this is Value_String; } }
    public bool is_Number { get { return this is Value_Number; } }
    public bool is_Object { get { return this is Value_Object; } }
    public bool is_Array { get { return this is Value_Array; } }
    public Views_mCore_Compile._IView__ dtor_n {
      get {
        var d = this;
        return ((Value_Null)d).n;
      }
    }
    public Views_mCore_Compile._IView__ dtor_b {
      get {
        var d = this;
        return ((Value_Bool)d).b;
      }
    }
    public Views_mCore_Compile._IView__ dtor_str {
      get {
        var d = this;
        return ((Value_String)d).str;
      }
    }
    public JSON_mGrammar_Compile._Ijnumber dtor_num {
      get {
        var d = this;
        return ((Value_Number)d).num;
      }
    }
    public JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> dtor_obj {
      get {
        var d = this;
        return ((Value_Object)d).obj;
      }
    }
    public JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> dtor_arr {
      get {
        var d = this;
        return ((Value_Array)d).arr;
      }
    }
    public abstract _IValue DowncastClone();
  }
  public class Value_Null : Value {
    public readonly Views_mCore_Compile._IView__ n;
    public Value_Null(Views_mCore_Compile._IView__ n) {
      this.n = n;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Null(n);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Null;
      return oth != null && object.Equals(this.n, oth.n);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.n));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Null";
      s += "(";
      s += Dafny.Helpers.ToString(this.n);
      s += ")";
      return s;
    }
  }
  public class Value_Bool : Value {
    public readonly Views_mCore_Compile._IView__ b;
    public Value_Bool(Views_mCore_Compile._IView__ b) {
      this.b = b;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Bool(b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Bool;
      return oth != null && object.Equals(this.b, oth.b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Bool";
      s += "(";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public class Value_String : Value {
    public readonly Views_mCore_Compile._IView__ str;
    public Value_String(Views_mCore_Compile._IView__ str) {
      this.str = str;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_String(str);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_String;
      return oth != null && object.Equals(this.str, oth.str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.String";
      s += "(";
      s += Dafny.Helpers.ToString(this.str);
      s += ")";
      return s;
    }
  }
  public class Value_Number : Value {
    public readonly JSON_mGrammar_Compile._Ijnumber num;
    public Value_Number(JSON_mGrammar_Compile._Ijnumber num) {
      this.num = num;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Number(num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Number;
      return oth != null && object.Equals(this.num, oth.num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Number";
      s += "(";
      s += Dafny.Helpers.ToString(this.num);
      s += ")";
      return s;
    }
  }
  public class Value_Object : Value {
    public readonly JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> obj;
    public Value_Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> obj) {
      this.obj = obj;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Object(obj);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Object;
      return oth != null && object.Equals(this.obj, oth.obj);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Object";
      s += "(";
      s += Dafny.Helpers.ToString(this.obj);
      s += ")";
      return s;
    }
  }
  public class Value_Array : Value {
    public readonly JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> arr;
    public Value_Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> arr) {
      this.arr = arr;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
      return new Value_Array(arr);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Array;
      return oth != null && object.Equals(this.arr, oth.arr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.arr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this.arr);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static bool Blank_q(byte b) {
      return ((((b) == (32)) || ((b) == (9))) || ((b) == (10))) || ((b) == (13));
    }
    public static bool Digit_q(byte b) {
      return (((byte)('0')) <= (b)) && ((b) <= ((byte)('9')));
    }
    public static Dafny.ISequence<byte> NULL { get {
      return Dafny.Sequence<byte>.FromElements((byte)('n'), (byte)('u'), (byte)('l'), (byte)('l'));
    } }
    public static Dafny.ISequence<byte> TRUE { get {
      return Dafny.Sequence<byte>.FromElements((byte)('t'), (byte)('r'), (byte)('u'), (byte)('e'));
    } }
    public static Dafny.ISequence<byte> FALSE { get {
      return Dafny.Sequence<byte>.FromElements((byte)('f'), (byte)('a'), (byte)('l'), (byte)('s'), (byte)('e'));
    } }
  }
} // end of namespace JSON_mGrammar_Compile
namespace JSON_mSpec_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> View(Views_mCore_Compile._IView__ v) {
      return (v).Bytes();
    }
    public static Dafny.ISequence<byte> Structural<__T>(JSON_mGrammar_Compile._IStructural<__T> self, Func<__T, Dafny.ISequence<byte>> pt)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_before), Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(pt)((self).dtor_t)), JSON_mSpec_Compile.__default.View((self).dtor_after));
    }
    public static Dafny.ISequence<byte> StructuralView(JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__> self) {
      return JSON_mSpec_Compile.__default.Structural<Views_mCore_Compile._IView__>(self, JSON_mSpec_Compile.__default.View);
    }
    public static Dafny.ISequence<byte> Maybe<__T>(JSON_mGrammar_Compile._IMaybe<__T> self, Func<__T, Dafny.ISequence<byte>> pt)
    {
      if ((self).is_Empty) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        return Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(pt)((self).dtor_t);
      }
    }
    public static Dafny.ISequence<byte> ConcatBytes<__T>(Dafny.ISequence<__T> ts, Func<__T, Dafny.ISequence<byte>> pt)
    {
      Dafny.ISequence<byte> _23___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ts).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_23___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _23___accumulator = Dafny.Sequence<byte>.Concat(_23___accumulator, Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(pt)((ts).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> _in6 = (ts).Drop(BigInteger.One);
        Func<__T, Dafny.ISequence<byte>> _in7 = pt;
        ts = _in6;
        pt = _in7;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> Bracketed<__D, __S>(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, __D, __S, Views_mCore_Compile._IView__> self, Func<JSON_mGrammar_Compile._ISuffixed<__D, __S>, Dafny.ISequence<byte>> pdatum)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.StructuralView((self).dtor_l), JSON_mSpec_Compile.__default.ConcatBytes<JSON_mGrammar_Compile._ISuffixed<__D, __S>>((self).dtor_data, pdatum)), JSON_mSpec_Compile.__default.StructuralView((self).dtor_r));
    }
    public static Dafny.ISequence<byte> KV(JSON_mGrammar_Compile._Ijkv self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_k), JSON_mSpec_Compile.__default.StructuralView((self).dtor_colon)), JSON_mSpec_Compile.__default.Value((self).dtor_v));
    }
    public static Dafny.ISequence<byte> Frac(JSON_mGrammar_Compile._Ijfrac self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_period), JSON_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Exp(JSON_mGrammar_Compile._Ijexp self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_e), JSON_mSpec_Compile.__default.View((self).dtor_sign)), JSON_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Number(JSON_mGrammar_Compile._Ijnumber self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_minus), JSON_mSpec_Compile.__default.View((self).dtor_num)), JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._Ijfrac>((self).dtor_frac, JSON_mSpec_Compile.__default.Frac)), JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._Ijexp>((self).dtor_exp, JSON_mSpec_Compile.__default.Exp));
    }
    public static Dafny.ISequence<byte> String(Views_mCore_Compile._IView__ self) {
      return JSON_mSpec_Compile.__default.View(self);
    }
    public static Dafny.ISequence<byte> CommaSuffix(JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> c) {
      return JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>(c, JSON_mSpec_Compile.__default.StructuralView);
    }
    public static Dafny.ISequence<byte> Member(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.KV((self).dtor_t), JSON_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Item(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.Value((self).dtor_t), JSON_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> obj) {
      return JSON_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>(obj, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>, Dafny.ISequence<byte>>>>((_24_obj) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>, Dafny.ISequence<byte>>)((_25_d) => {
        return JSON_mSpec_Compile.__default.Member(_25_d);
      })))(obj));
    }
    public static Dafny.ISequence<byte> Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> arr) {
      return JSON_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>(arr, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>, Dafny.ISequence<byte>>>>((_26_arr) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>, Dafny.ISequence<byte>>)((_27_d) => {
        return JSON_mSpec_Compile.__default.Item(_27_d);
      })))(arr));
    }
    public static Dafny.ISequence<byte> Value(JSON_mGrammar_Compile._IValue self) {
      JSON_mGrammar_Compile._IValue _source5 = self;
      if (_source5.is_Null) {
        Views_mCore_Compile._IView__ _28___mcc_h0 = _source5.dtor_n;
        Views_mCore_Compile._IView__ _29_n = _28___mcc_h0;
        return JSON_mSpec_Compile.__default.View(_29_n);
      } else if (_source5.is_Bool) {
        Views_mCore_Compile._IView__ _30___mcc_h1 = _source5.dtor_b;
        Views_mCore_Compile._IView__ _31_b = _30___mcc_h1;
        return JSON_mSpec_Compile.__default.View(_31_b);
      } else if (_source5.is_String) {
        Views_mCore_Compile._IView__ _32___mcc_h2 = _source5.dtor_str;
        Views_mCore_Compile._IView__ _33_str = _32___mcc_h2;
        return JSON_mSpec_Compile.__default.String(_33_str);
      } else if (_source5.is_Number) {
        JSON_mGrammar_Compile._Ijnumber _34___mcc_h3 = _source5.dtor_num;
        JSON_mGrammar_Compile._Ijnumber _35_num = _34___mcc_h3;
        return JSON_mSpec_Compile.__default.Number(_35_num);
      } else if (_source5.is_Object) {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _36___mcc_h4 = _source5.dtor_obj;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _37_obj = _36___mcc_h4;
        return JSON_mSpec_Compile.__default.Object(_37_obj);
      } else {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _38___mcc_h5 = _source5.dtor_arr;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _39_arr = _38___mcc_h5;
        return JSON_mSpec_Compile.__default.Array(_39_arr);
      }
    }
    public static Dafny.ISequence<byte> JSON(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return JSON_mSpec_Compile.__default.Structural<JSON_mGrammar_Compile._IValue>(js, JSON_mSpec_Compile.__default.Value);
    }
  }
} // end of namespace JSON_mSpec_Compile
namespace JSON_mSpecProperties_Compile {

} // end of namespace JSON_mSpecProperties_Compile
namespace JSON_mZeroCopy_mSerializer_Compile {

  public interface _IError {
    bool is_OutOfMemory { get; }
    _IError DowncastClone();
  }
  public class Error : _IError {
    public Error() {
    }
    public _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mSerializer_Compile.Error;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mSerializer_Compile.Error.OutOfMemory";
      return s;
    }
    private static readonly _IError theDefault = create();
    public static _IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile._IError> _TYPE = new Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile._IError>(JSON_mZeroCopy_mSerializer_Compile.Error.Default());
    public static Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create() {
      return new Error();
    }
    public bool is_OutOfMemory { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IError> AllSingletonConstructors {
      get {
        yield return Error.create();
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> Serialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js)
    {
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> rbs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile._IError>.Default(new byte[0]);
      Views_mWriters_Compile._IWriter__ _40_writer;
      _40_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile._IOutcome<JSON_mZeroCopy_mSerializer_Compile._IError> _41_valueOrError0 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile._IError>.Default();
      _41_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile._IError>((_40_writer).Unsaturated_q, JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_41_valueOrError0).IsFailure()) {
        rbs = (_41_valueOrError0).PropagateFailure<byte[]>();
        return rbs;
      }
      byte[] _42_bs;
      byte[] _out0;
      _out0 = (_40_writer).ToArray();
      _42_bs = _out0;
      rbs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile._IError>.create_Success(_42_bs);
      return rbs;
      return rbs;
    }
    public static Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> SerializeTo(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] bs)
    {
      Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile._IError>.Default(0);
      Views_mWriters_Compile._IWriter__ _43_writer;
      _43_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile._IOutcome<JSON_mZeroCopy_mSerializer_Compile._IError> _44_valueOrError0 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile._IError>.Default();
      _44_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile._IError>((_43_writer).Unsaturated_q, JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_44_valueOrError0).IsFailure()) {
        len = (_44_valueOrError0).PropagateFailure<uint>();
        return len;
      }
      Wrappers_Compile._IOutcome<JSON_mZeroCopy_mSerializer_Compile._IError> _45_valueOrError1 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile._IError>.Default();
      _45_valueOrError1 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile._IError>((new BigInteger((_43_writer).dtor_length)) <= (new BigInteger((bs).Length)), JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_45_valueOrError1).IsFailure()) {
        len = (_45_valueOrError1).PropagateFailure<uint>();
        return len;
      }
      (_43_writer).Blit(bs);
      len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile._IError>.create_Success((_43_writer).dtor_length);
      return len;
      return len;
    }
    public static Views_mWriters_Compile._IWriter__ Text(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return JSON_mZeroCopy_mSerializer_Compile.__default.JSON(js, Views_mWriters_Compile.Writer__.Empty);
    }
    public static Views_mWriters_Compile._IWriter__ JSON(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, Views_mWriters_Compile._IWriter__ writer)
    {
      return (((writer).Append((js).dtor_before)).Then(Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__>>>((_46_js) => ((System.Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__>)((_47_wr) => {
        return JSON_mZeroCopy_mSerializer_Compile.__default.Value((_46_js).dtor_t, _47_wr);
      })))(js))).Append((js).dtor_after);
    }
    public static Views_mWriters_Compile._IWriter__ Value(JSON_mGrammar_Compile._IValue v, Views_mWriters_Compile._IWriter__ writer)
    {
      JSON_mGrammar_Compile._IValue _source6 = v;
      if (_source6.is_Null) {
        Views_mCore_Compile._IView__ _48___mcc_h0 = _source6.dtor_n;
        Views_mCore_Compile._IView__ _49_n = _48___mcc_h0;
        return (writer).Append(_49_n);
      } else if (_source6.is_Bool) {
        Views_mCore_Compile._IView__ _50___mcc_h1 = _source6.dtor_b;
        Views_mCore_Compile._IView__ _51_b = _50___mcc_h1;
        return (writer).Append(_51_b);
      } else if (_source6.is_String) {
        Views_mCore_Compile._IView__ _52___mcc_h2 = _source6.dtor_str;
        Views_mCore_Compile._IView__ _53_str = _52___mcc_h2;
        return JSON_mZeroCopy_mSerializer_Compile.__default.String(_53_str, writer);
      } else if (_source6.is_Number) {
        JSON_mGrammar_Compile._Ijnumber _54___mcc_h3 = _source6.dtor_num;
        JSON_mGrammar_Compile._Ijnumber _55_num = _54___mcc_h3;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Number(_55_num, writer);
      } else if (_source6.is_Object) {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _56___mcc_h4 = _source6.dtor_obj;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _57_obj = _56___mcc_h4;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Object(_57_obj, writer);
      } else {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _58___mcc_h5 = _source6.dtor_arr;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _59_arr = _58___mcc_h5;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Array(_59_arr, writer);
      }
    }
    public static Views_mWriters_Compile._IWriter__ String(Views_mCore_Compile._IView__ str, Views_mWriters_Compile._IWriter__ writer)
    {
      return (writer).Append(str);
    }
    public static Views_mWriters_Compile._IWriter__ Number(JSON_mGrammar_Compile._Ijnumber num, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _60_writer = ((writer).Append((num).dtor_minus)).Append((num).dtor_num);
      Views_mWriters_Compile._IWriter__ _61_writer = ((((num).dtor_frac).is_NonEmpty) ? (((_60_writer).Append((((num).dtor_frac).dtor_t).dtor_period)).Append((((num).dtor_frac).dtor_t).dtor_num)) : (_60_writer));
      Views_mWriters_Compile._IWriter__ _62_writer = ((((num).dtor_exp).is_NonEmpty) ? ((((_61_writer).Append((((num).dtor_exp).dtor_t).dtor_e)).Append((((num).dtor_exp).dtor_t).dtor_sign)).Append((((num).dtor_exp).dtor_t).dtor_num)) : (_61_writer));
      return _62_writer;
    }
    public static Views_mWriters_Compile._IWriter__ StructuralView(JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__> st, Views_mWriters_Compile._IWriter__ writer)
    {
      return (((writer).Append((st).dtor_before)).Append((st).dtor_t)).Append((st).dtor_after);
    }
    public static Views_mWriters_Compile._IWriter__ Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> obj, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _63_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_l, writer);
      Views_mWriters_Compile._IWriter__ _64_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Members(obj, _63_writer);
      Views_mWriters_Compile._IWriter__ _65_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_r, _64_writer);
      return _65_writer;
    }
    public static Views_mWriters_Compile._IWriter__ Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> arr, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _66_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_l, writer);
      Views_mWriters_Compile._IWriter__ _67_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Items(arr, _66_writer);
      Views_mWriters_Compile._IWriter__ _68_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_r, _67_writer);
      return _68_writer;
    }
    public static Views_mWriters_Compile._IWriter__ Members(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> obj, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      Views_mWriters_Compile._IWriter__ _out1;
      _out1 = JSON_mZeroCopy_mSerializer_Compile.__default.MembersImpl(obj, writer);
      wr = _out1;
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ Items(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> arr, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      Views_mWriters_Compile._IWriter__ _out2;
      _out2 = JSON_mZeroCopy_mSerializer_Compile.__default.ItemsImpl(arr, writer);
      wr = _out2;
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ MembersImpl(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> obj, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>> _69_members;
      _69_members = (obj).dtor_data;
      BigInteger _hi1 = new BigInteger((_69_members).Count);
      for (BigInteger _70_i = BigInteger.Zero; _70_i < _hi1; _70_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Member((_69_members).Select(_70_i), wr);
      }
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ ItemsImpl(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> arr, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>> _71_items;
      _71_items = (arr).dtor_data;
      BigInteger _hi2 = new BigInteger((_71_items).Count);
      for (BigInteger _72_i = BigInteger.Zero; _72_i < _hi2; _72_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Item((_71_items).Select(_72_i), wr);
      }
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ Member(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__> m, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _73_writer = (writer).Append(((m).dtor_t).dtor_k);
      Views_mWriters_Compile._IWriter__ _74_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_t).dtor_colon, _73_writer);
      Views_mWriters_Compile._IWriter__ _75_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Value(((m).dtor_t).dtor_v, _74_writer);
      if (((m).dtor_suffix).is_Empty) {
        return _75_writer;
      } else {
        return JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _75_writer);
      }
    }
    public static Views_mWriters_Compile._IWriter__ Item(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__> m, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _76_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Value((m).dtor_t, writer);
      if (((m).dtor_suffix).is_Empty) {
        return _76_writer;
      } else {
        return JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _76_writer);
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mSerializer_Compile
namespace Lexers_mCore_Compile {

  public interface _ILexerState<out T, out R> {
    bool is_Accept { get; }
    bool is_Reject { get; }
    bool is_Partial { get; }
    R dtor_err { get; }
    T dtor_st { get; }
    _ILexerState<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public abstract class LexerState<T, R> : _ILexerState<T, R> {
    public LexerState() { }
    public static _ILexerState<T, R> Default() {
      return create_Accept();
    }
    public static Dafny.TypeDescriptor<Lexers_mCore_Compile._ILexerState<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Lexers_mCore_Compile._ILexerState<T, R>>(Lexers_mCore_Compile.LexerState<T, R>.Default());
    }
    public static _ILexerState<T, R> create_Accept() {
      return new LexerState_Accept<T, R>();
    }
    public static _ILexerState<T, R> create_Reject(R err) {
      return new LexerState_Reject<T, R>(err);
    }
    public static _ILexerState<T, R> create_Partial(T st) {
      return new LexerState_Partial<T, R>(st);
    }
    public bool is_Accept { get { return this is LexerState_Accept<T, R>; } }
    public bool is_Reject { get { return this is LexerState_Reject<T, R>; } }
    public bool is_Partial { get { return this is LexerState_Partial<T, R>; } }
    public R dtor_err {
      get {
        var d = this;
        return ((LexerState_Reject<T, R>)d).err;
      }
    }
    public T dtor_st {
      get {
        var d = this;
        return ((LexerState_Partial<T, R>)d).st;
      }
    }
    public abstract _ILexerState<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class LexerState_Accept<T, R> : LexerState<T, R> {
    public LexerState_Accept() {
    }
    public override _ILexerState<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerState<__T, __R> dt) { return dt; }
      return new LexerState_Accept<__T, __R>();
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mCore_Compile.LexerState_Accept<T, R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mCore_Compile.LexerState.Accept";
      return s;
    }
  }
  public class LexerState_Reject<T, R> : LexerState<T, R> {
    public readonly R err;
    public LexerState_Reject(R err) {
      this.err = err;
    }
    public override _ILexerState<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerState<__T, __R> dt) { return dt; }
      return new LexerState_Reject<__T, __R>(converter1(err));
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mCore_Compile.LexerState_Reject<T, R>;
      return oth != null && object.Equals(this.err, oth.err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mCore_Compile.LexerState.Reject";
      s += "(";
      s += Dafny.Helpers.ToString(this.err);
      s += ")";
      return s;
    }
  }
  public class LexerState_Partial<T, R> : LexerState<T, R> {
    public readonly T st;
    public LexerState_Partial(T st) {
      this.st = st;
    }
    public override _ILexerState<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerState<__T, __R> dt) { return dt; }
      return new LexerState_Partial<__T, __R>(converter0(st));
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mCore_Compile.LexerState_Partial<T, R>;
      return oth != null && object.Equals(this.st, oth.st);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.st));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mCore_Compile.LexerState.Partial";
      s += "(";
      s += Dafny.Helpers.ToString(this.st);
      s += ")";
      return s;
    }
  }

} // end of namespace Lexers_mCore_Compile
namespace Lexers_mStrings_Compile {

  public interface _IStringLexerState {
    bool is_Start { get; }
    bool is_Body { get; }
    bool is_End { get; }
    bool dtor_escaped { get; }
    _IStringLexerState DowncastClone();
  }
  public abstract class StringLexerState : _IStringLexerState {
    public StringLexerState() { }
    private static readonly _IStringLexerState theDefault = create_Start();
    public static _IStringLexerState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Lexers_mStrings_Compile._IStringLexerState> _TYPE = new Dafny.TypeDescriptor<Lexers_mStrings_Compile._IStringLexerState>(Lexers_mStrings_Compile.StringLexerState.Default());
    public static Dafny.TypeDescriptor<Lexers_mStrings_Compile._IStringLexerState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStringLexerState create_Start() {
      return new StringLexerState_Start();
    }
    public static _IStringLexerState create_Body(bool escaped) {
      return new StringLexerState_Body(escaped);
    }
    public static _IStringLexerState create_End() {
      return new StringLexerState_End();
    }
    public bool is_Start { get { return this is StringLexerState_Start; } }
    public bool is_Body { get { return this is StringLexerState_Body; } }
    public bool is_End { get { return this is StringLexerState_End; } }
    public bool dtor_escaped {
      get {
        var d = this;
        return ((StringLexerState_Body)d).escaped;
      }
    }
    public abstract _IStringLexerState DowncastClone();
  }
  public class StringLexerState_Start : StringLexerState {
    public StringLexerState_Start() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_Start();
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mStrings_Compile.StringLexerState_Start;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mStrings_Compile.StringLexerState.Start";
      return s;
    }
  }
  public class StringLexerState_Body : StringLexerState {
    public readonly bool escaped;
    public StringLexerState_Body(bool escaped) {
      this.escaped = escaped;
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_Body(escaped);
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mStrings_Compile.StringLexerState_Body;
      return oth != null && this.escaped == oth.escaped;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.escaped));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mStrings_Compile.StringLexerState.Body";
      s += "(";
      s += Dafny.Helpers.ToString(this.escaped);
      s += ")";
      return s;
    }
  }
  public class StringLexerState_End : StringLexerState {
    public StringLexerState_End() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
      return new StringLexerState_End();
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mStrings_Compile.StringLexerState_End;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mStrings_Compile.StringLexerState.End";
      return s;
    }
  }

  public partial class __default {
    public static Lexers_mCore_Compile._ILexerState<bool, __R> StringBody<__R>(Lexers_mCore_Compile._ILexerState<bool, __R> st, short @byte)
    {
      Lexers_mCore_Compile._ILexerState<bool, __R> _source7 = st;
      if (_source7.is_Accept) {
        return st;
      } else if (_source7.is_Reject) {
        __R _77___mcc_h0 = _source7.dtor_err;
        return st;
      } else {
        bool _78___mcc_h2 = _source7.dtor_st;
        bool _79_escaped = _78___mcc_h2;
        if ((@byte) == ((short)('\\'))) {
          return Lexers_mCore_Compile.LexerState<bool, __R>.create_Partial(!(_79_escaped));
        } else if (((@byte) == ((short)('\"'))) && (!(_79_escaped))) {
          return Lexers_mCore_Compile.LexerState<bool, __R>.create_Accept();
        } else {
          return Lexers_mCore_Compile.LexerState<bool, __R>.create_Partial(false);
        }
      }
    }
    public static Lexers_mCore_Compile._ILexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>> String(Lexers_mCore_Compile._ILexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>> st, short @byte)
    {
      Lexers_mCore_Compile._ILexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>> _source8 = st;
      if (_source8.is_Accept) {
        return st;
      } else if (_source8.is_Reject) {
        Dafny.ISequence<char> _80___mcc_h0 = _source8.dtor_err;
        return st;
      } else {
        Lexers_mStrings_Compile._IStringLexerState _81___mcc_h2 = _source8.dtor_st;
        Lexers_mStrings_Compile._IStringLexerState _source9 = _81___mcc_h2;
        if (_source9.is_Start) {
          if ((@byte) == ((short)('\"'))) {
            return Lexers_mCore_Compile.LexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(false));
          } else {
            return Lexers_mCore_Compile.LexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Reject(Dafny.Sequence<char>.FromString("String must start with double quote"));
          }
        } else if (_source9.is_Body) {
          bool _82___mcc_h4 = _source9.dtor_escaped;
          bool _83_escaped = _82___mcc_h4;
          if ((@byte) == ((short)('\\'))) {
            return Lexers_mCore_Compile.LexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(!(_83_escaped)));
          } else if (((@byte) == ((short)('\"'))) && (!(_83_escaped))) {
            return Lexers_mCore_Compile.LexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_End());
          } else {
            return Lexers_mCore_Compile.LexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(false));
          }
        } else {
          return Lexers_mCore_Compile.LexerState<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Accept();
        }
      }
    }
    public static bool StringBodyLexerStart { get {
      return false;
    } }
    public static Lexers_mStrings_Compile._IStringLexerState StringLexerStart { get {
      return Lexers_mStrings_Compile.StringLexerState.create_Start();
    } }
  }
} // end of namespace Lexers_mStrings_Compile
namespace Lexers_Compile {

} // end of namespace Lexers_Compile
namespace Cursors_Compile {

  public interface _ISplit<out T> {
    bool is_SP { get; }
    T dtor_t { get; }
    Cursors_Compile._ICursor__ dtor_cs { get; }
    _ISplit<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Split<T> : _ISplit<T> {
    public readonly T t;
    public readonly Cursors_Compile._ICursor__ cs;
    public Split(T t, Cursors_Compile._ICursor__ cs) {
      this.t = t;
      this.cs = cs;
    }
    public _ISplit<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _ISplit<__T> dt) { return dt; }
      return new Split<__T>(converter0(t), cs);
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.Split<T>;
      return oth != null && object.Equals(this.t, oth.t) && object.Equals(this.cs, oth.cs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.Split.SP";
      s += "(";
      s += Dafny.Helpers.ToString(this.t);
      s += ", ";
      s += Dafny.Helpers.ToString(this.cs);
      s += ")";
      return s;
    }
    public static _ISplit<T> Default(T _default_T) {
      return create(_default_T, Cursors_Compile.FreshCursor.Default());
    }
    public static Dafny.TypeDescriptor<Cursors_Compile._ISplit<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Cursors_Compile._ISplit<T>>(Cursors_Compile.Split<T>.Default(_td_T.Default()));
    }
    public static _ISplit<T> create(T t, Cursors_Compile._ICursor__ cs) {
      return new Split<T>(t, cs);
    }
    public bool is_SP { get { return true; } }
    public T dtor_t {
      get {
        return this.t;
      }
    }
    public Cursors_Compile._ICursor__ dtor_cs {
      get {
        return this.cs;
      }
    }
  }

  public partial class Cursor {
    private static readonly Cursors_Compile._ICursor__ Witness = Cursors_Compile.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static Cursors_Compile._ICursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Cursors_Compile._ICursor__> _TYPE = new Dafny.TypeDescriptor<Cursors_Compile._ICursor__>(Cursors_Compile.Cursor.Default());
    public static Dafny.TypeDescriptor<Cursors_Compile._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class FreshCursor {
    private static readonly Cursors_Compile._ICursor__ Witness = Cursors_Compile.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static Cursors_Compile._ICursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Cursors_Compile._ICursor__> _TYPE = new Dafny.TypeDescriptor<Cursors_Compile._ICursor__>(Cursors_Compile.FreshCursor.Default());
    public static Dafny.TypeDescriptor<Cursors_Compile._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _ICursorError<out R> {
    bool is_EOF { get; }
    bool is_ExpectingByte { get; }
    bool is_ExpectingAnyByte { get; }
    bool is_OtherError { get; }
    byte dtor_expected { get; }
    short dtor_b { get; }
    Dafny.ISequence<byte> dtor_expected__sq { get; }
    R dtor_err { get; }
    _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
  }
  public abstract class CursorError<R> : _ICursorError<R> {
    public CursorError() { }
    public static _ICursorError<R> Default() {
      return create_EOF();
    }
    public static Dafny.TypeDescriptor<Cursors_Compile._ICursorError<R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Cursors_Compile._ICursorError<R>>(Cursors_Compile.CursorError<R>.Default());
    }
    public static _ICursorError<R> create_EOF() {
      return new CursorError_EOF<R>();
    }
    public static _ICursorError<R> create_ExpectingByte(byte expected, short b) {
      return new CursorError_ExpectingByte<R>(expected, b);
    }
    public static _ICursorError<R> create_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      return new CursorError_ExpectingAnyByte<R>(expected__sq, b);
    }
    public static _ICursorError<R> create_OtherError(R err) {
      return new CursorError_OtherError<R>(err);
    }
    public bool is_EOF { get { return this is CursorError_EOF<R>; } }
    public bool is_ExpectingByte { get { return this is CursorError_ExpectingByte<R>; } }
    public bool is_ExpectingAnyByte { get { return this is CursorError_ExpectingAnyByte<R>; } }
    public bool is_OtherError { get { return this is CursorError_OtherError<R>; } }
    public byte dtor_expected {
      get {
        var d = this;
        return ((CursorError_ExpectingByte<R>)d).expected;
      }
    }
    public short dtor_b {
      get {
        var d = this;
        if (d is CursorError_ExpectingByte<R>) { return ((CursorError_ExpectingByte<R>)d).b; }
        return ((CursorError_ExpectingAnyByte<R>)d).b;
      }
    }
    public Dafny.ISequence<byte> dtor_expected__sq {
      get {
        var d = this;
        return ((CursorError_ExpectingAnyByte<R>)d).expected__sq;
      }
    }
    public R dtor_err {
      get {
        var d = this;
        return ((CursorError_OtherError<R>)d).err;
      }
    }
    public abstract _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
    public static Dafny.ISequence<char> _ToString(Cursors_Compile._ICursorError<R> _this, Func<R, Dafny.ISequence<char>> pr) {
      Cursors_Compile._ICursorError<R> _source10 = _this;
      if (_source10.is_EOF) {
        return Dafny.Sequence<char>.FromString("Reached EOF");
      } else if (_source10.is_ExpectingByte) {
        byte _84___mcc_h0 = _source10.dtor_expected;
        short _85___mcc_h1 = _source10.dtor_b;
        short _86_b = _85___mcc_h1;
        byte _87_b0 = _84___mcc_h0;
        Dafny.ISequence<char> _88_c = (((_86_b) > (0)) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_86_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting '"), Dafny.Sequence<char>.FromElements((char)(_87_b0))), Dafny.Sequence<char>.FromString("', read ")), _88_c);
      } else if (_source10.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _89___mcc_h2 = _source10.dtor_expected__sq;
        short _90___mcc_h3 = _source10.dtor_b;
        short _91_b = _90___mcc_h3;
        Dafny.ISequence<byte> _92_bs0 = _89___mcc_h2;
        Dafny.ISequence<char> _93_c = (((_91_b) > (0)) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_91_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        Dafny.ISequence<char> _94_c0s = ((System.Func<Dafny.ISequence<char>>) (() => {
          BigInteger dim0 = new BigInteger((_92_bs0).Count);
          var arr0 = new char[Dafny.Helpers.ToIntChecked(dim0,"C# array size must not be larger than max 32-bit int")];
          for (int i0 = 0; i0 < dim0; i0++) {
            var _95_idx = (BigInteger) i0;
            arr0[(int)(_95_idx)] = (char)((_92_bs0).Select(_95_idx));
          }
          return Dafny.Sequence<char>.FromArray(arr0);
        }))();
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting one of '"), _94_c0s), Dafny.Sequence<char>.FromString("', read ")), _93_c);
      } else {
        R _96___mcc_h4 = _source10.dtor_err;
        R _97_err = _96___mcc_h4;
        return Dafny.Helpers.Id<Func<R, Dafny.ISequence<char>>>(pr)(_97_err);
      }
    }
  }
  public class CursorError_EOF<R> : CursorError<R> {
    public CursorError_EOF() {
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_EOF<__R>();
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_EOF<R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.EOF";
      return s;
    }
  }
  public class CursorError_ExpectingByte<R> : CursorError<R> {
    public readonly byte expected;
    public readonly short b;
    public CursorError_ExpectingByte(byte expected, short b) {
      this.expected = expected;
      this.b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingByte<__R>(expected, b);
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_ExpectingByte<R>;
      return oth != null && this.expected == oth.expected && this.b == oth.b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expected));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.ExpectingByte";
      s += "(";
      s += Dafny.Helpers.ToString(this.expected);
      s += ", ";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public class CursorError_ExpectingAnyByte<R> : CursorError<R> {
    public readonly Dafny.ISequence<byte> expected__sq;
    public readonly short b;
    public CursorError_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      this.expected__sq = expected__sq;
      this.b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingAnyByte<__R>(expected__sq, b);
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_ExpectingAnyByte<R>;
      return oth != null && object.Equals(this.expected__sq, oth.expected__sq) && this.b == oth.b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expected__sq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.ExpectingAnyByte";
      s += "(";
      s += Dafny.Helpers.ToString(this.expected__sq);
      s += ", ";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public class CursorError_OtherError<R> : CursorError<R> {
    public readonly R err;
    public CursorError_OtherError(R err) {
      this.err = err;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
      return new CursorError_OtherError<__R>(converter0(err));
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_OtherError<R>;
      return oth != null && object.Equals(this.err, oth.err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.OtherError";
      s += "(";
      s += Dafny.Helpers.ToString(this.err);
      s += ")";
      return s;
    }
  }

  public interface _ICursor__ {
    bool is_Cursor { get; }
    Dafny.ISequence<byte> dtor_s { get; }
    uint dtor_beg { get; }
    uint dtor_point { get; }
    uint dtor_end { get; }
    _ICursor__ DowncastClone();
    bool BOF_q { get; }
    bool EOF_q { get; }
    Dafny.ISequence<byte> Bytes();
    Views_mCore_Compile._IView__ Prefix();
    Cursors_Compile._ICursor__ Suffix();
    Cursors_Compile._ISplit<Views_mCore_Compile._IView__> Split();
    uint PrefixLength();
    uint SuffixLength();
    uint Length();
    byte At(uint idx);
    byte SuffixAt(uint idx);
    short Peek();
    bool LookingAt(char c);
    Cursors_Compile._ICursor__ Skip(uint n);
    Cursors_Compile._ICursor__ Unskip(uint n);
    Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> Get<__R>(__R err);
    Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> AssertByte<__R>(byte b);
    Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset);
    Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> AssertChar<__R>(char c0);
    Cursors_Compile._ICursor__ SkipByte();
    Cursors_Compile._ICursor__ SkipIf(Func<byte, bool> p);
    Cursors_Compile._ICursor__ SkipWhile(Func<byte, bool> p);
    Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> SkipWhileLexer<__A, __R>(Func<Lexers_mCore_Compile._ILexerState<__A, __R>, short, Lexers_mCore_Compile._ILexerState<__A, __R>> step, Lexers_mCore_Compile._ILexerState<__A, __R> st);
  }
  public class Cursor__ : _ICursor__ {
    public readonly Dafny.ISequence<byte> s;
    public readonly uint beg;
    public readonly uint point;
    public readonly uint end;
    public Cursor__(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      this.s = s;
      this.beg = beg;
      this.point = point;
      this.end = end;
    }
    public _ICursor__ DowncastClone() {
      if (this is _ICursor__ dt) { return dt; }
      return new Cursor__(s, beg, point, end);
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.Cursor__;
      return oth != null && object.Equals(this.s, oth.s) && this.beg == oth.beg && this.point == oth.point && this.end == oth.end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.point));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Cursors_Compile.Cursor_.Cursor";
      ss += "(";
      ss += Dafny.Helpers.ToString(this.s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.point);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.end);
      ss += ")";
      return ss;
    }
    private static readonly _ICursor__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0, 0);
    public static _ICursor__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Cursors_Compile._ICursor__> _TYPE = new Dafny.TypeDescriptor<Cursors_Compile._ICursor__>(Cursors_Compile.Cursor__.Default());
    public static Dafny.TypeDescriptor<Cursors_Compile._ICursor__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ICursor__ create(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      return new Cursor__(s, beg, point, end);
    }
    public bool is_Cursor { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this.s;
      }
    }
    public uint dtor_beg {
      get {
        return this.beg;
      }
    }
    public uint dtor_point {
      get {
        return this.point;
      }
    }
    public uint dtor_end {
      get {
        return this.end;
      }
    }
    public static Cursors_Compile._ICursor__ OfView(Views_mCore_Compile._IView__ v) {
      return Cursors_Compile.Cursor__.create((v).dtor_s, (v).dtor_beg, (v).dtor_beg, (v).dtor_end);
    }
    public static Cursors_Compile._ICursor__ OfBytes(Dafny.ISequence<byte> bs) {
      return Cursors_Compile.Cursor__.create(bs, 0U, (uint)(bs).LongCount, (uint)(bs).LongCount);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public Views_mCore_Compile._IView__ Prefix() {
      return Views_mCore_Compile.View__.create((this).dtor_s, (this).dtor_beg, (this).dtor_point);
    }
    public Cursors_Compile._ICursor__ Suffix() {
      Cursors_Compile._ICursor__ _98_dt__update__tmp_h0 = this;
      uint _99_dt__update_hbeg_h0 = (this).dtor_point;
      return Cursors_Compile.Cursor__.create((_98_dt__update__tmp_h0).dtor_s, _99_dt__update_hbeg_h0, (_98_dt__update__tmp_h0).dtor_point, (_98_dt__update__tmp_h0).dtor_end);
    }
    public Cursors_Compile._ISplit<Views_mCore_Compile._IView__> Split() {
      return Cursors_Compile.Split<Views_mCore_Compile._IView__>.create((this).Prefix(), (this).Suffix());
    }
    public uint PrefixLength() {
      return ((this).dtor_point) - ((this).dtor_beg);
    }
    public uint SuffixLength() {
      return ((this).dtor_end) - ((this).dtor_point);
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public byte SuffixAt(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_point) + (idx));
    }
    public short Peek() {
      if ((this).EOF_q) {
        return -1;
      } else {
        return (short)((this).SuffixAt(0U));
      }
    }
    public bool LookingAt(char c) {
      return ((this).Peek()) == ((short)(c));
    }
    public Cursors_Compile._ICursor__ Skip(uint n) {
      Cursors_Compile._ICursor__ _100_dt__update__tmp_h0 = this;
      uint _101_dt__update_hpoint_h0 = ((this).dtor_point) + (n);
      return Cursors_Compile.Cursor__.create((_100_dt__update__tmp_h0).dtor_s, (_100_dt__update__tmp_h0).dtor_beg, _101_dt__update_hpoint_h0, (_100_dt__update__tmp_h0).dtor_end);
    }
    public Cursors_Compile._ICursor__ Unskip(uint n) {
      Cursors_Compile._ICursor__ _102_dt__update__tmp_h0 = this;
      uint _103_dt__update_hpoint_h0 = ((this).dtor_point) - (n);
      return Cursors_Compile.Cursor__.create((_102_dt__update__tmp_h0).dtor_s, (_102_dt__update__tmp_h0).dtor_beg, _103_dt__update_hpoint_h0, (_102_dt__update__tmp_h0).dtor_end);
    }
    public Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> Get<__R>(__R err) {
      if ((this).EOF_q) {
        return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_OtherError(err));
      } else {
        return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Success((this).Skip(1U));
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> AssertByte<__R>(byte b) {
      short _104_nxt = (this).Peek();
      if ((_104_nxt) == ((short)(b))) {
        return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Success((this).Skip(1U));
      } else {
        return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_ExpectingByte(b, _104_nxt));
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset)
    {
      _ICursor__ _this = this;
    TAIL_CALL_START: ;
      if ((offset) == ((uint)(bs).LongCount)) {
        return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Success(_this);
      } else {
        Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> _105_valueOrError0 = (_this).AssertByte<__R>((byte)((bs).Select(offset)));
        if ((_105_valueOrError0).IsFailure()) {
          return (_105_valueOrError0).PropagateFailure<Cursors_Compile._ICursor__>();
        } else {
          Cursors_Compile._ICursor__ _106_ps = (_105_valueOrError0).Extract();
          var _in8 = _106_ps;
          Dafny.ISequence<byte> _in9 = bs;
          uint _in10 = (offset) + (1U);
          _this = _in8;
          bs = _in9;
          offset = _in10;
          goto TAIL_CALL_START;
        }
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> AssertChar<__R>(char c0) {
      return (this).AssertByte<__R>((byte)(c0));
    }
    public Cursors_Compile._ICursor__ SkipByte() {
      if ((this).EOF_q) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public Cursors_Compile._ICursor__ SkipIf(Func<byte, bool> p) {
      if (((this).EOF_q) || (!(Dafny.Helpers.Id<Func<byte, bool>>(p)((this).SuffixAt(0U))))) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public Cursors_Compile._ICursor__ SkipWhile(Func<byte, bool> p) {
      _ICursor__ _this = this;
    TAIL_CALL_START: ;
      if (((_this).EOF_q) || (!(Dafny.Helpers.Id<Func<byte, bool>>(p)((_this).SuffixAt(0U))))) {
        return _this;
      } else {
        var _in11 = (_this).Skip(1U);
        Func<byte, bool> _in12 = p;
        _this = _in11;
        p = _in12;
        goto TAIL_CALL_START;
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>> SkipWhileLexer<__A, __R>(Func<Lexers_mCore_Compile._ILexerState<__A, __R>, short, Lexers_mCore_Compile._ILexerState<__A, __R>> step, Lexers_mCore_Compile._ILexerState<__A, __R> st)
    {
      _ICursor__ _this = this;
    TAIL_CALL_START: ;
      Lexers_mCore_Compile._ILexerState<__A, __R> _source11 = Dafny.Helpers.Id<Func<Lexers_mCore_Compile._ILexerState<__A, __R>, short, Lexers_mCore_Compile._ILexerState<__A, __R>>>(step)(st, (_this).Peek());
      if (_source11.is_Accept) {
        return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Success(_this);
      } else if (_source11.is_Reject) {
        __R _107___mcc_h0 = _source11.dtor_err;
        __R _108_err = _107___mcc_h0;
        return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_OtherError(_108_err));
      } else {
        __A _109___mcc_h2 = _source11.dtor_st;
        Lexers_mCore_Compile._ILexerState<__A, __R> _110_partial = Dafny.Helpers.Id<Func<Lexers_mCore_Compile._ILexerState<__A, __R>, short, Lexers_mCore_Compile._ILexerState<__A, __R>>>(step)(st, (_this).Peek());
        if ((_this).EOF_q) {
          return Wrappers_Compile.Result<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_EOF());
        } else {
          var _in13 = (_this).Skip(1U);
          Func<Lexers_mCore_Compile._ILexerState<__A, __R>, short, Lexers_mCore_Compile._ILexerState<__A, __R>> _in14 = step;
          Lexers_mCore_Compile._ILexerState<__A, __R> _in15 = _110_partial;
          _this = _in13;
          step = _in14;
          st = _in15;
          goto TAIL_CALL_START;
        }
      }
    }
    public bool BOF_q { get {
      return ((this).dtor_point) == ((this).dtor_beg);
    } }
    public bool EOF_q { get {
      return ((this).dtor_point) == ((this).dtor_end);
    } }
  }

} // end of namespace Cursors_Compile
namespace Parsers_Compile {

  public partial class Parser<T, R> {
    public static Parsers_Compile._IParser__<T, R> Default() {
      return Parsers_Compile.__default.ParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>>(Parsers_Compile.Parser<T, R>.Default());
    }
  }

  public interface _IParser__<T, out R> {
    bool is_Parser { get; }
    Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> dtor_fn { get; }
    _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class Parser__<T, R> : _IParser__<T, R> {
    public readonly Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> fn;
    public Parser__(Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> fn) {
      this.fn = fn;
    }
    public _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IParser__<__T, __R> dt) { return dt; }
      return new Parser__<__T, __R>((fn).DowncastClone<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>, Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>>(Dafny.Helpers.Id<Cursors_Compile._ICursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>, Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as Parsers_Compile.Parser__<T, R>;
      return oth != null && object.Equals(this.fn, oth.fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Parsers_Compile.Parser_.Parser";
      s += "(";
      s += Dafny.Helpers.ToString(this.fn);
      s += ")";
      return s;
    }
    public static _IParser__<T, R> Default(T _default_T) {
      return create(((Cursors_Compile._ICursor__ x0) => Wrappers_Compile.Result<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>.Default(Cursors_Compile.Split<T>.Default(_default_T))));
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>>(Parsers_Compile.Parser__<T, R>.Default(_td_T.Default()));
    }
    public static _IParser__<T, R> create(Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> fn) {
      return new Parser__<T, R>(fn);
    }
    public bool is_Parser { get { return true; } }
    public Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> dtor_fn {
      get {
        return this.fn;
      }
    }
  }

  public interface _ISubParser__<T, out R> {
    bool is_SubParser { get; }
    Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> dtor_fn { get; }
    _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class SubParser__<T, R> : _ISubParser__<T, R> {
    public readonly Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> fn;
    public SubParser__(Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> fn) {
      this.fn = fn;
    }
    public _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ISubParser__<__T, __R> dt) { return dt; }
      return new SubParser__<__T, __R>((fn).DowncastClone<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>, Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>>(Dafny.Helpers.Id<Cursors_Compile._ICursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>, Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as Parsers_Compile.SubParser__<T, R>;
      return oth != null && object.Equals(this.fn, oth.fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Parsers_Compile.SubParser_.SubParser";
      s += "(";
      s += Dafny.Helpers.ToString(this.fn);
      s += ")";
      return s;
    }
    public static _ISubParser__<T, R> Default() {
      return create(((Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>>)null));
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>>(Parsers_Compile.SubParser__<T, R>.Default());
    }
    public static _ISubParser__<T, R> create(Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> fn) {
      return new SubParser__<T, R>(fn);
    }
    public bool is_SubParser { get { return true; } }
    public Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<T>, Cursors_Compile._ICursorError<R>>> dtor_fn {
      get {
        return this.fn;
      }
    }
  }

  public partial class SubParser<T, R> {
    public static Parsers_Compile._ISubParser__<T, R> Default() {
      return Parsers_Compile.__default.SubParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>>(Parsers_Compile.SubParser<T, R>.Default());
    }
  }

  public partial class __default {
    public static Parsers_Compile._IParser__<__T, __R> ParserWitness<__T, __R>() {
      return Parsers_Compile.Parser__<__T, __R>.create(((System.Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>>)((_111___v0) => {
  return Wrappers_Compile.Result<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_EOF());
})));
    }
    public static Parsers_Compile._ISubParser__<__T, __R> SubParserWitness<__T, __R>() {
      return Parsers_Compile.SubParser__<__T, __R>.create(((System.Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>>)((_112_cs) => {
  return Wrappers_Compile.Result<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_EOF());
})));
    }
  }
} // end of namespace Parsers_Compile
namespace JSON_mZeroCopy_mDeserializer_mCore_Compile {

  public interface _IJSONError {
    bool is_UnterminatedSequence { get; }
    bool is_EmptyNumber { get; }
    bool is_ExpectingEOF { get; }
    bool is_IntOverflow { get; }
    _IJSONError DowncastClone();
    Dafny.ISequence<char> _ToString();
  }
  public abstract class JSONError : _IJSONError {
    public JSONError() { }
    private static readonly _IJSONError theDefault = create_UnterminatedSequence();
    public static _IJSONError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _TYPE = new Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.Default());
    public static Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IJSONError create_UnterminatedSequence() {
      return new JSONError_UnterminatedSequence();
    }
    public static _IJSONError create_EmptyNumber() {
      return new JSONError_EmptyNumber();
    }
    public static _IJSONError create_ExpectingEOF() {
      return new JSONError_ExpectingEOF();
    }
    public static _IJSONError create_IntOverflow() {
      return new JSONError_IntOverflow();
    }
    public bool is_UnterminatedSequence { get { return this is JSONError_UnterminatedSequence; } }
    public bool is_EmptyNumber { get { return this is JSONError_EmptyNumber; } }
    public bool is_ExpectingEOF { get { return this is JSONError_ExpectingEOF; } }
    public bool is_IntOverflow { get { return this is JSONError_IntOverflow; } }
    public static System.Collections.Generic.IEnumerable<_IJSONError> AllSingletonConstructors {
      get {
        yield return JSONError.create_UnterminatedSequence();
        yield return JSONError.create_EmptyNumber();
        yield return JSONError.create_ExpectingEOF();
        yield return JSONError.create_IntOverflow();
      }
    }
    public abstract _IJSONError DowncastClone();
    public Dafny.ISequence<char> _ToString() {
      JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError _source12 = this;
      if (_source12.is_UnterminatedSequence) {
        return Dafny.Sequence<char>.FromString("Unterminated sequence");
      } else if (_source12.is_EmptyNumber) {
        return Dafny.Sequence<char>.FromString("Number must contain at least one digit");
      } else if (_source12.is_ExpectingEOF) {
        return Dafny.Sequence<char>.FromString("Expecting EOF");
      } else {
        return Dafny.Sequence<char>.FromString("Input length does not fit in a 32-bit counter");
      }
    }
  }
  public class JSONError_UnterminatedSequence : JSONError {
    public JSONError_UnterminatedSequence() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
      return new JSONError_UnterminatedSequence();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_UnterminatedSequence;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.UnterminatedSequence";
      return s;
    }
  }
  public class JSONError_EmptyNumber : JSONError {
    public JSONError_EmptyNumber() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
      return new JSONError_EmptyNumber();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_EmptyNumber;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.EmptyNumber";
      return s;
    }
  }
  public class JSONError_ExpectingEOF : JSONError {
    public JSONError_ExpectingEOF() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
      return new JSONError_ExpectingEOF();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_ExpectingEOF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.ExpectingEOF";
      return s;
    }
  }
  public class JSONError_IntOverflow : JSONError {
    public JSONError_IntOverflow() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
      return new JSONError_IntOverflow();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_IntOverflow;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.IntOverflow";
      return s;
    }
  }

  public partial class jopt {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mCore_Compile.jopt.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ValueParser {
    private static readonly Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _TYPE = new Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>(Parsers_Compile.SubParser<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.Default());
    public static Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Get(Cursors_Compile._ICursor__ cs, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError err)
    {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _113_valueOrError0 = (cs).Get<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(err);
      if ((_113_valueOrError0).IsFailure()) {
        return (_113_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _114_cs = (_113_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_114_cs).Split());
      }
    }
    public static Cursors_Compile._ISplit<Views_mCore_Compile._IView__> WS(Cursors_Compile._ICursor__ cs) {
      return ((cs).SkipWhile(JSON_mGrammar_Compile.__default.Blank_q)).Split();
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<__T>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Structural<__T>(Cursors_Compile._ICursor__ cs, Parsers_Compile._IParser__<__T, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> parser)
    {
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      Views_mCore_Compile._IView__ _115_before = _let_tmp_rhs0.dtor_t;
      Cursors_Compile._ICursor__ _116_cs = _let_tmp_rhs0.dtor_cs;
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _117_valueOrError0 = Dafny.Helpers.Id<Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<__T>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>((parser).dtor_fn)(_116_cs);
      if ((_117_valueOrError0).IsFailure()) {
        return (_117_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<__T>>>();
      } else {
        Cursors_Compile._ISplit<__T> _let_tmp_rhs1 = (_117_valueOrError0).Extract();
        __T _118_val = _let_tmp_rhs1.dtor_t;
        Cursors_Compile._ICursor__ _119_cs = _let_tmp_rhs1.dtor_cs;
        Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs2 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_119_cs);
        Views_mCore_Compile._IView__ _120_after = _let_tmp_rhs2.dtor_t;
        Cursors_Compile._ICursor__ _121_cs = _let_tmp_rhs2.dtor_cs;
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<__T>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<__T>>.create(JSON_mGrammar_Compile.Structural<__T>.create(_115_before, _118_val, _120_after), _121_cs));
      }
    }
    public static Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> TryStructural(Cursors_Compile._ICursor__ cs) {
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs3 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      Views_mCore_Compile._IView__ _122_before = _let_tmp_rhs3.dtor_t;
      Cursors_Compile._ICursor__ _123_cs = _let_tmp_rhs3.dtor_cs;
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs4 = ((_123_cs).SkipByte()).Split();
      Views_mCore_Compile._IView__ _124_val = _let_tmp_rhs4.dtor_t;
      Cursors_Compile._ICursor__ _125_cs = _let_tmp_rhs4.dtor_cs;
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs5 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_125_cs);
      Views_mCore_Compile._IView__ _126_after = _let_tmp_rhs5.dtor_t;
      Cursors_Compile._ICursor__ _127_cs = _let_tmp_rhs5.dtor_cs;
      return Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>.create(JSON_mGrammar_Compile.Structural<Views_mCore_Compile._IView__>.create(_122_before, _124_val, _126_after), _127_cs);
    }
    public static Func<Views_mCore_Compile._IView__, Dafny.ISequence<byte>> SpecView { get {
      return ((System.Func<Views_mCore_Compile._IView__, Dafny.ISequence<byte>>)((_128_v) => {
        return JSON_mSpec_Compile.__default.View(_128_v);
      }));
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mCore_Compile
namespace JSON_mZeroCopy_mDeserializer_mStrings_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> String(Cursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _129_valueOrError0 = (cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>('\"');
      if ((_129_valueOrError0).IsFailure()) {
        return (_129_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _130_cs = (_129_valueOrError0).Extract();
        Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _131_valueOrError1 = (_130_cs).SkipWhileLexer<bool, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>((Lexers_mCore_Compile._ILexerState<bool, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _eta0, short _eta1) => Lexers_mStrings_Compile.__default.StringBody<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(_eta0, _eta1), Lexers_mCore_Compile.LexerState<bool, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_Partial(Lexers_mStrings_Compile.__default.StringBodyLexerStart));
        if ((_131_valueOrError1).IsFailure()) {
          return (_131_valueOrError1).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
        } else {
          Cursors_Compile._ICursor__ _132_cs = (_131_valueOrError1).Extract();
          Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _133_valueOrError2 = (_132_cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>('\"');
          if ((_133_valueOrError2).IsFailure()) {
            return (_133_valueOrError2).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
          } else {
            Cursors_Compile._ICursor__ _134_cs = (_133_valueOrError2).Extract();
            return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_134_cs).Split());
          }
        }
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mStrings_Compile
namespace JSON_mZeroCopy_mDeserializer_mNumbers_Compile {

  public partial class __default {
    public static Cursors_Compile._ISplit<Views_mCore_Compile._IView__> Digits(Cursors_Compile._ICursor__ cs) {
      return ((cs).SkipWhile(JSON_mGrammar_Compile.__default.Digit_q)).Split();
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> NonEmptyDigits(Cursors_Compile._ICursor__ cs) {
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _135_sp = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Digits(cs);
      Wrappers_Compile._IOutcome<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _136_valueOrError0 = Wrappers_Compile.__default.Need<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>(!(((_135_sp).dtor_t).Empty_q), Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_EmptyNumber()));
      if ((_136_valueOrError0).IsFailure()) {
        return (_136_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_135_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> NonZeroInt(Cursors_Compile._ICursor__ cs) {
      return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(cs);
    }
    public static Cursors_Compile._ISplit<Views_mCore_Compile._IView__> OptionalMinus(Cursors_Compile._ICursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_137_c) => {
        return (_137_c) == ((byte)('-'));
      })))).Split();
    }
    public static Cursors_Compile._ISplit<Views_mCore_Compile._IView__> OptionalSign(Cursors_Compile._ICursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_138_c) => {
        return ((_138_c) == ((byte)('-'))) || ((_138_c) == ((byte)('+')));
      })))).Split();
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> TrimmedInt(Cursors_Compile._ICursor__ cs) {
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _139_sp = ((cs).SkipIf(((System.Func<byte, bool>)((_140_c) => {
        return (_140_c) == ((byte)('0'));
      })))).Split();
      if (((_139_sp).dtor_t).Empty_q) {
        return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonZeroInt((_139_sp).dtor_cs);
      } else {
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_139_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Exp(Cursors_Compile._ICursor__ cs) {
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs6 = ((cs).SkipIf(((System.Func<byte, bool>)((_141_c) => {
        return ((_141_c) == ((byte)('e'))) || ((_141_c) == ((byte)('E')));
      })))).Split();
      Views_mCore_Compile._IView__ _142_e = _let_tmp_rhs6.dtor_t;
      Cursors_Compile._ICursor__ _143_cs = _let_tmp_rhs6.dtor_cs;
      if ((_142_e).Empty_q) {
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_Empty(), _143_cs));
      } else {
        Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs7 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalSign(_143_cs);
        Views_mCore_Compile._IView__ _144_sign = _let_tmp_rhs7.dtor_t;
        Cursors_Compile._ICursor__ _145_cs = _let_tmp_rhs7.dtor_cs;
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _146_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_145_cs);
        if ((_146_valueOrError0).IsFailure()) {
          return (_146_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>>();
        } else {
          Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs8 = (_146_valueOrError0).Extract();
          Views_mCore_Compile._IView__ _147_num = _let_tmp_rhs8.dtor_t;
          Cursors_Compile._ICursor__ _148_cs = _let_tmp_rhs8.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_NonEmpty(JSON_mGrammar_Compile.jexp.create(_142_e, _144_sign, _147_num)), _148_cs));
        }
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Frac(Cursors_Compile._ICursor__ cs) {
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs9 = ((cs).SkipIf(((System.Func<byte, bool>)((_149_c) => {
        return (_149_c) == ((byte)('.'));
      })))).Split();
      Views_mCore_Compile._IView__ _150_period = _let_tmp_rhs9.dtor_t;
      Cursors_Compile._ICursor__ _151_cs = _let_tmp_rhs9.dtor_cs;
      if ((_150_period).Empty_q) {
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_Empty(), _151_cs));
      } else {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _152_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_151_cs);
        if ((_152_valueOrError0).IsFailure()) {
          return (_152_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>>();
        } else {
          Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs10 = (_152_valueOrError0).Extract();
          Views_mCore_Compile._IView__ _153_num = _let_tmp_rhs10.dtor_t;
          Cursors_Compile._ICursor__ _154_cs = _let_tmp_rhs10.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_NonEmpty(JSON_mGrammar_Compile.jfrac.create(_150_period, _153_num)), _154_cs));
        }
      }
    }
    public static Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber> NumberFromParts(Cursors_Compile._ISplit<Views_mCore_Compile._IView__> minus, Cursors_Compile._ISplit<Views_mCore_Compile._IView__> num, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>> frac, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>> exp)
    {
      Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber> _155_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>.create(JSON_mGrammar_Compile.jnumber.create((minus).dtor_t, (num).dtor_t, (frac).dtor_t, (exp).dtor_t), (exp).dtor_cs);
      return _155_sp;
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Number(Cursors_Compile._ICursor__ cs) {
      Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _156_minus = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalMinus(cs);
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _157_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.TrimmedInt((_156_minus).dtor_cs);
      if ((_157_valueOrError0).IsFailure()) {
        return (_157_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>>();
      } else {
        Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _158_num = (_157_valueOrError0).Extract();
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _159_valueOrError1 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Frac((_158_num).dtor_cs);
        if ((_159_valueOrError1).IsFailure()) {
          return (_159_valueOrError1).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>>();
        } else {
          Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>> _160_frac = (_159_valueOrError1).Extract();
          Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _161_valueOrError2 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Exp((_160_frac).dtor_cs);
          if ((_161_valueOrError2).IsFailure()) {
            return (_161_valueOrError2).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>>();
          } else {
            Cursors_Compile._ISplit<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>> _162_exp = (_161_valueOrError2).Extract();
            return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NumberFromParts(_156_minus, _158_num, _160_frac, _162_exp));
          }
        }
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mNumbers_Compile
namespace JSON_mZeroCopy_mDeserializer_mObjectParams_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Colon(Cursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _163_valueOrError0 = (cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(':');
      if ((_163_valueOrError0).IsFailure()) {
        return (_163_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _164_cs = (_163_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_164_cs).Split());
      }
    }
    public static Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv> KVFromParts(Cursors_Compile._ISplit<Views_mCore_Compile._IView__> k, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> colon, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> v)
    {
      Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv> _165_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>.create(JSON_mGrammar_Compile.jkv.create((k).dtor_t, (colon).dtor_t, (v).dtor_t), (v).dtor_cs);
      return _165_sp;
    }
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile._Ijkv t) {
      return JSON_mSpec_Compile.__default.KV(t);
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Element(Cursors_Compile._ICursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _166_valueOrError0 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
      if ((_166_valueOrError0).IsFailure()) {
        return (_166_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv>>();
      } else {
        Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _167_k = (_166_valueOrError0).Extract();
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _168_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile._IView__>((_167_k).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile._IView__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Colon));
        if ((_168_valueOrError1).IsFailure()) {
          return (_168_valueOrError1).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv>>();
        } else {
          Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _169_colon = (_168_valueOrError1).Extract();
          Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _170_valueOrError2 = Dafny.Helpers.Id<Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>((json).dtor_fn)((_169_colon).dtor_cs);
          if ((_170_valueOrError2).IsFailure()) {
            return (_170_valueOrError2).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv>>();
          } else {
            Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> _171_v = (_170_valueOrError2).Extract();
            return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.KVFromParts(_167_k, _169_colon, _171_v));
          }
        }
      }
    }
    public static byte OPEN { get {
      return (byte)('{');
    } }
    public static byte CLOSE { get {
      return (byte)('}');
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mObjectParams_Compile
namespace JSON_mZeroCopy_mDeserializer_mObjects_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Object(Cursors_Compile._ICursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _172_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Bracketed(cs, json);
      if ((_172_valueOrError0).IsFailure()) {
        return (_172_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
      } else {
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> _173_sp = (_172_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_173_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Open(Cursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _174_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.OPEN);
      if ((_174_valueOrError0).IsFailure()) {
        return (_174_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _175_cs = (_174_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_175_cs).Split());
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Close(Cursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _176_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE);
      if ((_176_valueOrError0).IsFailure()) {
        return (_176_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _177_cs = (_176_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_177_cs).Split());
      }
    }
    public static Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> BracketedFromParts(Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> open, Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> elems, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> close)
    {
      Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> _178_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>.create(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _178_sp;
    }
    public static Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> AppendWithSuffix(Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> elems, Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv> elem, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__> _179_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>.create_NonEmpty((sep).dtor_t));
      Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> _180_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>.FromElements(_179_suffixed)), (sep).dtor_cs);
      return _180_elems_k;
    }
    public static Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> AppendLast(Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> elems, Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv> elem, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__> _181_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>.create_Empty());
      Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> _182_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>.FromElements(_181_suffixed)), (elem).dtor_cs);
      return _182_elems_k;
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Elements(Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> open, Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _183_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_183_valueOrError0).IsFailure()) {
        return (_183_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
      } else {
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijkv> _184_elem = (_183_valueOrError0).Extract();
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _185_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_184_elem).dtor_cs);
        short _186_s0 = (((_185_sep).dtor_t).dtor_t).Peek();
        if ((_186_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR))) {
          Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> _187_elems = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendWithSuffix(elems, _184_elem, _185_sep);
          Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _in16 = json;
          Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _in17 = open;
          Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> _in18 = _187_elems;
          json = _in16;
          open = _in17;
          elems = _in18;
          goto TAIL_CALL_START;
        } else if ((_186_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> _188_elems = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendLast(elems, _184_elem, _185_sep);
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(open, _188_elems, _185_sep));
        } else {
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Failure(Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE, JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR), _186_s0));
        }
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Bracketed(Cursors_Compile._ICursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _189_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile._IView__>(cs, Parsers_Compile.Parser__<Views_mCore_Compile._IView__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Open));
      if ((_189_valueOrError0).IsFailure()) {
        return (_189_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
      } else {
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _190_open = (_189_valueOrError0).Extract();
        Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>> _191_elems = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__>>.FromElements(), (_190_open).dtor_cs);
        if ((((_190_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _192_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile._IView__>((_190_open).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile._IView__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Close));
          if ((_192_valueOrError1).IsFailure()) {
            return (_192_valueOrError1).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
          } else {
            Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _193_close = (_192_valueOrError1).Extract();
            return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(_190_open, _191_elems, _193_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Elements(json, _190_open, _191_elems);
        }
      }
    }
    public static byte SEPARATOR { get {
      return (byte)(',');
    } }
  }

  public partial class jopen {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.OPEN));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.jopen.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.jclose.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mObjects_Compile
namespace JSON_mZeroCopy_mDeserializer_mArrayParams_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile._IValue t) {
      return JSON_mSpec_Compile.__default.Value(t);
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Element(Cursors_Compile._ICursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      return Dafny.Helpers.Id<Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>((json).dtor_fn)(cs);
    }
    public static byte OPEN { get {
      return (byte)('[');
    } }
    public static byte CLOSE { get {
      return (byte)(']');
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mArrayParams_Compile
namespace JSON_mZeroCopy_mDeserializer_mArrays_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Array(Cursors_Compile._ICursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _194_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Bracketed(cs, json);
      if ((_194_valueOrError0).IsFailure()) {
        return (_194_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
      } else {
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> _195_sp = (_194_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_195_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Open(Cursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _196_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.OPEN);
      if ((_196_valueOrError0).IsFailure()) {
        return (_196_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _197_cs = (_196_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_197_cs).Split());
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Close(Cursors_Compile._ICursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _198_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE);
      if ((_198_valueOrError0).IsFailure()) {
        return (_198_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _199_cs = (_198_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_199_cs).Split());
      }
    }
    public static Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> BracketedFromParts(Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> open, Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> elems, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> close)
    {
      Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> _200_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>.create(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _200_sp;
    }
    public static Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> AppendWithSuffix(Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> elems, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> elem, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__> _201_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>.create_NonEmpty((sep).dtor_t));
      Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> _202_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>.FromElements(_201_suffixed)), (sep).dtor_cs);
      return _202_elems_k;
    }
    public static Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> AppendLast(Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> elems, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> elem, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__> _203_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>.create_Empty());
      Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> _204_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>.FromElements(_203_suffixed)), (elem).dtor_cs);
      return _204_elems_k;
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Elements(Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json, Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> open, Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _205_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_205_valueOrError0).IsFailure()) {
        return (_205_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
      } else {
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue> _206_elem = (_205_valueOrError0).Extract();
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _207_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_206_elem).dtor_cs);
        short _208_s0 = (((_207_sep).dtor_t).dtor_t).Peek();
        if ((_208_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR))) {
          Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> _209_elems = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendWithSuffix(elems, _206_elem, _207_sep);
          Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _in19 = json;
          Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _in20 = open;
          Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> _in21 = _209_elems;
          json = _in19;
          open = _in20;
          elems = _in21;
          goto TAIL_CALL_START;
        } else if ((_208_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> _210_elems = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendLast(elems, _206_elem, _207_sep);
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(open, _210_elems, _207_sep));
        } else {
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Failure(Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE, JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR), _208_s0));
        }
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Bracketed(Cursors_Compile._ICursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _211_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile._IView__>(cs, Parsers_Compile.Parser__<Views_mCore_Compile._IView__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Open));
      if ((_211_valueOrError0).IsFailure()) {
        return (_211_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
      } else {
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _212_open = (_211_valueOrError0).Extract();
        Cursors_Compile._ISplit<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>> _213_elems = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__>>.FromElements(), (_212_open).dtor_cs);
        if ((((_212_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _214_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile._IView__>((_212_open).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile._IView__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Close));
          if ((_214_valueOrError1).IsFailure()) {
            return (_214_valueOrError1).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>>();
          } else {
            Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile._IView__>> _215_close = (_214_valueOrError1).Extract();
            return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(_212_open, _213_elems, _215_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Elements(json, _212_open, _213_elems);
        }
      }
    }
    public static byte SEPARATOR { get {
      return (byte)(',');
    } }
  }

  public partial class jopen {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.OPEN));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.jopen.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly Views_mCore_Compile._IView__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE));
    public static Views_mCore_Compile._IView__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile._IView__>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.jclose.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile._IView__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mArrays_Compile
namespace JSON_mZeroCopy_mDeserializer_mConstants_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Constant(Cursors_Compile._ICursor__ cs, Dafny.ISequence<byte> expected)
    {
      Wrappers_Compile._IResult<Cursors_Compile._ICursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _216_valueOrError0 = (cs).AssertBytes<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(expected, 0U);
      if ((_216_valueOrError0).IsFailure()) {
        return (_216_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>>();
      } else {
        Cursors_Compile._ICursor__ _217_cs = (_216_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_217_cs).Split());
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mConstants_Compile
namespace JSON_mZeroCopy_mDeserializer_mValues_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Value(Cursors_Compile._ICursor__ cs) {
      short _218_c = (cs).Peek();
      if ((_218_c) == ((short)('{'))) {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _219_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Object(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_219_valueOrError0).IsFailure()) {
          return (_219_valueOrError0).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> _let_tmp_rhs11 = (_219_valueOrError0).Extract();
          JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _220_obj = _let_tmp_rhs11.dtor_t;
          Cursors_Compile._ICursor__ _221_cs = _let_tmp_rhs11.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Object(_220_obj), _221_cs));
        }
      } else if ((_218_c) == ((short)('['))) {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _222_valueOrError1 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Array(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_222_valueOrError1).IsFailure()) {
          return (_222_valueOrError1).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile._ISplit<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__>> _let_tmp_rhs12 = (_222_valueOrError1).Extract();
          JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile._IView__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile._IView__, Views_mCore_Compile._IView__> _223_arr = _let_tmp_rhs12.dtor_t;
          Cursors_Compile._ICursor__ _224_cs = _let_tmp_rhs12.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Array(_223_arr), _224_cs));
        }
      } else if ((_218_c) == ((short)('\"'))) {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _225_valueOrError2 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
        if ((_225_valueOrError2).IsFailure()) {
          return (_225_valueOrError2).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs13 = (_225_valueOrError2).Extract();
          Views_mCore_Compile._IView__ _226_str = _let_tmp_rhs13.dtor_t;
          Cursors_Compile._ICursor__ _227_cs = _let_tmp_rhs13.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_String(_226_str), _227_cs));
        }
      } else if ((_218_c) == ((short)('t'))) {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _228_valueOrError3 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.TRUE);
        if ((_228_valueOrError3).IsFailure()) {
          return (_228_valueOrError3).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs14 = (_228_valueOrError3).Extract();
          Views_mCore_Compile._IView__ _229_cst = _let_tmp_rhs14.dtor_t;
          Cursors_Compile._ICursor__ _230_cs = _let_tmp_rhs14.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Bool(_229_cst), _230_cs));
        }
      } else if ((_218_c) == ((short)('f'))) {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _231_valueOrError4 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.FALSE);
        if ((_231_valueOrError4).IsFailure()) {
          return (_231_valueOrError4).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs15 = (_231_valueOrError4).Extract();
          Views_mCore_Compile._IView__ _232_cst = _let_tmp_rhs15.dtor_t;
          Cursors_Compile._ICursor__ _233_cs = _let_tmp_rhs15.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Bool(_232_cst), _233_cs));
        }
      } else if ((_218_c) == ((short)('n'))) {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<Views_mCore_Compile._IView__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _234_valueOrError5 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.NULL);
        if ((_234_valueOrError5).IsFailure()) {
          return (_234_valueOrError5).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile._ISplit<Views_mCore_Compile._IView__> _let_tmp_rhs16 = (_234_valueOrError5).Extract();
          Views_mCore_Compile._IView__ _235_cst = _let_tmp_rhs16.dtor_t;
          Cursors_Compile._ICursor__ _236_cs = _let_tmp_rhs16.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Null(_235_cst), _236_cs));
        }
      } else {
        Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _237_valueOrError6 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Number(cs);
        if ((_237_valueOrError6).IsFailure()) {
          return (_237_valueOrError6).PropagateFailure<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile._ISplit<JSON_mGrammar_Compile._Ijnumber> _let_tmp_rhs17 = (_237_valueOrError6).Extract();
          JSON_mGrammar_Compile._Ijnumber _238_num = _let_tmp_rhs17.dtor_t;
          Cursors_Compile._ICursor__ _239_cs = _let_tmp_rhs17.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Number(_238_num), _239_cs));
        }
      }
    }
    public static Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> ValueParser(Cursors_Compile._ICursor__ cs) {
      Func<Cursors_Compile._ICursor__, bool> _240_pre = Dafny.Helpers.Id<Func<Cursors_Compile._ICursor__, Func<Cursors_Compile._ICursor__, bool>>>((_241_cs) => ((System.Func<Cursors_Compile._ICursor__, bool>)((_242_ps_k) => {
        return ((_242_ps_k).Length()) < ((_241_cs).Length());
      })))(cs);
      Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>> _243_fn = Dafny.Helpers.Id<Func<Func<Cursors_Compile._ICursor__, bool>, Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>>((_244_pre) => ((System.Func<Cursors_Compile._ICursor__, Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>)((_245_ps_k) => {
        return JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value(_245_ps_k);
      })))(_240_pre);
      return Parsers_Compile.SubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(_243_fn);
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mValues_Compile
namespace JSON_mZeroCopy_mDeserializer_mAPI_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> JSON(Cursors_Compile._ICursor__ cs) {
      return JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mGrammar_Compile._IValue>(cs, Parsers_Compile.Parser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value));
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Text(Views_mCore_Compile._IView__ v) {
      Wrappers_Compile._IResult<Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _246_valueOrError0 = JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.JSON(Cursors_Compile.Cursor__.OfView(v));
      if ((_246_valueOrError0).IsFailure()) {
        return (_246_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
      } else {
        Cursors_Compile._ISplit<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>> _let_tmp_rhs18 = (_246_valueOrError0).Extract();
        JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _247_text = _let_tmp_rhs18.dtor_t;
        Cursors_Compile._ICursor__ _248_cs = _let_tmp_rhs18.dtor_cs;
        Wrappers_Compile._IOutcome<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _249_valueOrError1 = Wrappers_Compile.__default.Need<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>((_248_cs).EOF_q, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_ExpectingEOF()));
        if ((_249_valueOrError1).IsFailure()) {
          return (_249_valueOrError1).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
        } else {
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_247_text);
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> OfBytes(Dafny.ISequence<byte> bs) {
      Wrappers_Compile._IOutcome<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _250_valueOrError0 = Wrappers_Compile.__default.Need<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>((new BigInteger((bs).Count)) < (BoundedInts_Compile.__default.TWO__TO__THE__32), Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_IntOverflow()));
      if ((_250_valueOrError0).IsFailure()) {
        return (_250_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
      } else {
        return JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.Text(Views_mCore_Compile.View__.OfBytes(bs));
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mAPI_Compile
namespace JSON_mZeroCopy_mDeserializer_Compile {

} // end of namespace JSON_mZeroCopy_mDeserializer_Compile
namespace JSON_mZeroCopy_mAPI_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> Serialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return (JSON_mZeroCopy_mSerializer_Compile.__default.Text(js)).Bytes();
    }
    public static Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> SerializeAlloc(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js)
    {
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> bs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile._IError>.Default(new byte[0]);
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> _out3;
      _out3 = JSON_mZeroCopy_mSerializer_Compile.__default.Serialize(js);
      bs = _out3;
      return bs;
    }
    public static Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> SerializeBlit(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] bs)
    {
      Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile._IError>.Default(0);
      Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _out4;
      _out4 = JSON_mZeroCopy_mSerializer_Compile.__default.SerializeTo(js, bs);
      len = _out4;
      return len;
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Deserialize(Dafny.ISequence<byte> bs) {
      return JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.OfBytes(bs);
    }
  }
} // end of namespace JSON_mZeroCopy_mAPI_Compile
namespace JSON_mZeroCopy_Compile {

} // end of namespace JSON_mZeroCopy_Compile
namespace JSON_Compile {

} // end of namespace JSON_Compile
namespace Benchmarks {

  public partial class __default {
    public static void Serialize(Dafny.ISequence<byte> bytes)
    {
      uint _hi3 = Benchmarks.__default.WARMUP;
      for (uint _251_i = 0U; _251_i < _hi3; _251_i++) {
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _252___v0;
        _252___v0 = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(bytes);
      }
      Benchmarks.Interop.StartTimer();
      uint _hi4 = Benchmarks.__default.REPEATS;
      for (uint _253_i = 0U; _253_i < _hi4; _253_i++) {
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _254___v1;
        _254___v1 = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(bytes);
      }
      Benchmarks.Interop.ReportTimer(Dafny.Sequence<char>.FromString("Serialize"), new BigInteger((bytes).Count), Benchmarks.__default.REPEATS);
    }
    public static void Deserialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] target)
    {
      uint _hi5 = Benchmarks.__default.WARMUP;
      for (uint _255_i = 0U; _255_i < _hi5; _255_i++) {
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _256___v2;
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _out5;
        _out5 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeBlit(js, target);
        _256___v2 = _out5;
      }
      Benchmarks.Interop.StartTimer();
      uint _hi6 = Benchmarks.__default.REPEATS;
      for (uint _257_i = 0U; _257_i < _hi6; _257_i++) {
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _258___v3;
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _out6;
        _out6 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeBlit(js, target);
        _258___v3 = _out6;
      }
      Benchmarks.Interop.ReportTimer(Dafny.Sequence<char>.FromString("Deserialize"), new BigInteger((target).Length), Benchmarks.__default.REPEATS);
    }
    public static void _Main()
    {
      byte[] _259_input__array;
      byte[] _out7;
      _out7 = Benchmarks.Interop.ReadInput();
      _259_input__array = _out7;
      byte[] _260_output__array;
      byte[] _nw1 = new byte[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((_259_input__array).Length), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      _260_output__array = _nw1;
      Dafny.ISequence<byte> _261_bytes;
      _261_bytes = Dafny.Helpers.SeqFromArray(_259_input__array);
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _262_jsr;
      _262_jsr = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(_261_bytes);
      if (!((_262_jsr).is_Success)) {
        throw new Dafny.HaltException("c:\\Users\\cpitcla\\git\\dafny\\libraries\\src\\JSON\\Benchmarks\\Benchmark.dfy(50,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _263_js;
      _263_js = (_262_jsr).dtor_value;
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> _264_output;
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> _out8;
      _out8 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeAlloc(_263_js);
      _264_output = _out8;
      if (!((_264_output).is_Success)) {
        throw new Dafny.HaltException("c:\\Users\\cpitcla\\git\\dafny\\libraries\\src\\JSON\\Benchmarks\\Benchmark.dfy(54,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Benchmarks.__default.Serialize(_261_bytes);
      Benchmarks.__default.Deserialize(_263_js, _260_output__array);
    }
    public static uint WARMUP { get {
      return 0U;
    } }
    public static uint REPEATS { get {
      return 10U;
    } }
  }
} // end of namespace Benchmarks
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(Benchmarks.__default._Main);
  }
}
