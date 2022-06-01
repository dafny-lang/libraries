include "JSON.Grammar.dfy"
include "JSON.Spec.dfy"
include "JSON.SpecProperties.dfy"
include "Parsers.dfy"

module {:options "/functionSyntax:4"} JSON.ZeroCopy.Deserializer {
  module Core {
    import opened BoundedInts
    import opened Wrappers

    import Spec
    import Vs = Views.Core
    import opened Cursors
    import opened Parsers
    import opened Grammar

    datatype JSONError =
      | UnterminatedSequence
      | EmptyNumber
      | ExpectingEOF
      | IntOverflow
    {
      function ToString() : string {
        match this
          case UnterminatedSequence => "Unterminated sequence"
          case EmptyNumber => "Number must contain at least one digit"
          case ExpectingEOF => "Expecting EOF"
          case IntOverflow => "Input length does not fit in a 32-bit counter"
      }
    }
    type Error = CursorError<JSONError>
    type ParseResult<+T> = SplitResult<T, JSONError>
    type Parser<!T> = Parsers.Parser<T, JSONError>
    type SubParser<!T> = Parsers.SubParser<T, JSONError>

    // BUG(https://github.com/dafny-lang/dafny/issues/2179)
    const SpecView := (v: Vs.View) => Spec.View(v);

    function {:opaque} Get(cs: FreshCursor, err: JSONError): (pr: ParseResult<jchar>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var cs :- cs.Get(err);
      Success(cs.Split())
    }

    function {:opaque} WS(cs: FreshCursor): (sp: Split<jblanks>)
      ensures sp.SplitFrom?(cs, SpecView)
    {
      cs.SkipWhile(Blank?).Split()
    } by method {
      reveal WS();
      var point' := cs.point;
      var end := cs.end;
      while point' < end && Blank?(cs.s[point'])
        invariant cs.(point := point').Valid?
        invariant cs.(point := point').SkipWhile(Blank?) == cs.SkipWhile(Blank?)
      {
        point' := point' + 1;
      }
      return Cursor(cs.s, cs.beg, point', cs.end).Split();
    }

    function {:opaque} Structural<T>(cs: FreshCursor, parser: Parser<T>)
      : (pr: ParseResult<Structural<T>>)
      requires forall cs :: parser.fn.requires(cs)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, st => Spec.Structural(st, parser.spec))
    {
      var SP(before, cs) := WS(cs);
      var SP(val, cs) :- parser.fn(cs);
      var SP(after, cs) := WS(cs);
      Success(SP(Grammar.Structural(before, val, after), cs))
    }

    type jopt = v: Vs.View | v.Length() <= 1 witness Vs.View.OfBytes([])

    function {:opaque} TryStructural(cs: FreshCursor)
      : (sp: Split<Structural<jopt>>)
      ensures sp.SplitFrom?(cs, st => Spec.Structural(st, SpecView))
    {
      var SP(before, cs) := WS(cs);
      var SP(val, cs) := cs.SkipByte().Split();
      var SP(after, cs) := WS(cs);
      SP(Grammar.Structural(before, val, after), cs)
    }

    type ValueParser = sp: SubParser<Value> |
      forall t :: sp.spec(t) == Spec.Value(t)
      witness *
  }
  type Error = Core.Error

  abstract module SequenceParams {
    import opened BoundedInts

    import opened Grammar
    import opened Cursors
    import opened Core

    const OPEN: byte
    const CLOSE: byte

    type TElement

    ghost function ElementSpec(t: TElement) : bytes

    function Element(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<TElement>)
      requires cs.StrictlySplitFrom?(json.cs)
      decreases cs.Length()
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, ElementSpec)
  }

  abstract module Sequences {
    import opened Wrappers
    import opened BoundedInts
    import opened Params: SequenceParams

    import SpecProperties
    import opened Vs = Views.Core
    import opened Grammar
    import opened Cursors
    import Parsers
    import opened Core

    const SEPARATOR: byte := ',' as byte

    type jopen = v: Vs.View | v.Byte?(OPEN) witness Vs.View.OfBytes([OPEN])
    type jclose = v: Vs.View | v.Byte?(CLOSE) witness Vs.View.OfBytes([CLOSE])
    type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>
    type TSuffixedElement = Suffixed<TElement, jcomma>

    ghost function SuffixedElementSpec(e: TSuffixedElement) : bytes {
      ElementSpec(e.t) + Spec.CommaSuffix(e.suffix)
    }

    ghost function BracketedSpec(ts: TBracketed): bytes {
      Spec.Bracketed(ts, SuffixedElementSpec)
    }

    ghost function SuffixedElementsSpec(ts: seq<TSuffixedElement>): bytes {
      Spec.ConcatBytes(ts, SuffixedElementSpec)
    }

    function {:opaque} Open(cs: FreshCursor)
      : (pr: ParseResult<jopen>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, _ => [OPEN])
    {
      var cs :- cs.AssertByte(OPEN);
      Success(cs.Split())
    }

    function {:opaque} Close(cs: FreshCursor)
      : (pr: ParseResult<jclose>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, _ => [CLOSE])
    {
      var cs :- cs.AssertByte(CLOSE);
      Success(cs.Split())
    }

    function {:opaque} BracketedFromParts(ghost cs: Cursor,
                                open: Split<Structural<jopen>>,
                                elems: Split<seq<TSuffixedElement>>,
                                close: Split<Structural<jclose>>)
      : (sp: Split<TBracketed>)
      requires Grammar.NoTrailingSuffix(elems.t)
      requires open.StrictlySplitFrom?(cs, c => Spec.Structural(c, SpecView))
      requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
      requires close.StrictlySplitFrom?(elems.cs, c => Spec.Structural(c, SpecView))
      ensures sp.StrictlySplitFrom?(cs, BracketedSpec)
    {
      var sp := SP(Grammar.Bracketed(open.t, elems.t, close.t), close.cs);
      calc { // Dafny/Z3 has a lot of trouble with associativity, so do the steps one by one:
        cs.Bytes();
        Spec.Structural(open.t, SpecView) + open.cs.Bytes();
        Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
        Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
        Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
      }
      sp
    }

    function {:opaque} AppendWithSuffix(ghost cs0: FreshCursor,
                              ghost json: ValueParser,
                              elems: Split<seq<TSuffixedElement>>,
                              elem: Split<TElement>,
                              sep: Split<Structural<jcomma>>)
      : (elems': Split<seq<TSuffixedElement>>)
      requires elems.cs.StrictlySplitFrom?(json.cs)
      requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
      requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
      requires sep.StrictlySplitFrom?(elem.cs, c => Spec.Structural(c, SpecView))
      requires forall e | e in elems.t :: e.suffix.NonEmpty?
      ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
      ensures forall e | e in elems'.t :: e.suffix.NonEmpty?
      ensures elems'.cs.Length() < elems.cs.Length()
      ensures elems'.cs.StrictlySplitFrom?(json.cs)
    {
      var suffixed := Suffixed(elem.t, NonEmpty(sep.t));
      var elems' := SP(elems.t + [suffixed], sep.cs); // DISCUSS: Moving this down doubles the verification time
      SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
      elems'
    }

    function {:opaque} AppendLast(ghost cs0: FreshCursor,
                              ghost json: ValueParser,
                              elems: Split<seq<TSuffixedElement>>,
                              elem: Split<TElement>,
                              sep: Split<Structural<jclose>>)
      : (elems': Split<seq<TSuffixedElement>>)
      requires elems.cs.StrictlySplitFrom?(json.cs)
      requires elems.SplitFrom?(cs0, SuffixedElementsSpec)
      requires elem.StrictlySplitFrom?(elems.cs, ElementSpec)
      requires sep.StrictlySplitFrom?(elem.cs, c => Spec.Structural(c, SpecView))
      requires forall e | e in elems.t :: e.suffix.NonEmpty?
      ensures elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec)
      ensures NoTrailingSuffix(elems'.t)
      ensures elems'.cs.Length() < elems.cs.Length()
      ensures elems'.cs.StrictlySplitFrom?(json.cs)
      ensures sep.StrictlySplitFrom?(elems'.cs, c => Spec.Structural(c, SpecView))
    {
      var suffixed := Suffixed(elem.t, Empty());
      var elems' := SP(elems.t + [suffixed], elem.cs);
      SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
      elems'
    }

    // The implementation and proof of this function is more painful than
    // expected due to the tail recursion.
    function {:opaque} {:tailrecursion} Elements(
      ghost cs0: FreshCursor,
      json: ValueParser,
      open: Split<Structural<jopen>>,
      elems: Split<seq<TSuffixedElement>>
    ) // DISCUSS: Why is this function reverified once per instantiation of the module?
    : (pr: ParseResult<TBracketed>)
      requires open.StrictlySplitFrom?(cs0, c => Spec.Structural(c, SpecView))
      requires elems.cs.StrictlySplitFrom?(json.cs)
      requires elems.SplitFrom?(open.cs, SuffixedElementsSpec)
      requires forall e | e in elems.t :: e.suffix.NonEmpty?
      decreases elems.cs.Length()
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs0, BracketedSpec)
    {
      var elem :- Element(elems.cs, json);
      var sep := Core.TryStructural(elem.cs);
      var s0 := sep.t.t.Peek();
      if s0 == SEPARATOR as opt_byte then
        var elems := AppendWithSuffix(open.cs, json, elems, elem, sep);
        Elements(cs0, json, open, elems)
      else if s0 == CLOSE as opt_byte then
        var elems := AppendLast(open.cs, json, elems, elem, sep);
        Success(BracketedFromParts(cs0, open, elems, sep))
      else
        Failure(ExpectingAnyByte([CLOSE, SEPARATOR], s0))
    }

    function {:opaque} Bracketed(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<TBracketed>)
      requires cs.SplitFrom?(json.cs)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, BracketedSpec)
    {
      var open :- Core.Structural(cs, Parsers.Parser(Open, SpecView));
      assert open.cs.StrictlySplitFrom?(json.cs);
      var elems := SP([], open.cs);
      if open.cs.Peek() == CLOSE as opt_byte then
        var close :- Core.Structural(open.cs, Parsers.Parser(Close, SpecView));
        Success(BracketedFromParts(cs, open, elems, close))
      else
        Elements(cs, json, open, elems)
    }

    lemma Valid(x: TBracketed)
      ensures x.l.t.Byte?(OPEN)
      ensures x.r.t.Byte?(CLOSE)
      ensures NoTrailingSuffix(x.data)
      ensures forall pf | pf in x.data ::
        pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
    { // DISCUSS: Why is this lemma needed?  Why does it require a body?
      var xlt: jopen := x.l.t;
      var xrt: jclose := x.r.t;
      forall pf | pf in x.data
        ensures pf.suffix.NonEmpty? ==> pf.suffix.t.t.Byte?(SEPARATOR)
      {
        if pf.suffix.NonEmpty? {
          var xtt := pf.suffix.t.t;
        }
      }
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

    function {:opaque} JSON(cs: FreshCursor) : (pr: ParseResult<JSON>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.JSON)
    {
      Core.Structural(cs, Parsers.Parser(Values.Value, Spec.Value))
    }

    function {:opaque} Text(v: View) : (jsr: Result<JSON, Error>)
      ensures jsr.Success? ==> v.Bytes() == Spec.JSON(jsr.value)
    {
      var SP(text, cs) :- JSON(Cursor.OfView(v));
      :- Need(cs.EOF?, OtherError(ExpectingEOF));
      Success(text)
    }

    function {:opaque} OfBytes(bs: bytes) : (jsr: Result<JSON, Error>)
      ensures jsr.Success? ==> bs == Spec.JSON(jsr.value)
    {
      :- Need(|bs| < TWO_TO_THE_32, OtherError(IntOverflow));
      Text(Vs.View.OfBytes(bs))
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

    function {:opaque} Value(cs: FreshCursor) : (pr: ParseResult<Value>)
      decreases cs.Length(), 1
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Value)
    {
      var c := cs.Peek();
      if c == '{' as opt_byte then
        var SP(obj, cs) :- Objects.Object(cs, ValueParser(cs));
        Success(SP(Grammar.Object(obj), cs))
      else if c == '[' as opt_byte then
        var SP(arr, cs) :- Arrays.Array(cs, ValueParser(cs));
        Success(SP(Grammar.Array(arr), cs))
      else if c == '\"' as opt_byte then
        var SP(str, cs) :- Strings.String(cs);
        Success(SP(Grammar.String(str), cs))
      else if c == 't' as opt_byte then
        var SP(cst, cs) :- Constants.Constant(cs, TRUE);
        Success(SP(Grammar.Bool(cst), cs))
      else if c == 'f' as opt_byte then
        var SP(cst, cs) :- Constants.Constant(cs, FALSE);
        Success(SP(Grammar.Bool(cst), cs))
      else if c == 'n' as opt_byte then
        var SP(cst, cs) :- Constants.Constant(cs, NULL);
        Success(SP(Grammar.Null(cst), cs))
      else
        var SP(num, cs) :- Numbers.Number(cs);
        Success(SP(Grammar.Number(num), cs))
      }

      function {:opaque} ValueParser(cs: FreshCursor) : (p: ValueParser)
        decreases cs.Length(), 0
        ensures cs.SplitFrom?(p.cs)
      {
        var pre := (ps': FreshCursor) => ps'.Length() < cs.Length();
        var fn := (ps': FreshCursor) requires pre(ps') => Value(ps');
        Parsers.SubParser(cs, pre, fn, Spec.Value)
      }
  }

  module Constants {
    import opened BoundedInts
    import opened Wrappers

    import opened Grammar
    import opened Core
    import opened Cursors

    function {:opaque} Constant(cs: FreshCursor, expected: bytes) : (pr: ParseResult<jstring>)
      requires |expected| < TWO_TO_THE_32
      ensures pr.Success? ==> pr.value.t.Bytes() == expected
      ensures pr.Success? ==> pr.value.SplitFrom?(cs, _ => expected)
    {
      var cs :- cs.AssertBytes(expected);
      Success(cs.Split())
    }
  }

  module Strings {
    import opened Wrappers
    import opened BoundedInts

    import opened Grammar
    import opened Cursors
    import opened LC = Lexers.Core
    import opened Lexers.Strings
    import opened Parsers
    import opened Core

    function {:opaque} StringBody(cs: Cursor): (pr: CursorResult<JSONError>)
      ensures pr.Success? ==> pr.value.AdvancedFrom?(cs)
    {
      cs.SkipWhileLexer(Strings.StringBody, StringBodyLexerStart)
    } by method {
      reveal StringBody();
      var escaped := false;
      for point' := cs.point to cs.end
        invariant cs.(point := point').Valid?
        invariant cs.(point := point').SkipWhileLexer(Strings.StringBody, escaped) == StringBody(cs)
      {
        var byte := cs.s[point'];
        if byte == '\"' as byte && !escaped {
          return Success(Cursor(cs.s, cs.beg, point', cs.end));
        } else if byte == '\\' as byte {
          escaped := !escaped;
        } else {
          escaped := false;
        }
      }
      return Failure(EOF);
    }

    function {:opaque} String(cs: FreshCursor): (pr: ParseResult<jstring>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.String)
    {
      var cs :- cs.AssertChar('\"');
      var cs :- StringBody(cs);
      var cs :- cs.AssertChar('\"');
      Success(cs.Split())
    }
  }

  module Numbers {
    import opened BoundedInts
    import opened Wrappers

    import opened Grammar
    import opened Cursors
    import opened Core

    function {:opaque} Digits(cs: FreshCursor) : (sp: Split<jdigits>)
      ensures sp.SplitFrom?(cs, SpecView)
    {
      cs.SkipWhile(Digit?).Split()
    }

    function {:opaque} NonEmptyDigits(cs: FreshCursor) : (pr: ParseResult<jnum>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var sp := Digits(cs);
      :- Need(!sp.t.Empty?, OtherError(EmptyNumber));
      Success(sp)
    }

    function {:opaque} NonZeroInt(cs: FreshCursor) : (pr: ParseResult<jint>)
      requires cs.Peek() != '0' as opt_byte
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      NonEmptyDigits(cs)
    }

    function {:opaque} OptionalMinus(cs: FreshCursor) : (sp: Split<jminus>)
      ensures sp.SplitFrom?(cs, SpecView)
    {
      cs.SkipIf(c => c == '-' as byte).Split()
    }

    function {:opaque} OptionalSign(cs: FreshCursor) : (sp: Split<jsign>)
      ensures sp.SplitFrom?(cs, SpecView)
    {
      cs.SkipIf(c => c == '-' as byte || c == '+' as byte).Split()
    }

    function {:opaque} TrimmedInt(cs: FreshCursor) : (pr: ParseResult<jint>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var sp := cs.SkipIf(c => c == '0' as byte).Split();
      if sp.t.Empty? then NonZeroInt(sp.cs)
      else Success(sp)
    }

    function {:opaque} Exp(cs: FreshCursor) : (pr: ParseResult<Maybe<jexp>>)
      ensures pr.Success? ==> pr.value.SplitFrom?(cs, exp => Spec.Maybe(exp, Spec.Exp))
    {
      var SP(e, cs) :=
        cs.SkipIf(c => c == 'e' as byte || c == 'E' as byte).Split();
      if e.Empty? then
        Success(SP(Empty(), cs))
      else
        assert e.Char?('e') || e.Char?('E');
        var SP(sign, cs) := OptionalSign(cs);
        var SP(num, cs) :- NonEmptyDigits(cs);
        Success(SP(NonEmpty(JExp(e, sign, num)), cs))
    }

    function {:opaque} Frac(cs: FreshCursor) : (pr: ParseResult<Maybe<jfrac>>)
      ensures pr.Success? ==> pr.value.SplitFrom?(cs, frac => Spec.Maybe(frac, Spec.Frac))
    {
      var SP(period, cs) :=
        cs.SkipIf(c => c == '.' as byte).Split();
      if period.Empty? then
        Success(SP(Empty(), cs))
      else
        var SP(num, cs) :- NonEmptyDigits(cs);
        Success(SP(NonEmpty(JFrac(period, num)), cs))
    }

    function {:opaque} NumberFromParts(
      ghost cs: Cursor,
      minus: Split<jminus>, num: Split<jint>,
      frac: Split<Maybe<jfrac>>, exp: Split<Maybe<jexp>>
    )
      : (sp: Split<jnumber>)
      requires minus.SplitFrom?(cs, SpecView)
      requires num.StrictlySplitFrom?(minus.cs, SpecView)
      requires frac.SplitFrom?(num.cs, frac => Spec.Maybe(frac, Spec.Frac))
      requires exp.SplitFrom?(frac.cs, exp => Spec.Maybe(exp, Spec.Exp))
      ensures sp.StrictlySplitFrom?(cs, Spec.Number)
    {
      var sp := SP(Grammar.JNumber(minus.t, num.t, frac.t, exp.t), exp.cs);
      calc { // Dafny/Z3 has a lot of trouble with associativity, so do the steps one by one:
        cs.Bytes();
        Spec.View(minus.t) + minus.cs.Bytes();
        Spec.View(minus.t) + Spec.View(num.t) + num.cs.Bytes();
        Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac) + frac.cs.Bytes();
        Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac) + Spec.Maybe(exp.t, Spec.Exp) + exp.cs.Bytes();
        Spec.Number(sp.t) + exp.cs.Bytes();
      }
      sp
    }

    function {:opaque} Number(cs: FreshCursor) : (pr: ParseResult<jnumber>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Number)
    {
      var minus := OptionalMinus(cs);
      var num :- TrimmedInt(minus.cs);
      var frac :- Frac(num.cs);
      var exp :- Exp(frac.cs);
      Success(NumberFromParts(cs, minus, num, frac, exp))
    }
  }

  module ArrayParams refines SequenceParams {
    import opened Strings
    import opened Wrappers

    type TElement = Value

    const OPEN := '[' as byte
    const CLOSE := ']' as byte

    function ElementSpec(t: TElement) : bytes {
      Spec.Value(t)
    }
    function {:opaque} Element(cs: FreshCursor, json: ValueParser) : (pr: ParseResult<TElement>)
    {
      json.fn(cs)
    }
  }

  module Arrays refines Sequences {
    import opened Params = ArrayParams

    function {:opaque} Array(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<jarray>)
      requires cs.SplitFrom?(json.cs)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Array)
    {
      var sp :- Bracketed(cs, json);
      SpecProperties.Bracketed_Morphism(sp.t);
      assert Spec.Bracketed(sp.t, SuffixedElementSpec) == Spec.Array(sp.t);
      Success(sp)
    }
  }

  module ObjectParams refines SequenceParams {
    import opened Wrappers
    import Strings

    type TElement = jkv

    const OPEN := '{' as byte
    const CLOSE := '}' as byte

    function Colon(cs: FreshCursor) : (pr: ParseResult<jcolon>) // DISCUSS: Why can't I make this opaque?
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var cs :- cs.AssertChar(':');
      Success(cs.Split())
    }

    function {:opaque} KVFromParts(ghost cs: Cursor, k: Split<jstring>,
                                   colon: Split<Structural<jcolon>>, v: Split<Value>)
      : (sp: Split<jkv>)
      requires k.StrictlySplitFrom?(cs, Spec.String)
      requires colon.StrictlySplitFrom?(k.cs, c => Spec.Structural(c, SpecView))
      requires v.StrictlySplitFrom?(colon.cs, Spec.Value)
      ensures sp.StrictlySplitFrom?(cs, Spec.KV)
    {
      var sp := SP(Grammar.KV(k.t, colon.t, v.t), v.cs);
      calc { // Dafny/Z3 has a lot of trouble with associativity, so do the steps one by one:
        cs.Bytes();
        Spec.String(k.t) + k.cs.Bytes();
        Spec.String(k.t) + Spec.Structural(colon.t, SpecView) + colon.cs.Bytes();
        Spec.String(k.t) + Spec.Structural(colon.t, SpecView) + Spec.Value(v.t) + v.cs.Bytes();
        Spec.KV(sp.t) + v.cs.Bytes();
      }
      sp
    }

    function ElementSpec(t: TElement) : bytes {
      Spec.KV(t)
    }
    function {:opaque} Element(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<TElement>)
    {
      var k :- Strings.String(cs);
      var colon :- Core.Structural(k.cs, Parsers.Parser(Colon, SpecView));
      var v :- json.fn(colon.cs);
      Success(KVFromParts(cs, k, colon, v))
    }
  }

  module Objects refines Sequences {
    import opened Params = ObjectParams

    function {:opaque} Object(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<jobject>)
      requires cs.SplitFrom?(json.cs)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Object)
    {
      var sp :- Bracketed(cs, json);
      SpecProperties.Bracketed_Morphism(sp.t);
      assert Spec.Bracketed(sp.t, SuffixedElementSpec) == Spec.Object(sp.t); // DISCUSS
      Success(sp)
    }
  }
}
