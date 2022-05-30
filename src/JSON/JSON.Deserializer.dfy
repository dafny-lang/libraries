include "JSON.Grammar.dfy"
include "JSON.Spec.dfy"
include "Parsers.dfy"

module {:options "/functionSyntax:4"} JSON.Deserializer {
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
    {
      function ToString() : string {
        match this
          case UnterminatedSequence => "Unterminated sequence"
          case EmptyNumber => "Number must contain at least one digit"
          case ExpectingEOF => "Expecting EOF"
      }
    }
    type ParseError = CursorError<JSONError>
    type ParseResult<+T> = SplitResult<T, JSONError>
    type Parser<!T> = Parsers.Parser<T, JSONError>
    type SubParser<!T> = Parsers.SubParser<T, JSONError>

    // BUG(https://github.com/dafny-lang/dafny/issues/2179)
    const SpecView := (v: Vs.View) => Spec.View(v);

    // FIXME make more things opaque

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
    }

    function Structural<T>(cs: FreshCursor, parser: Parser<T>)
      : (pr: ParseResult<Structural<T>>)
      requires forall cs :: parser.fn.requires(cs)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, st => Spec.Structural(st, parser.spec))
    {
      var SP(before, cs) := WS(cs);
      var SP(val, cs) :- parser.fn(cs);
      var SP(after, cs) := WS(cs);
      Success(SP(Grammar.Structural(before, val, after), cs))
    }

    type ValueParser = sp: SubParser<Value> |
      forall t :: sp.spec(t) == Spec.Value(t)
      witness *
  }

  abstract module SequenceParams {
    import opened BoundedInts

    import opened Grammar
    import opened Cursors
    import opened Core

    const OPEN: byte
    const CLOSE: byte
    const SEPARATOR: byte

    type TElement
    ghost function ElementSpec(t: TElement) : bytes
    function Element(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<TElement>)
      requires cs.StrictlySplitFrom?(json.cs)
      decreases cs.Length()
      ensures pr.Success? ==> pr.value.SplitFrom?(cs, ElementSpec)
  }

  abstract module Sequences {
    import opened Wrappers
    import opened BoundedInts
    import opened Params: SequenceParams

    import opened Vs = Views.Core
    import opened Grammar
    import opened Cursors
    import Parsers
    import opened Core

    type jopen = v: View | v.Byte?(OPEN) witness View.OfBytes([OPEN])
    type jclose = v: View | v.Byte?(CLOSE) witness View.OfBytes([CLOSE])
    type jsep = v: View | v.Byte?(SEPARATOR) witness View.OfBytes([SEPARATOR])
    type TSeq = Bracketed<jopen, TElement, jsep, jclose>

    function Open(cs: FreshCursor)
      : (pr: ParseResult<jopen>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, _ => [OPEN])
    {
      var cs :- cs.AssertByte(OPEN);
      Success(cs.Split())
    }

    function Close(cs: FreshCursor)
      : (pr: ParseResult<jclose>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, _ => [CLOSE])
    {
      var cs :- cs.AssertByte(CLOSE);
      Success(cs.Split())
    }

    function {:tailrecursion} Elements(
      cs: FreshCursor, json: ValueParser,
      open: Structural<jopen>,
      items: seq<Suffixed<TElement, jsep>> := []
    )
      : (pr: ParseResult<TSeq>)
      requires cs.StrictlySplitFrom?(json.cs)
      requires forall x | x in items :: x.suffix.NonEmpty?
      decreases cs.Length()
      ensures pr.Success? ==> pr.value.cs.StrictlySplitFrom?(cs)
      // PROOF
    {
      var SP(item, cs) :- Element(cs, json);
      var SP(sep, cs) :- Core.Structural(cs,
        Parsers.Parser(cs => Get(cs, UnterminatedSequence), SpecView));
      var s0 := sep.t.At(0);
      if s0 == CLOSE then
        var items := items + [Suffixed(item, Empty())];
        Success(SP(Grammar.Bracketed(open, items, sep), cs))
      else if s0 == SEPARATOR then
        var SP(item, cs) :- Element(cs, json);
        var items := items + [Suffixed(item, NonEmpty(sep))];
        ghost var pr' := Elements(cs, json, open, items); // DISCUSS: Why is this needed?
        assert pr'.Success? ==> pr'.value.cs.StrictlySplitFrom?(cs);
        Elements(cs, json, open, items)
      else
        Failure(ExpectingAnyByte([CLOSE, SEPARATOR], s0 as opt_byte))
    }

    function Bracketed(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<TSeq>)
      requires cs.SplitFrom?(json.cs)
      ensures pr.Success? ==> pr.value.cs.StrictlySplitFrom?(cs)
    {
      var SP(open, cs) :- Core.Structural(cs, Parsers.Parser(Open, SpecView));
      if cs.Peek() == CLOSE as opt_byte then
        var SP(close, cs) :- Core.Structural(cs, Parsers.Parser(Close, SpecView));
        Success(SP(Grammar.Bracketed(open, [], close), cs))
      else
        ghost var pr := Elements(cs, json, open); // DISCUSS: Why is this needed?
        assert pr.Success? ==> pr.value.cs.StrictlySplitFrom?(cs);
        Elements(cs, json, open)
    }

    lemma Valid(x: TSeq)
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

  module Top {
    import opened Wrappers

    import opened Vs = Views.Core
    import opened Grammar
    import opened Cursors
    import opened Core
    import Values

    function JSON(cs: FreshCursor) : (pr: ParseResult<JSON>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.JSON)
    {
      Core.Structural(cs, Parsers.Parser(Values.Value, Spec.Value))
    }

    function Text(v: View) : (pr: Result<JSON, ParseError>) {
      var SP(text, cs) :- JSON(Cursor.OfView(v));
      :- Need(cs.EOF?, OtherError(ExpectingEOF));
      Success(text)
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

    function {:opaque} Value(cs: FreshCursor) : (pr: ParseResult<Value>)
      decreases cs.Length(), 1
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Value)
    {
      var c := cs.Peek();
      if c == '{' as opt_byte then assume false;
        var SP(obj, cs) :- Objects.Bracketed(cs, ValueParser(cs));
        Objects.Valid(obj);
        Success(SP(Grammar.Object(obj), cs))
      else if c == '[' as opt_byte then assume false;
        var SP(arr, cs) :- Arrays.Bracketed(cs, ValueParser(cs));
        Arrays.Valid(arr);
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

      function ValueParser(cs: FreshCursor) : (p: ValueParser)
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

    function Constant(cs: FreshCursor, expected: bytes) : (pr: ParseResult<jstring>)
      requires |expected| < TWO_TO_THE_32
      ensures pr.Success? ==> pr.value.SplitFrom?(cs, _ => expected)
    {
      var cs :- cs.AssertBytes(expected);
      Success(cs.Split())
    }
  }

  module Strings {
    import opened Wrappers

    import opened Grammar
    import opened Cursors
    import opened LC = Lexers.Core
    import opened Lexers.Strings
    import opened Parsers
    import opened Core

    function String(cs: FreshCursor): (pr: ParseResult<jstring>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.String)
    {
      var cs :- cs.AssertChar('\"');
      var cs :- cs.SkipWhileLexer(StringBody, Partial(StringBodyLexerStart));
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

    function Digits(cs: FreshCursor)
      : (sp: Split<jdigits>)
      ensures sp.cs.SplitFrom?(cs)
    {
      cs.SkipWhile(Digit?).Split()
    }

    function NonEmptyDigits(cs: FreshCursor) : (pr: ParseResult<jnum>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var sp := Digits(cs);
      :- Need(!sp.t.Empty?, OtherError(EmptyNumber));
      Success(sp)
    }

    function OptionalMinus(cs: FreshCursor) : (sp: Split<jminus>)
      ensures sp.SplitFrom?(cs, SpecView)
    {
      cs.SkipIf(c => c == '-' as byte).Split()
    }

    function OptionalSign(cs: FreshCursor) : (sp: Split<jsign>)
      ensures sp.SplitFrom?(cs, SpecView)
    {
      cs.SkipIf(c => c == '-' as byte || c == '+' as byte).Split()
    }

    function TrimmedInt(cs: FreshCursor) : (pr: ParseResult<jint>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var sp := cs.SkipIf(c => c == '0' as byte).Split();
      if sp.t.Empty? then NonEmptyDigits(cs)
      else Success(sp)
    }

    function Exp(cs: FreshCursor) : (pr: ParseResult<Maybe<jexp>>)
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

    function Frac(cs: FreshCursor) : (pr: ParseResult<Maybe<jfrac>>)
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

    function NumberFromParts(ghost cs: Cursor,
                             minus: Split<jminus>, num: Split<jint>,
                             frac: Split<Maybe<jfrac>>, exp: Split<Maybe<jexp>>)
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

    function Number(cs: FreshCursor) : (pr: ParseResult<jnumber>)
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
    const SEPARATOR: byte := ',' as byte

    function ElementSpec(t: TElement) : bytes {
      Spec.Value(t)
    }
    function Element(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<TElement>)
    {
      json.fn(cs)
    }
  }

  module Arrays refines Sequences {
    import opened Params = ArrayParams
  }

  module ObjectParams refines SequenceParams {
    import opened Wrappers
    import Strings

    type TElement = jkv

    const OPEN := '{' as byte
    const CLOSE := '}' as byte
    const SEPARATOR: byte := ',' as byte

    function Colon(cs: FreshCursor)
      : (pr: ParseResult<jcolon>)
    {
      var cs :- cs.AssertChar(':');
      Success(cs.Split())
    }

    function KVFromParts(ghost cs: Cursor, k: Split<jstring>,
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
    function Element(cs: FreshCursor, json: ValueParser)
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
  }
}
