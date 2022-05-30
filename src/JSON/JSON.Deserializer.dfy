include "JSON.Grammar.dfy"
include "Parsers.dfy"

module {:options "/functionSyntax:4"} JSON.Deserializer {
  module Core {
    import opened BoundedInts
    import opened Wrappers

    import opened Cursors
    import opened Parsers
    import opened Grammar

    datatype JSONError =
      | LeadingSeparator
      | UnterminatedSequence
      | EmptyNumber
      | ExpectingEOF
    {
      function ToString() : string {
        match this
          case LeadingSeparator => "Separator not allowed before first item"
          case UnterminatedSequence => "Unterminated sequence."
          case EmptyNumber => "Number must contain at least one digit"
          case ExpectingEOF => "Expecting EOF"
      }
    }
    type ParseError = CursorError<JSONError>
    type ParseResult<+T> = SplitResult<T, JSONError>
    type Parser<+T> = Parsers.Parser<T, JSONError>
    type SubParser<+T> = Parsers.SubParser<T, JSONError>

    // FIXME make more things opaque

    function {:opaque} Get(ps: FreshCursor, err: JSONError): (pr: ParseResult<jchar>)
      ensures pr.Success? ==> pr.value.t.Length() == 1
      ensures pr.Success? ==> ps.Bytes() == pr.value.t.Bytes() + pr.value.ps.Bytes()
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps) // FIXME splitfrom should be on pp
    {
      var ps :- ps.Get(err);
      Success(ps.Split())
    }

    function {:opaque} WS(ps: FreshCursor): (pp: Split<jblanks>)
      ensures ps.Bytes() == pp.t.Bytes() + pp.ps.Bytes()
      ensures pp.ps.SplitFrom?(ps)
    {
      ps.SkipWhile(Blank?).Split()
    }

    function Structural<T>(ps: FreshCursor, parser: Parser<T>)
      : (pr: ParseResult<Structural<T>>)
      requires forall ps :: parser.fn.requires(ps)
      // PROOF: pass spec in here ensures pr.Success? ==> ps.Bytes() == pr.value.t.Bytes() + pr.value.ps.Bytes()
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      var SP(before, ps) := WS(ps);
      var SP(val, ps) :- parser.fn(ps);
      var SP(after, ps) := WS(ps);
      Success(SP(Grammar.Structural(before, val, after), ps))
    }
  }

  abstract module SequenceParams {
    import opened BoundedInts

    import opened Grammar
    import opened Cursors
    import opened Core

    const OPEN: byte
    const CLOSE: byte
    const SEPARATOR: byte

    type TElement // LATER: With traits, make sure that TElement is convertible to bytes
    function Element(ps: FreshCursor, json: SubParser<Value>)
      : (pr: ParseResult<TElement>)
      requires ps.StrictlySplitFrom?(json.ps)
      decreases ps.Length()
      // PROOF pass spec here
      ensures pr.Success? ==> pr.value.ps.SplitFrom?(ps)
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
    type TSeq = Bracketed<jopen, jsep, TElement, jclose>

    function {:tailrecursion} SeparatorPrefixedElements(
      ps: FreshCursor, json: SubParser<Value>,
      open: Structural<jopen>,
      items: PrefixedSequence<jsep, TElement>
    ): (pr: ParseResult<TSeq>)
      requires ps.StrictlySplitFrom?(json.ps)
      requires NoLeadingPrefix(items)
      decreases ps.Length()
      // PROOF ensures pr.Success? ==> ps.Bytes() == pr.value.t.Bytes() + pr.value.ps.Bytes()
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      var SP(sep, ps) :- Core.Structural(ps, Parsers.Parser(ps => Get(ps, UnterminatedSequence)));
      var s0 := sep.t.At(0);
      if s0 == CLOSE then
        Success(SP(Grammar.Bracketed(open, items, sep), ps))
      else if s0 == SEPARATOR then
        :- Need(|items| > 0, OtherError(LeadingSeparator));
        var SP(item, ps) :- Element(ps, json);
        var items := items + [Prefixed(NonEmpty(sep), item)];
        ghost var pr' := SeparatorPrefixedElements(ps, json, open, items); // DISCUSS: Why is this needed?
        assert pr'.Success? ==> pr'.value.ps.StrictlySplitFrom?(ps);
        SeparatorPrefixedElements(ps, json, open, items)
      else
        Failure(ExpectingAnyByte([CLOSE, SEPARATOR], s0 as opt_byte))
    }

    function Open(ps: FreshCursor)
      : (pr: ParseResult<jopen>)
    {
      var ps :- ps.AssertByte(OPEN);
      Success(ps.Split())
    }

    function Close(ps: FreshCursor)
      : (pr: ParseResult<jclose>)
    {
      var ps :- ps.AssertByte(CLOSE);
      Success(ps.Split())
    }

    function Elements(ps: FreshCursor, json: SubParser<Value>, open: Structural<jopen>)
      : (pr: ParseResult<TSeq>)
      requires ps.StrictlySplitFrom?(json.ps)
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      if ps.Peek() == CLOSE as opt_byte then
        var SP(close, ps) :- Core.Structural(ps, Parsers.Parser(Close));
        Success(SP(Grammar.Bracketed(open, [], close), ps))
      else
        var SP(item, ps) :- Element(ps, json);
        var items := [Prefixed(Empty(), item)];
        ghost var pr' := SeparatorPrefixedElements(ps, json, open, items); // DISCUSS: Why is this needed?
        assert pr'.Success? ==> pr'.value.ps.StrictlySplitFrom?(ps);
        SeparatorPrefixedElements(ps, json, open, items)
    }

    lemma Valid(x: TSeq)
      ensures x.l.t.Byte?(OPEN)
      ensures x.r.t.Byte?(CLOSE)
      ensures NoLeadingPrefix(x.data)
      ensures forall pf | pf in x.data ::
        pf.prefix.NonEmpty? ==> pf.prefix.t.t.Byte?(SEPARATOR)
    { // DISCUSS: Why is this lemma needed?  Why does it require a body?
      var xlt: jopen := x.l.t;
      var xrt: jclose := x.r.t;
      forall pf | pf in x.data
        ensures pf.prefix.NonEmpty? ==> pf.prefix.t.t.Byte?(SEPARATOR)
      {
        if pf.prefix.NonEmpty? {
          var xtt := pf.prefix.t.t;
        }
      }
    }

    function Bracketed(ps: FreshCursor, json: SubParser<Value>)
      : (pr: ParseResult<TSeq>)
      requires ps.SplitFrom?(json.ps)
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
      // ensures pr.Success? ==> Valid?(pr.value.t)
    {
      var SP(open, ps) :- Core.Structural(ps, Parsers.Parser(Open));
      ghost var pr := Elements(ps, json, open); // DISCUSS: Why is this needed?
      assert pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps);
      Elements(ps, json, open)
    }
  }

  module Top {
    import opened Wrappers

    import opened Vs = Views.Core
    import opened Grammar
    import opened Cursors
    import opened Core
    import Values

    function JSON(ps: FreshCursor) : (pr: ParseResult<JSON>)
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      Core.Structural(ps, Parsers.Parser(Values.Value))
    }

    function Text(v: View) : (pr: Result<JSON, ParseError>) {
      var SP(text, ps) :- JSON(Cursor.OfView(v));
      :- Need(ps.EOF?, OtherError(ExpectingEOF));
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

    function Value(ps: FreshCursor) : (pr: ParseResult<Value>)
      decreases ps.Length(), 1
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      var c := ps.Peek();
      if c == '{' as opt_byte then
        var SP(obj, ps) :- Objects.Bracketed(ps, ValueParser(ps));
        Objects.Valid(obj);
        Success(SP(Grammar.Object(obj), ps))
      else if c == '[' as opt_byte then
        var SP(arr, ps) :- Arrays.Bracketed(ps, ValueParser(ps));
        Arrays.Valid(arr);
        Success(SP(Grammar.Array(arr), ps))
      else if c == '\"' as opt_byte then
        var SP(str, ps) :- Strings.String(ps);
        Success(SP(Grammar.String(str), ps))
      else if c == 't' as opt_byte then
        var SP(cst, ps) :- Constants.Constant(ps, TRUE);
        Success(SP(Grammar.Bool(cst), ps))
      else if c == 'f' as opt_byte then
        var SP(cst, ps) :- Constants.Constant(ps, FALSE);
        Success(SP(Grammar.Bool(cst), ps))
      else if c == 'n' as opt_byte then
        var SP(cst, ps) :- Constants.Constant(ps, NULL);
        Success(SP(Grammar.Null(cst), ps))
      else
        Numbers.Number(ps)
      }

      function ValueParser(ps: FreshCursor) : (p: SubParser<Value>)
        decreases ps.Length(), 0
        ensures ps.SplitFrom?(p.ps)
      {
        var pre := (ps': FreshCursor) => ps'.Length() < ps.Length();
        var fn := (ps': FreshCursor) requires pre(ps') => Value(ps');
        Parsers.SubParser(ps, pre, fn)
      }
  }

  module Constants {
    import opened BoundedInts
    import opened Wrappers

    import opened Grammar
    import opened Core
    import opened Cursors

    function Constant(ps: FreshCursor, expected: bytes) : (pr: ParseResult<jstring>)
      requires |expected| < TWO_TO_THE_32
      ensures pr.Success? ==> pr.value.t.Bytes() == expected
    {
      var ps :- ps.AssertBytes(expected);
      Success(ps.Split())
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

    function String(ps: FreshCursor): (pr: ParseResult<jstring>)
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      var ps :- ps.AssertChar('\"');
      var ps :- ps.SkipWhileLexer(StringBody, Partial(StringBodyLexerStart));
      var ps :- ps.AssertChar('\"');
      Success(ps.Split())
    }
  }

  module Numbers {
    import opened BoundedInts
    import opened Wrappers

    import opened Grammar
    import opened Cursors
    import opened Core

    function Digits(ps: FreshCursor)
      : (pp: Split<jdigits>)
      ensures pp.ps.SplitFrom?(ps)
    {
      ps.SkipWhile(Digit?).Split()
    }

    function NonEmptyDigits(ps: FreshCursor) : (pr: ParseResult<jnum>)
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      var pp := Digits(ps);
      :- Need(!pp.t.Empty?, OtherError(EmptyNumber));
      Success(pp)
    }

    function Minus(ps: FreshCursor) : (pp: Split<jminus>)
      ensures pp.ps.SplitFrom?(ps)
    {
      ps.SkipIf(c => c == '-' as byte).Split()
    }

    function Sign(ps: FreshCursor) : (pp: Split<jsign>)
      ensures pp.ps.SplitFrom?(ps)
    {
      ps.SkipIf(c => c == '-' as byte || c == '+' as byte).Split()
    }

    function TrimmedInt(ps: FreshCursor) : (pr: ParseResult<jint>)
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
    {
      var pp := ps.SkipIf(c => c == '0' as byte).Split();
      if pp.t.Empty? then NonEmptyDigits(ps)
      else Success(pp)
    }

    function Exp(ps: FreshCursor) : (pr: ParseResult<Maybe<jexp>>)
      ensures pr.Success? ==> pr.value.ps.SplitFrom?(ps)
    {
      var SP(e, ps) :=
        ps.SkipIf(c => c == 'e' as byte || c == 'E' as byte).Split();
      if e.Empty? then
        Success(SP(Empty(), ps))
      else
        assert e.Char?('e') || e.Char?('E');
        var SP(sign, ps) := Sign(ps);
        var SP(num, ps) :- NonEmptyDigits(ps);
        Success(SP(NonEmpty(JExp(e, sign, num)), ps))
    }

    function Frac(ps: FreshCursor) : (pr: ParseResult<Maybe<jfrac>>)
      ensures pr.Success? ==> pr.value.ps.SplitFrom?(ps)
    {
      var SP(period, ps) :=
        ps.SkipIf(c => c == '.' as byte).Split();
      if period.Empty? then
        Success(SP(Empty(), ps))
      else
        var SP(num, ps) :- NonEmptyDigits(ps);
        Success(SP(NonEmpty(JFrac(period, num)), ps))
    }

    function Number(ps: FreshCursor) : (pr: ParseResult<Value>)
      ensures pr.Success? ==> pr.value.ps.StrictlySplitFrom?(ps)
      ensures pr.Success? ==> pr.value.t.Number?
    {
      var SP(minus, ps) := Minus(ps);
      var SP(num, ps) :- TrimmedInt(ps);
      var SP(frac, ps) :- Frac(ps);
      var SP(exp, ps) :- Exp(ps);
      Success(SP(Grammar.Number(minus, num, frac, exp), ps))
    }
  }

  module ArrayParams refines SequenceParams {
    import opened Strings
    import opened Wrappers

    type TElement = Value

    const OPEN := '[' as byte
    const CLOSE := ']' as byte
    const SEPARATOR: byte := ',' as byte

    function Element(ps: FreshCursor, json: SubParser<Value>)
      : (pr: ParseResult<TElement>)
    {
      assert ps.StrictlySplitFrom?(json.ps);
      assert json.Valid?();
      assert json.Valid?();
      assert json.fn.requires(ps);
      json.fn(ps)
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

    function Colon(ps: FreshCursor)
      : (pr: ParseResult<jcolon>)
    {
      var ps :- ps.AssertChar(':');
      Success(ps.Split())
    }

    function Element(ps: FreshCursor, json: SubParser<Value>)
      : (pr: ParseResult<TElement>)
    {
      var SP(k, ps) :- Strings.String(ps);
      var SP(colon, ps) :- Core.Structural(ps, Parsers.Parser(Colon));
      var SP(v, ps) :- json.fn(ps);
      Success(SP(KV(k, colon, v), ps))
    }
  }

  module Objects refines Sequences {
    import opened Params = ObjectParams
  }
}
