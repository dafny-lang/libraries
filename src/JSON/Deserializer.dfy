include "../BoundedInts.dfy"
include "../Wrappers.dfy"
include "Grammar.dfy"
include "Parsers.dfy"

module {:options "/functionSyntax:4"} JSON.Deserializer {
  module Core {
    import opened BoundedInts
    import opened Wrappers

    import opened Cursors
    import opened Parsers
    import opened Grammar

    datatype JSONError =
      | LeadingSeparator // "Separator not allowed before first item"
      | UnterminatedSequence // "Unterminated sequence."
      | EmptyNumber // "Number must contain at least one digit"
      | ExpectingEOF // "Expecting EOF"
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

    function {:opaque} Get(ps: FreshCursor, err: JSONError): (pp: ParseResult<jchar>)
      ensures pp.Success? ==> pp.value.t.Length() == 1
      ensures pp.Success? ==> pp.value.ps.StrictlySplitFrom?(ps) // FIXME splitfrom should be on pp
    {
      var ps :- ps.Get(err);
      Success(ps.Split())
    }

    function {:opaque} WS(ps: FreshCursor): (pp: Split<jblanks>)
      ensures pp.ps.SplitFrom?(ps)
    {
      ps.SkipWhile(Blank?).Split()
    }

    function Structural<T>(ps: FreshCursor, parser: Parser<T>)
      : (ppr: ParseResult<Structural<T>>)
      requires forall ps :: parser.fn.requires(ps)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
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

    type TItem
    function Item(ps: FreshCursor, json: SubParser<Value>)
      : (ppr: ParseResult<TItem>)
      requires ps.StrictlySplitFrom?(json.ps)
      decreases ps.Length()
      ensures ppr.Success? ==> ppr.value.ps.SplitFrom?(ps)
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
    type TSeq = Bracketed<jopen, jsep, TItem, jclose>

    function {:tailrecursion} SeparatorPrefixedItems(
      ps: FreshCursor, json: SubParser<Value>,
      open: Structural<jopen>,
      items: PrefixedSequence<jsep, TItem>
    ): (ppr: ParseResult<TSeq>)
      requires ps.StrictlySplitFrom?(json.ps)
      requires NoLeadingPrefix(items)
      decreases ps.Length()
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
    {
      var SP(sep, ps) :- Core.Structural(ps, Parsers.Parser(ps => Get(ps, UnterminatedSequence)));
      var s0 := sep.t.At(0);
      if s0 == CLOSE then
        Success(SP(Grammar.Bracketed(open, items, sep), ps))
      else if s0 == SEPARATOR then
        :- Need(|items| > 0, OtherError(LeadingSeparator));
        var SP(item, ps) :- Item(ps, json);
        var items := items + [Prefixed(NonEmpty(sep), item)];
        ghost var ppr' := SeparatorPrefixedItems(ps, json, open, items); // DISCUSS: Why is this needed?
        assert ppr'.Success? ==> ppr'.value.ps.StrictlySplitFrom?(ps);
        SeparatorPrefixedItems(ps, json, open, items)
      else
        Failure(ExpectingAnyByte([CLOSE, SEPARATOR], s0 as opt_byte))
    }

    function Open(ps: FreshCursor)
      : (ppr: ParseResult<jopen>)
    {
      var ps :- ps.AssertByte(OPEN);
      Success(ps.Split())
    }

    function Close(ps: FreshCursor)
      : (ppr: ParseResult<jclose>)
    {
      var ps :- ps.AssertByte(CLOSE);
      Success(ps.Split())
    }

    function Items(ps: FreshCursor, json: SubParser<Value>, open: Structural<jopen>)
      : (ppr: ParseResult<TSeq>)
      requires ps.StrictlySplitFrom?(json.ps)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
    {
      if ps.Peek() == CLOSE as opt_byte then
        var SP(close, ps) :- Core.Structural(ps, Parsers.Parser(Close));
        Success(SP(Grammar.Bracketed(open, [], close), ps))
      else
        var SP(item, ps) :- Item(ps, json);
        var items := [Prefixed(Empty(), item)];
        ghost var ppr' := SeparatorPrefixedItems(ps, json, open, items); // DISCUSS: Why is this needed?
        assert ppr'.Success? ==> ppr'.value.ps.StrictlySplitFrom?(ps);
        SeparatorPrefixedItems(ps, json, open, items)
    }

    lemma Valid(x: TSeq)
      ensures x.l.t.Byte?(OPEN)
      ensures x.r.t.Byte?(CLOSE)
      ensures NoLeadingPrefix(x.data)
      ensures forall pf | pf in x.data ::
        pf.before.NonEmpty? ==> pf.before.t.t.Byte?(SEPARATOR)
    { // DISCUSS: Why is this lemma needed?  Why does it require a body?
      var xlt: jopen := x.l.t;
      var xrt: jclose := x.r.t;
      forall pf | pf in x.data
        ensures pf.before.NonEmpty? ==> pf.before.t.t.Byte?(SEPARATOR)
      {
        if pf.before.NonEmpty? {
          var xtt := pf.before.t.t;
        }
      }
    }

    function Bracketed(ps: FreshCursor, json: SubParser<Value>)
      : (ppr: ParseResult<TSeq>)
      requires ps.SplitFrom?(json.ps)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
      // ensures ppr.Success? ==> Valid?(ppr.value.t)
    {
      var SP(open, ps) :- Core.Structural(ps, Parsers.Parser(Open));
      ghost var ppr := Items(ps, json, open); // DISCUSS: Why is this needed?
      assert ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps);
      Items(ps, json, open)
    }
  }

  module Top {
    import opened Wrappers

    import opened Vs = Views.Core
    import opened Grammar
    import opened Cursors
    import opened Core
    import Values

    function JSON(ps: FreshCursor) : (ppr: ParseResult<JSON>)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
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

    function Value(ps: FreshCursor) : (ppr: ParseResult<Value>)
      decreases ps.Length(), 1
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
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

    function Constant(ps: FreshCursor, expected: bytes) : (ppr: ParseResult<jstring>)
      requires |expected| < TWO_TO_THE_32
      ensures ppr.Success? ==> ppr.value.t.Bytes() == expected
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

    function String(ps: FreshCursor): (ppr: ParseResult<jstring>)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
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

    function NonEmptyDigits(ps: FreshCursor) : (ppr: ParseResult<jnum>)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
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

    function TrimmedInt(ps: FreshCursor) : (ppr: ParseResult<jint>)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
    {
      var pp := ps.SkipIf(c => c == '0' as byte).Split();
      if pp.t.Empty? then NonEmptyDigits(ps)
      else Success(pp)
    }

    function Exp(ps: FreshCursor) : (ppr: ParseResult<Maybe<jexp>>)
      ensures ppr.Success? ==> ppr.value.ps.SplitFrom?(ps)
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

    function Frac(ps: FreshCursor) : (ppr: ParseResult<Maybe<jfrac>>)
      ensures ppr.Success? ==> ppr.value.ps.SplitFrom?(ps)
    {
      var SP(period, ps) :=
        ps.SkipIf(c => c == '.' as byte).Split();
      if period.Empty? then
        Success(SP(Empty(), ps))
      else
        var SP(num, ps) :- NonEmptyDigits(ps);
        Success(SP(NonEmpty(JFrac(period, num)), ps))
    }

    function Number(ps: FreshCursor) : (ppr: ParseResult<Value>)
      ensures ppr.Success? ==> ppr.value.ps.StrictlySplitFrom?(ps)
      ensures ppr.Success? ==> ppr.value.t.Number?
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

    type TItem = Value

    const OPEN := '[' as byte
    const CLOSE := ']' as byte
    const SEPARATOR: byte := ',' as byte

    function Item(ps: FreshCursor, json: SubParser<Value>)
      : (ppr: ParseResult<TItem>)
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

    type TItem = jkv

    const OPEN := '{' as byte
    const CLOSE := '}' as byte
    const SEPARATOR: byte := ',' as byte

    function Colon(ps: FreshCursor)
      : (ppr: ParseResult<jcolon>)
    {
      var ps :- ps.AssertChar(':');
      Success(ps.Split())
    }

    function Item(ps: FreshCursor, json: SubParser<Value>)
      : (ppr: ParseResult<TItem>)
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
