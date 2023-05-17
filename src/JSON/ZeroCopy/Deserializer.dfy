// RUN: %verify "%s"

include "../Utils/Seq.dfy"
include "../Errors.dfy"
include "../Grammar.dfy"
include "../ConcreteSyntax.Spec.dfy"
include "../ConcreteSyntax.SpecProperties.dfy"
include "../Utils/Parsers.dfy"

module {:options "-functionSyntax:4"} JSON.ZeroCopy.Deserializer {
  module Core {
    import opened BoundedInts
    import opened Wrappers

    import ConcreteSyntax.Spec
    import Vs = Utils.Views.Core
    import opened Utils.Cursors
    import opened Utils.Parsers
    import opened Grammar
    import Errors
    import opened Seq = Utils.Seq


    type JSONError = Errors.DeserializationError
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
    import opened Utils.Cursors
    import opened Core

    const OPEN: byte
    const CLOSE: byte

    type TElement

    ghost function ElementSpec(t: TElement): bytes

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

    import ConcreteSyntax.SpecProperties
    import opened Vs = Utils.Views.Core
    import opened Grammar
    import opened Utils.Cursors
    import Utils.Parsers
    import opened Core

    const SEPARATOR: byte := ',' as byte

    type jopen = v: Vs.View | v.Byte?(OPEN) witness Vs.View.OfBytes([OPEN])
    type jclose = v: Vs.View | v.Byte?(CLOSE) witness Vs.View.OfBytes([CLOSE])
    type TBracketed = Bracketed<jopen, TElement, jcomma, jclose>
    type TSuffixedElement = Suffixed<TElement, jcomma>

    ghost function SuffixedElementSpec(e: TSuffixedElement): bytes {
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
      calc {
        cs.Bytes();
        Spec.Structural(open.t, SpecView) + open.cs.Bytes();
        { assert open.cs.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes(); }
        Spec.Structural(open.t, SpecView) + (SuffixedElementsSpec(elems.t) + elems.cs.Bytes());
        { Seq.Assoc'(Spec.Structural(open.t, SpecView), SuffixedElementsSpec(elems.t), elems.cs.Bytes()); }
        Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
        { assert elems.cs.Bytes() == Spec.Structural(close.t, SpecView) + close.cs.Bytes(); }
        Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + (Spec.Structural(close.t, SpecView) + close.cs.Bytes());
        { Seq.Assoc'(Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t), Spec.Structural(close.t, SpecView), close.cs.Bytes()); }
        Spec.Structural(open.t, SpecView) + SuffixedElementsSpec(elems.t) + Spec.Structural(close.t, SpecView) + close.cs.Bytes();
        Spec.Bracketed(sp.t, SuffixedElementSpec) + close.cs.Bytes();
      }
      assert sp.StrictlySplitFrom?(cs, BracketedSpec);
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

      assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
        assert {:focus} cs0.Bytes() == SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() by {
          assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes() by {
            assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + elems.cs.Bytes();
            assert elems.cs.Bytes() == ElementSpec(suffixed.t) + elem.cs.Bytes();
            assert elem.cs.Bytes() == Spec.CommaSuffix(suffixed.suffix) + sep.cs.Bytes();
            Seq.Assoc'(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), elem.cs.Bytes());
            Seq.Assoc'(SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix), sep.cs.Bytes());
          }
          Seq.Assoc(SuffixedElementsSpec(elems.t), ElementSpec(suffixed.t), Spec.CommaSuffix(suffixed.suffix));
        }
        assert SuffixedElementsSpec(elems.t) + (ElementSpec(suffixed.t) + Spec.CommaSuffix(suffixed.suffix)) + sep.cs.Bytes() == SuffixedElementsSpec(elems'.t) + sep.cs.Bytes() by {
          assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
            SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
            assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) ==  Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
          }
        }
      }
      assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
      assert forall e | e in elems'.t :: e.suffix.NonEmpty? by { assert elems'.t == elems.t + [suffixed]; }
      assert {:split_here} elems'.cs.Length() < elems.cs.Length();
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

      assert cs0.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
        assert cs0.Bytes() == SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() by {
          assert elem.t == suffixed.t;
        }
        assert SuffixedElementsSpec(elems.t) + ElementSpec(suffixed.t) + elem.cs.Bytes() == SuffixedElementsSpec(elems'.t) + elem.cs.Bytes() by {
          assert SuffixedElementsSpec(elems.t) + SuffixedElementSpec(suffixed) == SuffixedElementsSpec(elems.t + [suffixed]) by {
            SpecProperties.ConcatBytes_Linear(elems.t, [suffixed], SuffixedElementSpec);
            assert Spec.ConcatBytes(elems.t, SuffixedElementSpec) + Spec.ConcatBytes([suffixed], SuffixedElementSpec) ==  Spec.ConcatBytes(elems.t + [suffixed], SuffixedElementSpec);
          }
        }
      }

      assert elems'.StrictlySplitFrom?(cs0, SuffixedElementsSpec);
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
        assert AppendWithSuffix.requires(open.cs, json, elems, elem, sep) by {
          assert {:focus} elems.cs.StrictlySplitFrom?(json.cs);
          assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
          assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
          assert sep.StrictlySplitFrom?(elem.cs, c => Spec.Structural(c, SpecView));
          assert forall e | e in elems.t :: e.suffix.NonEmpty?;
          assert {:split_here} true;
        }
        var elems := AppendWithSuffix(open.cs, json, elems, elem, sep);
        Elements(cs0, json, open, elems)
      else if s0 == CLOSE as opt_byte then
        assert AppendLast.requires(open.cs, json, elems, elem, sep) by {
          assert sep.StrictlySplitFrom?(elem.cs, c => Spec.Structural(c, SpecView));
          assert elems.cs.StrictlySplitFrom?(json.cs);
          assert elems.SplitFrom?(open.cs, SuffixedElementsSpec);
          assert elem.StrictlySplitFrom?(elems.cs, ElementSpec);
        }
        var elems' := AppendLast(open.cs, json, elems, elem, sep);
        assert elems'.SplitFrom?(open.cs, SuffixedElementsSpec) by {
          assert elems'.StrictlySplitFrom?(open.cs, SuffixedElementsSpec);
        }
        var bracketed := BracketedFromParts(cs0, open, elems', sep);
        assert bracketed.StrictlySplitFrom?(cs0, BracketedSpec);
        Success(bracketed)
      else
        var separator := SEPARATOR;
        var pr := Failure(ExpectingAnyByte([CLOSE, separator], s0));
        pr
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

    import opened Vs = Utils.Views.Core
    import opened Grammar
    import opened Core
    import opened Errors
    import Utils.Cursors
    import Values

    function LiftCursorError(err: Cursors.CursorError<DeserializationError>): DeserializationError {
      match err
      case EOF => ReachedEOF
      case ExpectingByte(expected, b) => ExpectingByte(expected, b)
      case ExpectingAnyByte(expected_sq, b) => ExpectingAnyByte(expected_sq, b)
      case OtherError(err) => err
    }

    function {:opaque} JSON(cs: Cursors.FreshCursor) : (pr: DeserializationResult<Cursors.Split<JSON>>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.JSON)
    {
      Core.Structural(cs, Parsers.Parser(Values.Value, Spec.Value)).MapFailure(LiftCursorError)
    }

    function {:opaque} Text(v: View) : (jsr: DeserializationResult<JSON>)
      ensures jsr.Success? ==> v.Bytes() == Spec.JSON(jsr.value)
    {
      var SP(text, cs) :- JSON(Cursors.Cursor.OfView(v));
      assert Cursors.SP(text, cs).BytesSplitFrom?(Cursors.Cursor.OfView(v), Spec.JSON);
      assert v.Bytes() == Spec.JSON(text) + cs.Bytes();
      :- Need(cs.EOF?, Errors.ExpectingEOF);
      assert cs.Bytes() == [];
      Success(text)
    }

    function {:opaque} OfBytes(bs: bytes) : (jsr: DeserializationResult<JSON>)
      ensures jsr.Success? ==> bs == Spec.JSON(jsr.value)
    {
      :- Need(|bs| < TWO_TO_THE_32, Errors.IntOverflow);
      Text(Vs.View.OfBytes(bs))
    }
  }

  module Values {
    import opened BoundedInts
    import opened Wrappers

    import opened Grammar
    import opened Utils.Cursors
    import opened Core

    import Strings
    import Numbers
    import Objects
    import Arrays
    import Constants

    import ConcreteSyntax.SpecProperties

    function {:opaque} Value(cs: FreshCursor) : (pr: ParseResult<Value>)
      decreases cs.Length(), 1
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Value)
    {
      var c := cs.Peek();
      if c == '{' as opt_byte then
        var SP(obj, cs') :- Objects.Object(cs, ValueParser(cs));
        var v := Grammar.Object(obj);
        var sp := SP(v, cs');
        assert sp.StrictlySplitFrom?(cs, Spec.Value) by {
          assert SP(obj, cs').StrictlySplitFrom?(cs, Spec.Object);
          Spec.UnfoldValueObject(v);
        }
        Success(sp)
      else if c == '[' as opt_byte then
        var SP(arr, cs') :- Arrays.Array(cs, ValueParser(cs));
        var v := Grammar.Array(arr);
        var sp := SP(v, cs');
        assert sp.StrictlySplitFrom?(cs, Spec.Value) by {
          assert SP(arr, cs').StrictlySplitFrom?(cs, Spec.Array);
          Spec.UnfoldValueArray(v);
        }
        Success(sp)
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
        var SP(num, cs') :- Numbers.Number(cs);
        var v := Grammar.Number(num);
        var sp := SP(v, cs');
        assert sp.StrictlySplitFrom?(cs, Spec.Value) by {
          assert SP(num, cs').StrictlySplitFrom?(cs, Spec.Number);
          Spec.UnfoldValueNumber(v);
        }
        assert sp.StrictlySplitFrom?(cs, Spec.Value);
        Success(sp)
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
    import opened Utils.Cursors

    function {:opaque} Constant(cs: FreshCursor, expected: bytes) : (pr: ParseResult<Vs.View>)
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
    import opened Utils.Cursors
    import opened LC = Utils.Lexers.Core
    import opened Utils.Lexers.Strings
    import opened Utils.Parsers
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

    function Quote(cs: FreshCursor) : (pr: ParseResult<jquote>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var cs :- cs.AssertChar('\"');
      Success(cs.Split())
    }

    function {:opaque} String(cs: FreshCursor): (pr: ParseResult<jstring>)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.String)
    {
      var SP(lq, cs) :- Quote(cs);
      var contents :- StringBody(cs);
      var SP(contents, cs) := contents.Split();
      var SP(rq, cs) :- Quote(cs);
      Success(SP(Grammar.JString(lq, contents, rq), cs))
    }
  }

  module Numbers {
    import opened BoundedInts
    import opened Wrappers

    import opened Grammar
    import opened Utils.Cursors
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
      :- Need(!sp.t.Empty?, OtherError(Errors.EmptyNumber));
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

    function {:opaque} {:vcs_split_on_every_assert} Exp(cs: FreshCursor) : (pr: ParseResult<Maybe<jexp>>)
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
      assert cs.Bytes() == Spec.Number(sp.t) + exp.cs.Bytes() by {
        assert cs.Bytes() == Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac) + Spec.Maybe(exp.t, Spec.Exp) + exp.cs.Bytes() by {
          assert cs.Bytes() == Spec.View(minus.t) + minus.cs.Bytes();
          assert minus.cs.Bytes() == Spec.View(num.t) + num.cs.Bytes();
          assert num.cs.Bytes() == Spec.Maybe(frac.t, Spec.Frac) + frac.cs.Bytes();
          assert frac.cs.Bytes() == Spec.Maybe(exp.t, Spec.Exp) + exp.cs.Bytes();
          Seq.Assoc'(Spec.View(minus.t), Spec.View(num.t), num.cs.Bytes());
          Seq.Assoc'(Spec.View(minus.t) + Spec.View(num.t), Spec.Maybe(frac.t, Spec.Frac), frac.cs.Bytes());
          Seq.Assoc'(Spec.View(minus.t) + Spec.View(num.t) + Spec.Maybe(frac.t, Spec.Frac), Spec.Maybe(exp.t, Spec.Exp), exp.cs.Bytes());
        }
      }
      assert sp.StrictlySplitFrom?(cs, Spec.Number);



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

    lemma BracketedToArray(arr: jarray)
      ensures Spec.Bracketed(arr, SuffixedElementSpec) == Spec.Array(arr)
    {
      var rItem := (d: jitem) requires d < arr => Spec.Item(d);
      assert Spec.Bracketed(arr, SuffixedElementSpec) == Spec.Bracketed(arr, rItem) by {
        SpecProperties.Bracketed_Morphism(arr);
        assert forall d | d < arr :: SuffixedElementSpec(d) == rItem(d);
      }
      calc {
        Spec.Bracketed(arr, SuffixedElementSpec);
        Spec.Bracketed(arr, rItem);
        Spec.Array(arr);
      }
    }

    function {:opaque}  Array(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<jarray>)
      requires cs.SplitFrom?(json.cs)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Array)
    {
      var sp :- Bracketed(cs, json);
      assert sp.StrictlySplitFrom?(cs, BracketedSpec);
      BracketedToArray(sp.t);
      Success(sp)
    }
  }

  module ObjectParams refines SequenceParams {
    import opened Wrappers
    import Strings

    type TElement = jKeyValue

    const OPEN := '{' as byte
    const CLOSE := '}' as byte

    function Colon(cs: FreshCursor) : (pr: ParseResult<jcolon>) // DISCUSS: Why can't I make this opaque?
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, SpecView)
    {
      var cs :- cs.AssertChar(':');
      Success(cs.Split())
    }

    function {:opaque} KeyValueFromParts(ghost cs: Cursor, k: Split<jstring>,
                                         colon: Split<Structural<jcolon>>, v: Split<Value>)
      : (sp: Split<jKeyValue>)
      requires k.StrictlySplitFrom?(cs, Spec.String)
      requires colon.StrictlySplitFrom?(k.cs, c => Spec.Structural(c, SpecView))
      requires v.StrictlySplitFrom?(colon.cs, Spec.Value)
      ensures sp.StrictlySplitFrom?(cs, ElementSpec)
    {
      var sp := SP(Grammar.KeyValue(k.t, colon.t, v.t), v.cs);
      assert cs.Bytes() == Spec.KeyValue(sp.t) + v.cs.Bytes() by {
        assert cs.Bytes() == Spec.String(k.t) + Spec.Structural(colon.t, SpecView) + Spec.Value(v.t) + v.cs.Bytes() by {
          assert cs.Bytes() == Spec.String(k.t) + k.cs.Bytes();
          assert k.cs.Bytes() == Spec.Structural(colon.t, SpecView) + colon.cs.Bytes();
          assert colon.cs.Bytes() == Spec.Value(v.t) + v.cs.Bytes();
          Seq.Assoc'(Spec.String(k.t), Spec.Structural(colon.t, SpecView), colon.cs.Bytes());
          Seq.Assoc'(Spec.String(k.t) + Spec.Structural(colon.t, SpecView), Spec.Value(v.t), v.cs.Bytes());
        }
      }
      assert sp.StrictlySplitFrom?(cs, ElementSpec);
      sp
    }

    function ElementSpec(t: TElement) : bytes {
      Spec.KeyValue(t)
    }
    function {:opaque} Element(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<TElement>)
    {
      var k :- Strings.String(cs);
      assert k.cs.StrictlySplitFrom?(json.cs);

      var p := Parsers.Parser(Colon, SpecView);
      assert p.Valid?();
      var colon :- Core.Structural(k.cs, p);
      assert colon.StrictlySplitFrom?(k.cs, st => Spec.Structural(st, p.spec));
      assert colon.cs.StrictlySplitFrom?(json.cs);

      var v :- json.fn(colon.cs);
      var kv := KeyValueFromParts(cs, k, colon, v);
      Success(kv)
    }
  }

  module Objects refines Sequences {
    import opened Params = ObjectParams

    lemma {:vcs_split_on_every_assert} BracketedToObject(obj: jobject)
      ensures Spec.Bracketed(obj, SuffixedElementSpec) == Spec.Object(obj)
    {
      var rMember := (d: jmember) requires d < obj => Spec.Member(d);
      assert Spec.Bracketed(obj, SuffixedElementSpec) == Spec.Bracketed(obj, rMember) by {
        SpecProperties.Bracketed_Morphism(obj);
        assert forall d | d < obj :: SuffixedElementSpec(d) == rMember(d);
      }
      calc {
        Spec.Bracketed(obj, SuffixedElementSpec);
        Spec.Bracketed(obj, rMember);
        Spec.Object(obj);
      }
    }

    function {:opaque} Object(cs: FreshCursor, json: ValueParser)
      : (pr: ParseResult<jobject>)
      requires cs.SplitFrom?(json.cs)
      ensures pr.Success? ==> pr.value.StrictlySplitFrom?(cs, Spec.Object)
    {
      var sp :- Bracketed(cs, json);
      assert sp.StrictlySplitFrom?(cs, BracketedSpec);
      BracketedToObject(sp.t);
      Success(sp)
    }
  }
}
