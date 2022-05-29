include "../Wrappers.dfy"
include "../BoundedInts.dfy"

module {:options "-functionSyntax:4"} Lexers {
  module Core {
    import opened Wrappers
    import opened BoundedInts

    datatype LexerState<+T, +R> = Accept | Reject(err: R) | Partial(st: T)

    type Lexer<!T, !R> = (LexerState<T, R>, opt_byte) -> LexerState<T, R>
  }

  module Strings {
    import opened Core
    import opened BoundedInts

    type StringBodyLexerState = /* escaped: */ bool
    const StringBodyLexerStart: StringBodyLexerState := false;

    function StringBody<R>(st: LexerState<StringBodyLexerState, R>, byte: opt_byte)
      : LexerState<StringBodyLexerState, R>
    {
      match st
        case Partial(escaped) =>
          if byte == '\\' as opt_byte then Partial(!escaped)
          else if byte == '\"' as opt_byte && !escaped then Accept
          else Partial(false)
        case _ => st
    }

    datatype StringLexerState = Start | Body(escaped: bool) | End
    const StringLexerStart: StringLexerState := Start;

    function String(st: LexerState<StringLexerState, string>, byte: opt_byte)
      : LexerState<StringLexerState, string>
    {
      match st
        case Partial(Start()) =>
          if byte == '\"' as opt_byte then Partial(Body(false))
          else Reject("String must start with double quote")
        case Partial(End()) =>
          Accept
        case Partial(Body(escaped)) =>
          if byte == '\\' as opt_byte then Partial(Body(!escaped))
          else if byte == '\"' as opt_byte && !escaped then Partial(End)
          else Partial(Body(false))
        case _ => st
    }
  }
}
