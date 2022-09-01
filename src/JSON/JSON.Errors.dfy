include "../Wrappers.dfy"

module {:options "/functionSyntax:4"} JSON.Errors {
  import Wrappers

  datatype DeserializationError =
    | UnterminatedSequence
    | EscapeAtEOS
    | EmptyNumber
    | ExpectingEOF
    | IntOverflow
  {
    function ToString() : string {
      match this
        case EscapeAtEOS => "Escape character at end of string"
        case UnterminatedSequence => "Unterminated sequence"
        case EmptyNumber => "Number must contain at least one digit"
        case ExpectingEOF => "Expecting EOF"
        case IntOverflow => "Input length does not fit in a 32-bit counter"
    }
  }

  datatype SerializationError =
    | OutOfMemory
    | IntTooLarge(i: int)
    | StringTooLong(s: string)

  type SerializationResult<+T> = Wrappers.Result<T, SerializationError>
  type DeserializationResult<+T> = Wrappers.Result<T, DeserializationError>
}
