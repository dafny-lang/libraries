include "stringParsers.dfy"
include "parsersBuilders.dfy"

module StringParsersBuilders refines ParserBuilders {
  import P = StringParsers
  export StringParsersBuilders extends ParserBuilders
    provides String, Int

  function String(s: string): B<string> {
    B(P.String(s))
  }
  function Int(): B<int> {
    B(P.Int())
  }
}