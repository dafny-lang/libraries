# Verified Parser Combinator Library in Dafny

To view a full example of how to use the parser combinator library,
especially how to define a recursive parser that is guaranteed to terminate,
please refer to the file `exampleArithmetic.dfy`, which parses
an arithmetic expression.

To get started, first you need to import the parser, I recommend:

```
include "parser.dfy"
import opened Parsers
import ParserEngine
```


Then, define a class that extends `ParserEngine.Engine` and defines
the input string at the same time:

```
  class MyParserEngine extends ParserEngine.Engine {
    constructor(input: string) {
      this.input := input;
    }
  }
```

A parser is a partial function that takes a position and returns a `ParseResult`. Errors have two levels, recoverable or not.

> ```
> type Parser<+T> = nat --> ParseResult<T>
> 
> datatype ParseResult<+T> =
>   | PFailure(level: FailureLevel, message: string, pos: nat)
>   | PSuccess(pos: nat, t: T)
> 
> datatype FailureLevel = Error | Recoverable
> ```

In this class, you can define parsers yourself, or use building blocks.
For example,

```
  function method ParseId?(): Parser<ID>
  {
    While?((pos: nat) requires pos <= |input| =>
      pos < |input| && input[pos] in "azertyuiopqsdfghjklmwxcvbnAZERTYUIOPQSDFGHJKLMWXCVBN_7894561230"
    )
  }
  
  function method ParseId(): Parser<ID>
  {
    Or(ParseId?(), Fail("Expected identifier", Error))
  }
  
  function method ParseField(): Parser<FieldDeclaration>
  {
    Bind(Concat(ParseId(), ConcatR(Const(":"), ParseId())),
        (result: (ID, ID), newPos: nat) => Succeed(Field(result.0, result.1)))
  }
  // It's the same as using Map() instead of Bind(), and removing the "Succeed(" and the `newPos` parameter)
  
  datatype FieldDeclaration = Field(name: ID, value: ID)
```

To invoke your function, define a main method like this:

```

method Main() {
  var content = "happy:code";
  
  var t := new MyParserEngine(content);
  var parseResult := t.ParseField()(0);
  if parseResult.PFailure? {
    t.ReportError(parseResult); // Nice error reporting message with quoting the line and position of failure, along with the message
    return;
  }
  var result := parseResult.t;
  print result;
}
```


