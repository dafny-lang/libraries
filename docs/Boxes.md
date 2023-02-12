
## The `Boxes` module {#sec-boxes}

A _Box_ datatype is one whose values can hold either a success indication, optionally along with a value, or a failure indication, optionally with error information.
These are particularly useful with Dafny's abrupt-termination-on-failure `:-` operator.

Any user datatype can serve this purpose, as long as it has an `IsFailure?` predicate 
(in which case it is known as a [_failure-compatible_](https://dafny.org/latest/DafnyRef/DafyRef#TODO) type --- an FC-type). 
In this module Dafny defines three such types, illustrates them with examples, and then describes 
how they can be used in a system where different parts of the system use different FC-types.

The three types are
- `Option<R>` - which is either `Some` with a value of type `T` or a `None` with no information
- `Outcome<E>` - which is either `Pass` with no informatino or `Fail` with an error value of type `E` (often a `string`) 
- `Result<R,E>` - which is either `Success` with a value of type `R` or `Failure` with error value of type `E` (often a `string`)

These are common programming idioms. The main complication comes when they are mixed in the same program.

### Option

Consider this routine that looks for a value in a sequence, beginning at position k, returning its index:
```dafny
import opened Dafny.Boxes
function Find<T(==)>(s: seq<T>, k: int, value: T): (r: Option<int>)
  requires 0 <= k <= |s|
  ensures  r.Some? ==> s[r.???] == value;
  ensures  r.None? ==> forall i | k <= i < |s| :: s[i] != value
{
  if k >= |s| then None else if s[k] == value then Some(k) else Find(s, k+1, value)
}
```

It could be used in a method like this

```dafny
method m(s: seq<int>) returns (r: Option<int>) {
  var value: int;
  // do various calculations
  var index: int :- Find(s, 0, value);
  // more calculations
  return Some(value);
}
```

You could just capture the result of find using `:=` in a `Option<int>` variable and inspect it. But if the `None` condition is 
generally a rare error, it is easy to forget to always check that each operation was successful. Instead, the `:-` changes the 
control flow so that if a `None` value is returned from `Find`, the method immediately aborts, with the output value (which has
the `Option<int>` type) getting that returned value.So this operates something like exceptions.
See the [reference manual](TODO)) for more on the similarities and differences with exceptions.

### Outcome

`Outcome` is a variation on these boxed types in which we mostly just care whether the operations succeeded or failed.
It has no place to carry a value, just information about the error. 

This datatype is most useful when used with methods with multiple return values.
Then the first return value can be an `Outcome` to indicate success or failure, with the other outputs returning 
appropriate values in the success situation.

For example, if we have this method
```dafny
method FindAllMatches<T(==)(s: seq<T>, value: T) returns (status: Outcome<string>, matches: seq<int>)
```
we can call it as
```dafny
var matches :- FindAllMatches(s, value);
```

Notice that there is no left-hand-side for the first out-parameter. It does not carry a value: if the value is a Fail, the control
flow will abruptly return; if is is a Pass, the first out-parameter is then discarded and the second is assigned to the remaining LHS.
An Outcome serves as an automatically-checked erorr mechanism.


### Result

A `Result` carries both a success value and failure information, or two separate, specifiable types. Its use is then very similar to `Option`.

### Combining different FC-types in expressions

The example given for `Option` above is legal Dafny code because the output of the caller method `m` has the same type
(`Option<int>`) as the output of the callee function `Find`. But what if it does not? You may be writing code that generally uses, say, `Result`,
but happens to be using code supplied by someone else that returns an `Outcome`.

When values of these types are used in expressions, the library types offer means to convert among them: each type has instance functions that
convert to values of the other types. For example, we can rewrite the example above this way:

```dafny
import opened Dafny.Boxes

function Find<T(==)>(s: seq<T>, k: int, value: T): (r: Option<int>)
  requires 0 <= k <= |s|
  ensures  r.Some? ==> k <= r.Extract() < |s|
  ensures  r.Some? ==> s[r.Extract()] == value;
  ensures  r.None? ==> forall i | k <= i < |s| :: s[i] != value
  decreases |s| - k
{
  if k >= |s| then None else if s[k] == value then Some(k) else Find(s, k+1, value)
}

method m(s: seq<int>) returns (r: Result<int,string>) {
  var value: int := *;
  // do various calculations
  var index: int :- Find(s, 0, value).ToResult("not found");
  // more calculations
  return Success(value);
}
```

Here we used the `ToResult` function of `Option` to convert the result value to a `Result`. There are similar `ToOutcome` and `ToOption` functions in each type.

But what if we need to convert to some custom FC-type? Each datatype also has a `Map` function that takes a function as an argument, which function is a converter from
one FC-type to another. For example, we could rewrite the above as

```dafny
  var index: int :- Find(s, 0, value).
     Map((o: Option<int>) => match o case Some(v) => Success(v) 
                                     case None => Failure("not found") );
```

### Combining different FC-types in methods

The conversion functions used in the last section work syntactically because we had boxed values that were returned by expressions (function calls), to which the conversion functions could
be applied. When a FC-value is returned by a method there is no place to call such a conversion function: the return value of the method must be captured by either `:=` or `:-`.

For this situation there is one more piece of syntax to make working with boxed values convenient. Suppose `Find` in our example is a method instead of a function. Then we have

```dafny
method m(s: seq<int>) returns (r: Result<int,string>) {
  var value: int := *;
  // do various calculations
  var f = (o: Option<int>) => match o case Some(v) => Success(v) 
                                      case None => Failure("not found")
  var index: int :- {:convert f} Find(s, 0, value);
  // more calculations
  return Success(value);
}
```

Writing this code perhaps does not save much over just capturing the result of `Find` with `:=`.
However, (a) if `f` is needed repeatedly, it can be defined once and used many times and (b) it allows us to continue to use the `:-` operator to enable a uniform approach to error handling.
