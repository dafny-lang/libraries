# Dafny Standard Library Style Guide

This style guide provides coding conventions for the Dafny Standard Library code.

*This documentation is a modification of the Dafny Style Guide and is still in progress.*

## Naming Convention

Any **variables** are named with `camelCase`.
```
  var minValue := 1;
  var cipherMessage := "Hello World";
```

Any **lemmas**, **predicates**, **functions**, **methods**, **classes**, **modules**, **datatypes**, and **newtypes**
are named with `PascalCase`.
```
  method FindIndex(arr: seq<int>, k: int)
    ...
``` 
        
The **lemma** keyword indicates a ghost method used for proof purposes. Any **lemma** names should be prefixed with `Lemma`.
```
  lemma LemmaValueIsInIndex(arr: seq<int>, k: int)
    ...
```
        
Any static or global **constants** are named with `UPPERCASE_WITH_UNDERSCORES`.
```
  static const MONTHS_IN_A_YEAR := 12
```
    
### Method Prefix

Avoid redundant names when variables or methods are in a class/module.
```
class Integer {

  // The following method converts the given integer
  // to a string.
  //
  // this method name can be simplified to ToString()
  // so that the method call is Integer.ToString(i)
  // instead of Integer.IntegerToString(i).

  // YES
  method ToString(i: int) returns (s: string)
    ...

  // NO
  method IntegerToString(i: int) returns (s: string)
    ...
  }
```
## Code Layout

### Braces

Opening braces for **modules**, **classes**, **datatypes**, **if** statements go on the same line.
```
module M {
  ...
}
```

Opening braces for **methods**, **lemmas**, **functions**, and **predicates** go on a new line.

```
module M {
  ...
  method Met(i: int) returns (j: int)
    requires i % 2 == 0
    ensures j > 10
  {
    ...
  }
}
```

### Imports

By default, import modules without opening them.
```
  import Coffee
  ...
```

However, if some members of a module are used very frequently, import it using `opened`:
```
  import opened Donut
  ...
```
    
When a file uses two modules and both of them define a method of the same name, do not import them `opened`.

```
import MyModule
import YourModule
...
method MyMethod() 
{
  MyModule.foo();
  YourModule.foo();
}
```

In this case, if you want to shorten the module name, import it with a shorthand name.

```
import M = MyModuleWithACumbersomeName
import Y = YourModuleWithACumbersomeName
...
method MyMethod() 
{
  M.Foo();
  Y.Foo();
}
```

Common imports, such as `StandardLibrary` and `Native`, should be grouped together, followed by custom module imports with a blank line in-between.

```
import opened StandardLibrary
import opened Native

import opened Donut
import Coffee
```

Although not required, it’s recommended to keep the order of `imports` and `include`s alphabetical, except when it makes more sense to group them logically.

## Indentation and Line Breaks

### Tabs or Spaces?

Use 2 spaces for each indentation.

### Maximum Character Limit

Although there is no strict requirement, it is generally recommended to have a maximum of 120 characters per line.

### Newlines

Use newlines between sequential functions, methods, predicates, and lemmas to increase readability.

End each file with a newline.

### Functions, Methods, Predicates, and Lemmas

Every Dafny method has the following signature.

```
method {:<attributes>} MethodName(param1: Type, param2: Type) returns (ret: Type)
  requires P()
  modifies param2
  ensures Q()
  decreases param1
```

When possible, put` MethodName` and the keyword `returns` on the same line, as `returns` is distinct from other method specification clauses, such as `requires`, `modifies`, `ensures`, and `decreases`, which should appear in this order. Each method specification clause should be on a separate line, indented.

In case the Method signature is too long, we can break it down.

```
method {:<attributes>} MethodName(param1: Type, param2: Type,
    param3: Type, param4: Type, param5: Type)
  returns (ret1: Type, ret2: Type, ret3: Type, ret4: Type,
    ret5: Type)
  requires P1()
  requires P2()
  requires P3()
  modifies param2
  modifies param3
  ensures Q1()
  ensures Q2()
  decreases param1
````

Multiple `requires` or `ensures` can be combined into one:

```
requires
  && P1()
  && P2()
  && P3()
````

The same rules apply to `function`, `predicate`, and `lemma` definitions.

## Content Conventions

### Order

Functions, predicates, and methods within a file should be sorted topologically, meaning that everything `method M` depends on should be above `M` in the file.

```
function MyFunction(a: int): int
{
  ...
}
method MyMethod(i: int) 
{
  ...
  return MyFunction(i);
}
```

### Predicates

Predicates should be used instead of functions that return a Boolean value. 

```
// YES
predicate Foo() 
{
  ...
} 

// NO
function Foo(): bool 
{
  ...
}
```

### Lemmas

When writing inductive proofs, contributors are strongly encouraged to
make the base case explicit.

```
// YES
lemma LemmaMinOfConcat(a: seq<int>, b: seq<int>)
  requires 0 < |a| && 0 < |b|
  ensures Min(a+b) <= Min(a)
  ensures Min(a+b) <= Min(b)
  ensures Min(a+b) == Min(a) || Min(a+b) == Min(b)
{
  if |a| == 1 {
  } else {
    assert a[1..] + b == (a + b)[1..];
    LemmaMinOfConcat(a[1..], b);
  }
} 

// NO
lemma LemmaMinOfConcat(a: seq<int>, b: seq<int>)
  requires 0 < |a| && 0 < |b|
  ensures Min(a+b) <= Min(a)
  ensures Min(a+b) <= Min(b)
  ensures Min(a+b) == Min(a) || Min(a+b) == Min(b)
{
  if |a| > 1 {
    assert a[1..] + b == (a + b)[1..];
    LemmaMinOfConcat(a[1..], b);
  }
}
```

## Things to Avoid

### Parentheses

In many cases, Dafny does not require parentheses around expressions. Here are some examples.

•	If-Else-While Statements

```
// YES
var i := 1;
while i < 10 {
  ...
  if 1 < i {
      ...
  }
  ...
}

// NO
var i := 1;
while (i < 10) {
  ...
  if (1 < i) {
      ...
  }
  ...
}
```

•	Statements That Take Expression Arguments

```
// YES
assert x < 100;
print x;

// NO
assert(x < 100);
print(x);
```

•	Simple Boolean/Arithmetic Expressions

```
// YES
method Collatz(num: nat)
  decreases *
{
  var n := num;
  while 1 < n
    decreases *
  {
    n := if n % 2 == 0 then n / 2 else n * 3 + 1;
  }
}

// NO
method Collatz(num: nat)
  decreases *
{
  var n := num;
  while (1 < n) // unnecessary parentheses
    decreases *
  {
    n := if ((n % 2) == 0) then (n / 2) else ((n * 3) + 1); // unnecessary parentheses
  }
}
```

### Whitespace

Avoid unnecessary whitespace inside expressions.

#### Type Declaration

A type declaration should have a form of `variableName: variableType`.

```
// YES
const one: int := 1
class {:extern} Util {
  var {:extern} Exception: System.String
}

// NO
const one : int := 1 // unnecessary whitespace
class {:extern} Util {
  var {:extern} Exception : System.String // unnecessary whitespace
}
```

If the type can be inferred by Dafny, leave it out, unless you think it provides useful documentation in the program. So, constant `one` above is better declared as

  const one := 1

#### Function, Method, Predicate, and Lemma Declaration

The `function`, `method`, `predicate`, and `lemma` definitions should have the form `FunctionName(parameterName: parameterType, ...)`.

```
// YES
function method Foo<int>(i: int): int

// NO
function method Foo<int> (i : int) : int // unnecessary whitespace
Avoid too little or too much whitespace that reduces the overall readability.
// YES
lemma LemmaMyLemma<A, B>(x: seq<seq<A>>, y: B) {
  ...
}

// NO
lemma LemmaMyLemma <A,B> ( x : seq<seq<A>> , y :B){
  ...
}
```

### Triggers

The `{:trigger}` annotations used in the standard library are an advanced topic and should not be needed when starting out on Dafny projects. For some background on quantifiers and triggers, check [this](https://github.com/dafny-lang/dafny/wiki/FAQ#how-does-dafny-handle-quantifiers-ive-heard-about-triggers-what-are-those) out. 
