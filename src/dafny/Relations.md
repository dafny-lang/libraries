
## The `Relations` module {#sec-relations}

The `Relations` module defines a number of properties of functions.

Properties of binary predicates:
- Reflexive
- Irreflexive
- AntiSymmetric
- Transitive
- Connected
- StronglyConnected
- TotalOrdering
- StrictTotalOrdering

A property of unary functions:
- Injective

Some of these are needed for further reasoning. For example, 
if one wants to sort a sequence by some relation `R`, one must establish that `R` is a _Total Ordering_. 
In fact, that is part of the precondition of the sorting function.

As a simple example, you might define a predicate like this:
```dafny
  const IntLT  := ((i: int, j: int) => (i < j))
```

and then need to proof this lemma to use it in a sorting routine:
```dafny
  lemma IntLTisStrictTotalOrder()
    ensures StrictTotalOrdering(IntLT) {}
```

Fortunately, dafny proofs this without aid.

All these definitions are ghost predicates; they are used as part of proofs rather than in compiled code.