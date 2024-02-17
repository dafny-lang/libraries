include "Actions.dfy"
include "Enumerators.dfy"

module ActionCombinators {

  import opened Actions
  import opened Wrappers
  import opened Enumerators

  // a.produced == Seq.Map(f, a.consumed)
  method Function<T, R>(f: T --> R)
    returns (a: Action<T, R>)
    ensures fresh(a.Repr)

  method EnumeratorOfSeq(s: seq<T>)
    returns (e: Enumerator<T>)

  // a.k.a. Chain(first, second)
  //
  // To map a function f over the values of an action a: 
  //   Compose(Function(f), a)
  //
  // Or over an enumerator e:
  //   var maybeF := (maybeT: Option<T>) => match maybeT {
  //      case Some(t) => Some(f(t))
  //      case None => None
  //   };
  //   Compose(Function(maybeF), e)
  //
  // To map an Action a over a sequence s:
  //   Collect(Compose(a, EnumeratorOfSeq(s)))
  method Compose<T, V, R>(second: Action<V, R>, first: Action<T, V>)
    returns (composed: Action<T, R>)
    requires second.Repr !! first.Repr

  // Produces Seq.Filter(what a produces, p)
  // a has to be an Enumerator to ensure Invoke() eventually terminates
  method Filter<T>(e: Enumerator<T>, p: T -> bool)
    returns (filtered: Enumerator<T>)

  // Produces Seq.Flatten(Actions.Map(inner, (what outer produces)))
  // inner needs to be an action rather than just a function
  // since enumerators are usually objects that need allocation.
  method Nested<T, V>(outer: Enumerator<V>, inner: Action<V, Enumerator<T>>)
    returns (nested: Enumerator<T>)

  method ForEach(source: Enumerator<T>, sink: Aggregator<T>)

  method Collect(source: Enumerator<T>)
    returns (s: seq<T>)
}