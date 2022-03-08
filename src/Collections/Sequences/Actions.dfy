// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Original: Copyright (c) 2020 Secure Foundations Lab
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../Wrappers.dfy"
include "../../Action.dfy"
include "Seq.dfy"

module Actions {
  import opened Wrappers
  import opened A = Action
  import opened Seq

  method Map<A, R>(
    action: Action<A, R>,
    s: seq<A>
  )
    returns (res: seq<R>)
    requires forall i | i in s :: action.Requires(i)
    ensures |s| == |res|
    ensures
      forall i ::
        && 0 <= i < |s|
      ==>
        action.Ensures(s[i], res[i])
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j ::
        && 0 <= j < i
      ==>
        action.Ensures(s[j], rs[j])
    {
      var r := action.Invoke(s[i]);
      rs := rs + [r];
    }
    return rs;
  }

  method MapWithResult<A, R, E>(
    action: Action<A, Result<R, E>>,
    s: seq<A>
  )
    returns (res: Result<seq<R>, E>)
    requires forall i | i in s :: action.Requires(i)
    ensures
      res.Success?
    ==>
      |s| == |res.value|
    ensures
      res.Success?
    ==>
        (forall i ::
          && 0 <= i < |s|
        ==>
          action.Ensures(s[i], Success(res.value[i])))
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |rs|
      invariant forall j ::
        && 0 <= j < i
      ==>
        action.Ensures(s[j], Success(rs[j]))
    {
      var maybeR := action.Invoke(s[i]);
      if maybeR.Failure? {
        return Failure(maybeR.error);
      }
      var r := maybeR.value;
      rs := rs + [r];
    }
    return Success(rs);
  }

  method FlatMap<A, R>(
    action: Action<A, seq<R>>,
    s: seq<A>
  )
    // The ghost parts is returned to facilitate
    // threading proof obligations.
    // Idealy, it would be great to remove this
    // and simply prove everything about `res`.
    // However in practice this has proven to be difficult.
    // Given how flexible FlatMap is,
    // there may not be a prcatical general solution.
    returns (res: seq<R>, ghost parts: seq<seq<R>>)
    requires forall i | i in s :: action.Requires(i)
    ensures
      && |s| == |parts|
      && res == Flatten(parts)
      && (forall i :: 0 <= i < |s|
      ==>
        && action.Ensures(s[i], parts[i])
        && multiset(parts[i]) <= multiset(res))
  {
    parts := [];
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j ::
        && 0 <= j < i
      ==>
        && action.Ensures(s[j], parts[j])
        && multiset(parts[j]) <= multiset(rs)
      invariant Flatten(parts) == rs
    {
      var r := action.Invoke(s[i]);
      rs := rs + r;
      LemmaFlattenConcat(parts, [r]);
      parts := parts + [r];
    }
    return rs, parts;
  }

  method FlatMapWithResult<A, R, E>(
    action: Action<A, Result<seq<R>, E>>,
    s: seq<A>
  )
    // The ghost parts is returned to facilitate
    // threading proof obligations.
    // Idealy, it would be great to remove this
    // and simply prove everything about `res`.
    // However in practice this has proven to be difficult.
    // Given how flexible FlatMap is,
    // there may not be a prcatical general solution.
    returns (res: Result<seq<R>, E>, ghost parts: seq<seq<R>>)
    requires forall i | i in s :: action.Requires(i)
    ensures
      res.Success?
    ==>
      && |s| == |parts|
      && res.value == Flatten(parts)
      && (forall i :: 0 <= i < |s|
      ==>
        && action.Ensures(s[i], Success(parts[i]))
        && multiset(parts[i]) <= multiset(res.value)
      )
  {
    parts := [];
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| == |parts|
      invariant forall j ::
        && 0 <= j < i
      ==>
        && action.Ensures(s[j], Success(parts[j]))
        && multiset(parts[j]) <= multiset(rs)
      invariant Flatten(parts) == rs
    {
      var maybeR := action.Invoke(s[i]);
      if maybeR.Failure? {
        return Failure(maybeR.error), parts;
      }
      var r := maybeR.value;
      rs := rs + r;
      LemmaFlattenConcat(parts, [r]);
      parts := parts + [r];
    }
    return Success(rs), parts;
  }

  method Filter<A>(
    action: Action<A, bool>,
    s: seq<A>
  )
    returns (res: seq<A>)
    requires forall i | i in s :: action.Requires(i)
    ensures |s| >= |res|
    ensures
      forall j ::
        j in res
      ==>
        && j in s
        && action.Ensures(j, true)
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j ::
        j in rs
      ==>
        && j in s
        && action.Ensures(j, true)
    {
      var r := action.Invoke(s[i]);
      if r {
        rs := rs + [s[i]];
      }
    }
    return rs;
  }

  method FilterWithResult<A, E>(
    action: Action<A, Result<bool, E>>,
    s: seq<A>
  )
    returns (res: Result<seq<A>, E>)
    requires forall i | i in s :: action.Requires(i)
    ensures
      res.Success?
    ==>
      && |s| >= |res.value|
      && forall j ::
        j in res.value
      ==>
        && j in s
        && action.Ensures(j, Success(true))
  {
    var rs := [];
    for i := 0 to |s|
      invariant |s[..i]| >= |rs|
      invariant forall j ::
        j in rs
      ==>
        && j in s
        && action.Ensures(j, Success(true))
    {
      var maybeR := action.Invoke(s[i]);
      if maybeR.Failure? {
        return Failure(maybeR.error);
      }
      var r := maybeR.value;
      if r {
        rs := rs + [s[i]];
      }
    }
    return Success(rs);
  }

  method ReduceToSuccess<A, B, E>(
    action: Action<A, Result<B, E>>,
    s: seq<A>
  )
    returns (res: Result<B, seq<E>>)
    requires forall i | i in s :: action.Requires(i)
    ensures
      res.Success?
    ==>
      exists a | a in s :: action.Ensures(a, Success(res.value))
  {
    var errors := [];
    for i := 0 to |s| {
      var attempt := action.Invoke(s[i]);
      if attempt.Success? {
        return Success(attempt.value);
      } else {
        errors := errors + [attempt.error];
      }
    }
    return Failure(errors);
  }
}
