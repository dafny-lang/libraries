// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "Wrappers.dfy"
include "Relations.dfy"
module Comparison {

import opened Wrappers
import opened Relations

  datatype Cmp = Lt | Eq | Gt {
    function method Flip(): Cmp {
      match this
        case Lt => Gt
        case Eq => Eq
        case Gt => Lt
    }

    const Le? := this != Gt
    const Ge? := this != Lt

    static function method ComputeTransitivity(c0: Cmp, c1: Cmp): Option<Cmp> {
      match (c0, c1)
        case (Lt, Lt) => Some(Lt)
        case (Lt, Eq) => Some(Lt)
        case (Lt, Gt) => None
        case (Eq, Lt) => Some(Lt)
        case (Eq, Eq) => Some(Eq)
        case (Eq, Gt) => Some(Gt)
        case (Gt, Lt) => None
        case (Gt, Eq) => Some(Gt)
        case (Gt, Gt) => Some(Gt)
    }
  }
   datatype Comparison<!T> = Comparison(cmp: (T, T) -> Cmp) {
    function method Compare(t0: T, t1: T): Cmp {
      cmp(t0, t1)
    }

     predicate CompleteonPair(t0: T, t1: T) {
      cmp(t0, t1) == cmp(t1, t0).Flip()
    }

    predicate Transitive'(t0: T, t1: T, t2: T) {
      cmp(t0, t1).Le? && cmp(t1, t2).Le? ==> cmp(t0, t2).Le?
    }

    predicate Complete(ts: set<T>) {
      forall t0, t1 | t0 in ts && t1 in ts :: CompleteonPair(t0, t1)
    }

    predicate Transitive(ts: set<T>) {
      forall t0, t1, t2 | t0 in ts && t1 in ts && t2 in ts :: Transitive'(t0, t1, t2)
    }

    predicate {:opaque} Valid(ts: set<T>) {
      Complete(ts) && Transitive(ts)
    }

    predicate Sorted(sq: seq<T>) {
      forall i, j | 0 <= i < j < |sq| :: cmp(sq[i], sq[j]).Le?
    }

    predicate Reflexive'(t0: T) {
      cmp(t0, t0) == Eq
    }

    lemma AlwaysReflexive(t0: T)
      requires CompleteonPair(t0, t0)
      ensures Reflexive'(t0)
    {}

    predicate {:opaque} Striped(sq: seq<T>, pivot: T, lo: int, left: int, mid: int, right: int, hi: int)
      requires 0 <= lo <= left <= mid <= right <= hi <= |sq|
    {
      && (forall i | lo    <= i < left :: cmp(sq[i], pivot).Lt?)
      && (forall i | left  <= i < mid  :: cmp(sq[i], pivot).Eq?)
      && (forall i | right <= i < hi   :: cmp(sq[i], pivot).Gt?)
    }

    lemma SortedConcat(sq0: seq<T>, sq1: seq<T>)
      requires Sorted(sq0)
      requires Sorted(sq1)
      requires forall i, j | 0 <= i < |sq0| && 0 <= j < |sq1| :: cmp(sq0[i], sq1[j]).Le?
      ensures Sorted(sq0 + sq1)
    {}

    }
  }