include "../Wrappers.dfy"

module Relations.Comparison {
    import opened Wrappers

  datatype CompResult = Lt | Eq | Gt {
    function method Flip(): CompResult {
      match this
        case Lt => Gt
        case Eq => Eq
        case Gt => Lt
    }

    const Le? := this != Gt
    const Ge? := this != Lt

    static function method ComputeTransitivity(c0: CompResult, c1: CompResult): Option<CompResult> {
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

  datatype Comparison<!T> = Comparison(cmp: (T, T) -> CompResult) {
    function method Compare(t0: T, t1: T): CompResult {
      cmp(t0, t1)
    }

    predicate Complete??(t0: T, t1: T) {
      cmp(t0, t1) == cmp(t1, t0).Flip()
    }

    predicate Antisymmetric??(t0: T, t1: T) {
      cmp(t0, t1) == Eq ==> t0 == t1
    }

    predicate Transitive??(t0: T, t1: T, t2: T) {
      cmp(t0, t1).Le? && cmp(t1, t2).Le? ==> cmp(t0, t2).Le?
    }

    predicate Reflexive??(t0: T) {
      cmp(t0, t0) == Eq
    }

    lemma AlwaysReflexive(t0: T)
      requires Complete??(t0, t0)
      ensures Reflexive??(t0)
    {}

    lemma PreciselyTransitive'(t0: T, t1: T, t2: T)
      requires Complete??(t0, t1) && Complete??(t0, t2) && Complete??(t1, t2)
      requires Antisymmetric??(t0, t1) && Antisymmetric??(t0, t2) && Antisymmetric??(t1, t2)
      requires Transitive??(t0, t1, t2) && Transitive??(t1, t2, t0)
      requires cmp(t0, t1).Le? && cmp(t1, t2).Le?
      ensures CompResult.ComputeTransitivity(cmp(t0, t1), cmp(t1, t2)) == Some(cmp(t0, t2))
    {}

    lemma PreciselyTransitive(t0: T, t1: T, t2: T)
      requires Reflexive??(t0) && Reflexive??(t1) && Reflexive??(t2)
      requires Complete??(t0, t1) && Complete??(t0, t2) && Complete??(t1, t2)
      requires Antisymmetric??(t0, t1) && Antisymmetric??(t0, t2) && Antisymmetric??(t1, t2)
      requires Transitive??(t0, t1, t2) && Transitive??(t1, t2, t0)
      requires Transitive??(t2, t1, t0) && Transitive??(t1, t0, t2)
      ensures match CompResult.ComputeTransitivity(cmp(t0, t1), cmp(t1, t2))
        case Some(c12) => c12 == cmp(t0, t2)
        case None => true
    {
      match (cmp(t0, t1), cmp(t1, t2))
        case (Lt, Lt) | (Lt, Eq) | (Eq, Lt) | (Eq, Eq) =>
          PreciselyTransitive'(t0, t1, t2);
        case (Eq, Gt) | (Gt, Eq) | (Gt, Gt) =>
          PreciselyTransitive'(t2, t1, t0);
        case (Lt, Gt) | (Gt, Lt) =>
    }

    predicate Complete?(ts: seq<T>) {
      forall t0, t1 | t0 in ts && t1 in ts :: Complete??(t0, t1)
    }

    predicate Antisymmetric?(ts: seq<T>) {
      forall t0, t1 | t0 in ts && t1 in ts :: Antisymmetric??(t0, t1)
    }

    predicate Transitive?(ts: seq<T>) {
      forall t0, t1, t2 | t0 in ts && t1 in ts && t2 in ts :: Transitive??(t0, t1, t2)
    }

    predicate {:opaque} Valid?(ts: seq<T>) {
      Complete?(ts) && /* Antisymmetric?(ts) && */ Transitive?(ts)
    }

    predicate {:opaque} Total?(ts: seq<T>) {
      Complete?(ts) && Antisymmetric?(ts) && Transitive?(ts)
    }

    lemma TotalValid(ts: seq<T>)
      ensures Total?(ts) ==> Valid?(ts)
    {
      reveal Total?();
      reveal Valid?();
    }

    predicate method SortedBy<T>(a: seq<T>,compare: (T, T) -> CompResult)
    {
        forall i, j | 0 <= i < j < |a| :: compare(a[i],a[j]).Lt?
    }

    lemma LemmaNewFirstElementStillSortedBy<T>(x: T, s: seq<T>,  compare: (T, T) -> CompResult) 
        requires SortedBy(s, compare)
        requires |s| == 0 || compare(x,s[0]).Lt?
    {}  
  }
}