
include "Helpers.dfy"

module Relations { 
    export 
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering
    provides Helpers

    import opened Helpers

    predicate Reflexive<T(!new)>(R: (T, T) -> bool) 
    {
        forall x :: R(x, x)
    }

    predicate AntiSymmetric<T(!new)>(R: (T, T) -> bool) 
    {
        forall x, y :: R(x, y) && R(y, x) ==> x == y
    }

    predicate Connected<T(!new)>(R: (T, T) -> bool) 
    {
        forall x, y :: R(x, y) || R(y, x)
    }

    predicate TotalOrdering<T(!new)>(R: (T, T) -> bool) 
    {
    && Reflexive(R)
    && AntiSymmetric(R)
    && Helpers.Transitive(R)
    && Connected(R)
    }  

}