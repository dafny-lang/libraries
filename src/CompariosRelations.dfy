include "Helpers.dfy"

module Relations.ComparisonsRelation { 

    export 
    reveals Reflexive, AntiSymmetric, Connected, TotalOrdering

    import opened Helpers.Comparison

    predicate Reflexive<T(!new)>(R: (T, T) -> CompResult) 
    {
        forall x :: R(x, x)
    }

    predicate AntiSymmetric<T(!new)>(R: (T, T) -> CompResult) 
    {
        forall x, y :: R(x, y) && R(y, x) ==> x == y
    }

    predicate Connected<T(!new)>(R: (T, T) -> CompResult) 
    {
        forall x, y :: R(x, y) || R(y, x)
    }

    predicate TotalOrdering<T(!new)>(R: (T, T) -> CompResult) 
    {
    && Reflexive(R)
    && AntiSymmetric(R)
    && Helpers.Transitive(R)
    && Connected(R)
    }  
}