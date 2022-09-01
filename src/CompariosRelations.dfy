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
    && Transitive(R)
    && Connected(R)
    }  

        predicate Trichotomous<T(!new)>(less: (T, T) -> CompResult) 
    {
        (forall x, y :: less(x, y) || x == y || less(y, x)) &&  // at least one of the three
        (forall x, y :: less(x, y) && less(y, x) ==> false) &&  // not both of the less's
        (forall x, y :: less(x, y) ==> x != y)  // not a less and the equality
    }

    predicate Transitive<T(!new)>(R: (T, T) -> CompResult) 
    {
        forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z)
    }
}