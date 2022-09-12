module Relations { 

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
    && Transitive(R)
    && Connected(R)
    }  

    /*
    * To be _trichotomous_ means that for any two `x` and `y`,
    * EXACTLY one of the following three conditions holds:
    *   - less(x, y)
    *   - x == y
    *   - less(y, x)
    * Note that being trichotomous implies being irreflexive.
    */

    predicate Trichotomous<T(!new)>(less: (T, T) -> bool) 
    {
        (forall x, y :: less(x, y) || x == y || less(y, x)) &&  // at least one of the three
        (forall x, y :: less(x, y) && less(y, x) ==> false) &&  // not both of the less's
        (forall x, y :: less(x, y) ==> x != y)  // not a less and the equality
    }

    predicate Transitive<T(!new)>(R: (T, T) -> bool) 
    {
        forall x, y, z :: R(x, y) && R(y, z) ==> R(x, z)
    }
}