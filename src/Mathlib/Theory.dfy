include "Definition.dfy"

module SolutionBasicTheory {

	import opened Base
	import opened SolutionBasic

	lemma NeutralIdempotent<T(!new)>(bop: BinaryOperator, e: T)
		requires Monoid(bop,e)
		ensures bop(e,e) == e
	{
	}
	
}

module SolutionLessBasicTheory {

	import opened Base
	import opened SolutionLessBasic

	lemma NeutralIdempotent<T(!new)>(M: Monoid)
		ensures M.bop(M.e,M.e) == M.e
	{
	}
	
}

abstract module SolutionModulesTheory_Out {

	import M: SolutionModules.Monoid

	lemma NeutralIdempotent()
		ensures M.bop(M.e,M.e) == M.e
	{
		M.neutral(); 
	}
	
}

/* module SolutionModulesTheory_In {

	abstract module MonoidTheory {

		import opened Base
		import opened SolutionModules.Monoid

		
		lemma NeutralIdempotent()
			ensures bop(e,e) == e
		{
			Monoid.neutral(); 
		}

	}
	
} */

module SolutionTraitsTheory_Out {

	import opened Base
	import opened SolutionTraitsAlt

	lemma NeutralIdempotent<T(0)>(M: Monoid)
		ensures M.bop(M.e(),M.e()) == M.e()
	{
		M.neutral();
	}
		
}

module SolutionTraitsTheory_In {

	import opened Base
	import opened SolutionTraitsAlt

	trait {:termination false} NeutralIdempotent<T(0)> extends Monoid<T> {

		lemma NeutralIdempotent()
			ensures bop(e(),e()) == e()
		{
			neutral();
		}
		
	}

}
