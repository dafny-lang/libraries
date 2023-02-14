include "Instance.dfy"
include "Theory.dfy"
	
module SolutionBasicUsing {

	import opened Base
	import opened SolutionBasicInstance
	import opened SolutionBasicTheory

	import opened MyInt
	
	lemma MyIntZeroIdempotent()
		ensures add(zero(),zero()) == zero()
	{
		MyIntIsMonoid();
		NeutralIdempotent(add,zero());
	}
	
}

module SolutionLessBasicUsing {

	import opened Base
	import opened SolutionLessBasicInstance
	import opened SolutionLessBasicTheory	

	import opened MyInt
	
	lemma MyIntZeroIdempotent()
		ensures add(zero(),zero()) == zero()
	{
		NeutralIdempotent(MyIntInstanceMonoid());
	}
	
}



module SolutionModulesUsing {

	import opened SolutionModulesInstance.IntMonoidOut
	import opened MyIntAuto

	lemma MyIntZeroIdempotent()
		ensures add(zero(),zero()) == zero()
	{	
		NeutralIdempotent();
	}
	
}

module SolutionTraitsUsing {

	import opened Base
	import opened SolutionTraitsInstance

	import opened MyIntAuto

	lemma MyIntZeroIdempotent(M: IntMonoid)
		ensures M.bop(M.e(),M.e()) == M.e()
	{
		M.NeutralIdempotent();
	}
	
}
