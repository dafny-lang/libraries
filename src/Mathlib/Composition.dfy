include "Definition.dfy"

module SolutionBasicComposition {

	import opened Base
	
	predicate UnitalMagma<T(!new)>(bop: BinaryOperator, e: T) {
		neutral(bop,e)
	}

	predicate SemiGroup<T(!new)>(bop: BinaryOperator) {
		associative(bop)
	}

	predicate Monoid<T(!new)>(bop: BinaryOperator, e: T) {
		UnitalMagma(bop,e) && SemiGroup(bop)
	}
	
}

module SolutionLessBasicComposition {

	import opened Base
	
	datatype MagmaSig<!T> = mkMagma(bop: BinaryOperator)

	datatype UnitalMagmaSig<!T> = mkUnitalMagma(S: MagmaSig, e: T)
		
	predicate UnitalMagmaTheory<T(!new)>(S: UnitalMagmaSig) {
		neutral(S.S.bop,S.e)
	}

	type UnitalMagma<!T(!new)> = S: UnitalMagmaSig | UnitalMagmaTheory(S) witness *

	predicate SemiGroupTheory<T(!new)>(S: MagmaSig) {
		associative(S.bop)
	}

	type SemiGroup<!T(!new)> = S: MagmaSig | SemiGroupTheory(S) witness *

	predicate MonoidTheory<T(!new)>(S: UnitalMagmaSig) {
		SemiGroupTheory(S.S) && UnitalMagmaTheory(S)
	}
		
	type Monoid<!T(!new)> = S: UnitalMagmaSig | MonoidTheory(S) witness *
		
}

module SolutionModuleComposition {
	
	module Magma {

		import opened Base
		
		type T(0)
		const bop: BinaryOperator<T>

	}

	module UnitalMagma {

		import opened Magma
		
		const e: T

		lemma neutral()
			ensures Base.neutral(bop,e)
			
	}

	module SemiGroup {

		import opened Magma
		
		lemma associative()
			ensures Base.associative(bop)

	}

	module Monoid {

		import opened UnitalMagma
		import opened SemiGroup
		
	}
	
}

module SolutionTraitComposition {

	import opened Base
	
	trait Magma<T(0)> {

		const bop: BinaryOperator<T>
		
	}

	trait UnitalMagma<T(0)> extends Magma<T> {

		const e: T

		lemma neutral()
			ensures Base.neutral(bop,e)

	}

	trait SemiGroup<T(0)> extends Magma<T> {

		lemma associative()
			ensures Base.associative(bop)

	}
	
	trait Monoid<T(0)> extends UnitalMagma<T>, SemiGroup<T> {		
	}
	
}



