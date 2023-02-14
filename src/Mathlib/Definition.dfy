module Base {

	type BinaryOperator<!T> = (T,T) -> T
		
	predicate associative<T(!new)>(bop: BinaryOperator) {
		forall x, y, z: T :: bop(x,bop(y,z)) == bop(bop(x,y),z)
	}

	predicate neutral<T(!new)>(bop: BinaryOperator, e: T) {
		forall x: T :: bop(e,x) == x == bop(x,e)
	}
		
}

module SolutionBasic {

	import opened Base
	
	predicate Monoid<T(!new)>(bop: BinaryOperator, e: T) {
		associative(bop) && neutral(bop,e)
	}
	
}

module SolutionLessBasic {

	import opened Base

	datatype MonoidSignature<!T> = mkMonoid(bop: BinaryOperator, e: T)

	predicate MonoidTheory<T(!new)>(S: MonoidSignature) {
		associative(S.bop) && neutral(S.bop,S.e)
	}

	type Monoid<!T(!new)> = S: MonoidSignature | MonoidTheory(S) witness *
	
}

module SolutionModules {

	abstract module Monoid {

		import Base

		type T(0)
		const bop: Base.BinaryOperator<T>
		const e: T

		lemma associative()
			ensures Base.associative(bop)

		lemma neutral()
			ensures Base.neutral(bop,e)
		
	}
	
}

module SolutionTraits {

	import Base

	trait {:termination false} Monoid<T(0)> {

		const bop: Base.BinaryOperator<T>
		const e: T

		lemma associative()
			ensures Base.associative(bop)

		lemma neutral()
			ensures Base.neutral(bop,e)

	}

}

module SolutionTraitsAlt {

	trait {:termination false} Monoid<T(0)> {

		function bop(x: T,y: T): T
		function e(): T

		lemma associative()
			ensures forall x, y, z: T :: bop(x,bop(y,z)) == bop(bop(x,y),z)

		lemma neutral()
			ensures forall x: T :: bop(e(),x) == x == bop(x,e())

	}

}
