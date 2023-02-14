include "Definition.dfy"
include "Theory.dfy"

module MyInt {

	import opened Base
	export provides Base, T, zero, add, associative, neutral
		
	type T(!new) = int

	// Problems with constants
	//const zero: T := 0

	function method zero(): T {
		0
	}
	
	function method add(s1: T, s2: T): T {
		s1 + s2
	}

	lemma associative()
		ensures Base.associative(add)
	{
	}

	lemma neutral()
		ensures Base.neutral(add,zero())
	{
	}
		
}
	
module SolutionBasicInstance {

	import opened Base
	import opened SolutionBasic

	import opened MyInt
	
	lemma MyIntIsMonoid()
		ensures Monoid(add,zero())
	{
		MyInt.associative();
		MyInt.neutral();
	}

}

module SolutionLessBasicInstance {

	import opened Base
	import opened SolutionLessBasic

	import opened MyInt

	function MyIntInstanceMonoid(): Monoid<MyInt.T>
	{
		MyInt.associative();
		MyInt.neutral();
		mkMonoid(add,zero())
	}
	
}

module MyIntAuto {

	import opened Base
	export provides Base, T, zero, add, associative, neutral
		
	type T(0) = int

	//const zero: T := 0

	function method zero(): T {
		0
	}
		
	function method add(s1: T, s2: T): T {
		s1 + s2
	}

	lemma associative()
		ensures Base.associative(add)
	{
	}

	lemma neutral()
		ensures Base.neutral(add,zero())
	{
	}
		
}

module SolutionModulesInstance {

	import opened Base
	import opened SolutionModules

	module IntMonoid refines SolutionModules.Monoid {

		import opened MyIntAuto
		
		type T(0) = MyIntAuto.T

		const bop := add

		const e := zero()

		lemma associative()
			ensures Base.associative(bop)
		{
			MyIntAuto.associative();
		}

		lemma neutral()
			ensures Base.neutral(bop,e)
		{
			MyIntAuto.neutral();
		}
			
	}
	
}

module SolutionTraitsInstance {

	import opened Base
	import opened SolutionTraitsAlt

	import opened MyIntAuto

	import opened SolutionTraitsTheory_In

	class IntMonoid extends Monoid<MyIntAuto.T>, NeutralIdempotent<MyIntAuto.T> {

		function bop(x: T,y: T): T {
			add(x,y)
		}

		function e(): T {
			zero()
		}

		lemma associative()
			ensures forall x, y, z: T :: bop(x,bop(y,z)) == bop(bop(x,y),z)
		{
			MyIntAuto.associative();
		}

		lemma neutral()
			ensures forall x: T :: bop(e(),x) == x == bop(x,e())
		{
			MyIntAuto.neutral();
		}
			
	}
	
}
