module RandomNumberGenerator {
  type RNG
}

abstract module Monad {
  type T<A>

  function Apply<A,B>(f: A -> B): T<A> -> T<B>

  function Return<A>(a: A): T<A>

  function Join<A>(ff: T<T<A>>): T<A>

  function Bind<A,B>(f: T<A>, g: A -> T<B>): T<B> {
    Join(Apply(g)(f))
  }

  function Composition<A,B,C>(f: A -> T<B>, g: B -> T<C>): A -> T<C> {
    (a: A) => Bind(f(a), g)
  }

  function Map<A,B>(f: A -> B): T<A> -> T<B> {
    (g: T<A>) => 
      Bind(g, (a: A) => Return(f(a)))
  }

/*   function Lift<A,B,C>(f: (A, B) -> C): (T<A>, T<B>) -> T<C>

  function Sample<A>(r: RNG, f: T<A>): A

  function Conditional<A>(p: A -> bool, f: T<A>): T<A> */
}

module GiryMonad refines Monad {
  newtype UnitInterval = p: real | 0.0 <= p <= 1.0

  type T<!A> = set<A> -> UnitInterval

  function Apply<A,B>(f: A -> B): T<A> -> T<B> {
    (f: T<A>) =>
      (s: set<B>) => 
        f(set a | f(a) in s)
  }

  function Return<A>(a: A): T<A> {
    (s: set<A>) => if a in s then 1.0 else 0.0
  }

  function Join<A>(ff: T<T<A>>): T<A> {
    (s: set<A>) => f(s)
  }

  function Bind<A,B>(f: T<A>, g: A -> T<B>): T<B> {
    (s: set<B>) => 
  }

  function Strength<A,B>(f: T<A>, b: B): T<(A,B)> {
    (s: set<(A,B)>) => 

  }
}

abstract module UniformDistribution {
  import opened Monad

  function Uniform<A>(xs: seq<A>): T<A>

}

abstract module Dice {
  import opened Monad
  import opened UniformDistribution

  function DiceSum(n: int): T<int>
    requires n >= 0
  {
    match n
      case 0 => Return(0)
      case 1 => Uniform([1,2,3,4,5,6])
      case _ => Lift((x: int, y: int) => x + y)(DiceSum(1), DiceSum(n-1))
  }
}


