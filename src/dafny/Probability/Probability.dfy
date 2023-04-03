module RNG {
  type rng = nat -> bool
}

module Hurd {
  import opened RNG

  type Hurd<A> = rng -> (A, rng)

  function Unit<A>(a: A): Hurd<A> {
    (r: rng) => (a, r)
  }

  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (r: rng) =>
      var (a, r') := f(r);
      g(a)(r')
  }

  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    (r: rng) =>
      var (f, r') := ff(r);
      f(r')
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }
}

