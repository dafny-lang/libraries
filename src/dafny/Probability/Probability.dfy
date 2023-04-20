module RNG {
  type rng = nat -> bool

  // Definition 14
  function Head(s: rng): bool {
    s(0)
  }

  // Definition 14
  function Tail(s: rng): rng {
    (n: nat) => s(n+1)
  }

  // Definition 14
  function Cons(a: bool, s: rng, n: nat): bool {
    if n == 0 then 
      a 
    else 
      s(n-1)
  }

  // Definition 14
  function Take(n: nat, s: rng): seq<bool> {
    if n == 0 then
      []
    else
      [Head(s)] + Take(n-1, Tail(s))
  }

  // Definition 14
  function Drop(n: nat, s: rng): rng {
    if n == 0 then
      s
    else
      Drop(n-1, Tail(s))
  }

  // Definition 14
  function Dest(s: rng): (bool, rng) {
    (Head(s), Tail(s))
  }

  // Definition 15
  ghost function Iter<A>(h: A -> bool, t: A -> A, x: A): rng {
    assume false;
    (n: nat) => Cons(h(x), Iter(h, t, t(x)), n)
  }

  // Definition 16
  ghost function Mirror(s: rng): rng {
    (n: nat) => Cons(!Head(s), Tail(s), n)
  }

  // Definition 17
  ghost function PrefixSet(l: seq<bool>): iset<rng> {
    iset s: rng | Take(|l|, s) == l
  }

  // Definition 17
  ghost function PrefixSeq(l: seq<bool>, a: bool): seq<bool> {
    if l == [] then
      [a]
    else
      [l[0]] + PrefixSeq(l[1..], a)
  }

  // Equation (2.45)
  lemma LemmaHdCons(h: bool, t: rng) 
    ensures Head((n: nat) => Cons(h, t, n)) == h
  {}

  // Equation (2.46)
  lemma LemmaTlCons(h: bool, t: rng, n: nat)
    ensures Tail((n: nat) => Cons(h, t, n))(n) == t(n)
  {}

  // Equation (2.47), (2.48)
  lemma LemmaHdtlDecomp(s: rng, n: nat) returns (x: (bool, rng))
    ensures s(n) == Cons(x.0, x.1, n)
  {
    x := (Head(s), Tail(s));
  }

  // Equation (2.50)
  lemma LemmaMirrorIdempotent(s: rng, n: nat) 
    ensures Mirror(Mirror(s))(n) == s(n)
  {}

  // Equation (2.51)
  lemma LemmaTlMirror(s: rng, n: nat)
    ensures Tail(Mirror(s))(n) == Tail(s)(n)
  {}
}

module HurdMonad {
  import opened RNG

  // Definition 29
  type Hurd<A> = rng -> (A, rng)

  // Definition 29
  function Unit<A>(a: A): Hurd<A> {
    (s: rng) => (a, s)
  }

  // Definition 29
  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (s: rng) =>
      var (a, s') := f(s);
      g(a)(s')
  }
  
  // Definition 53
  function Map<A,B>(f: A -> B, m: Hurd<A>): Hurd<B> {
    Bind(m, (a: A) => Unit(f(a)))
  }
  
  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    (s: rng) =>
      var (f, s') := ff(s);
      f(s')
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  lemma LemmaCompositionAssociative<A,B,C,D>(f: A -> Hurd<B>, g: B -> Hurd<C>, h: C -> Hurd<D>, a: A, s: rng) 
    ensures Composition(Composition(f, g), h)(a)(s) == Composition(f, Composition(g, h))(a)(s)
  {
    var (b, t) := f(a)(s);
    var (c, u) := g(b)(t);
    calc {
      Composition(Composition(f, g), h)(a)(s);
    ==
      h(c)(u);
    ==
      Composition(f, Composition(g, h))(a)(s);
    }
  }

  lemma LemmaUnitalityJoin<A>(f: Hurd<A>, s: rng)
    ensures Join(Map(Unit, f))(s) == Join(Unit(f))(s)
  {
    var (a, t) := f(s);
    calc {
      Join(Unit(f))(s);
    ==
      (a, t);
    ==
      Join(Map(Unit, f))(s);
    }
  }
  
  lemma LemmaAssociativityJoin<A>(fff: Hurd<Hurd<Hurd<A>>>, s: rng)
    ensures Join(Map(Join, fff))(s) == Join(Join(fff))(s)
  {
    var (ff, t) := fff(s);
    var (f, u) := ff(t);
    calc {
      Join(Map(Join, fff))(s);
    ==
      f(u);
    ==
      Join(Join(fff))(s);
    }
  }
}

module Probability {
  ghost function EmptyIset<T(!new)>(): iset<T> {
    iset x: T | false
  }

  // Definition 4
  ghost predicate IsAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>) {
    && (forall e | e in event_space :: e <= sample_space)
    && EmptyIset() in event_space
    && (forall e | e in event_space :: (sample_space - e) in event_space)
    && (forall e1, e2 | e1 in event_space && e2 in event_space :: e1 + e2 in event_space)
  }    

  lemma LemmaSampleSpaceInAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>)
    requires IsAlgebra(event_space, sample_space)
    ensures sample_space in event_space
  {
    assert sample_space == sample_space - EmptyIset();
  }

  ghost function CountableUnion<T>(f: nat -> iset<T>, i: nat := 0): iset<T> {
    assume false;
    f(i) + CountableUnion(f, i+1)
  }

  ghost function CountableSum(f: nat -> real, i: nat := 0): real {
    assume false;
    f(i) + CountableSum(f, i+1)
  }

  // Definition 4
  ghost predicate IsSigmaAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>) {
    && IsAlgebra(event_space, sample_space)
    && forall f: nat -> iset<T> | (forall n :: f(n) in event_space) :: CountableUnion(f) in event_space 
  }

  datatype MeasurableSpaceStructure<!T> = Pair(event_space: iset<iset<T>>, sample_space: iset<T>)

  type MeasurableSpace<!T(!new)> = pair: MeasurableSpaceStructure | IsSigmaAlgebra(pair.event_space, pair.sample_space) witness *

  // Definition 5
  ghost predicate IsPositive<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
    && mu(EmptyIset()) == 0.0
    && forall e | e in ms.event_space :: 0.0 <= mu(e)
  }

  // Definition 5
  ghost predicate IsIncreasing<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
    forall e1, e2 | e1 in ms.event_space && e2 in ms.event_space && e1 <= e2 :: mu(e1) <= mu(e2)
  }

  // Definition 5
  ghost predicate IsAdditive<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
    forall e1, e2 | e1 in ms.event_space && e2 in ms.event_space && e1 * e2 == EmptyIset() :: mu(e1) + mu(e2) == mu(e1 + e2)
  }

  // Definition 5
  ghost predicate IsCountablyAdditive<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
    forall f: nat -> iset<T> | (forall n :: f(n) in ms.event_space) && (forall m, n | m != n :: f(m) * f(n) == EmptyIset()) && (CountableUnion(f) in ms.event_space) :: (CountableSum((n: nat) => mu(f(n))) == mu(CountableUnion(f)))
  }

  // Equation (2.18)
  lemma {:axiom} LemmaPosCountAddImpliesAdd<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real)
    requires IsPositive(ms, mu)
    requires IsCountablyAdditive(ms, mu)
    ensures IsAdditive(ms, mu)
  
  // Definition 6
  datatype MeasureSpaceStructure<!T(!new)> = Pair(ms: MeasurableSpace, mu : iset<T> -> real) 
  type MeasureSpace<!T(!new)> = pair: MeasureSpaceStructure | IsPositive(pair.ms, pair.mu) && IsCountablyAdditive(pair.ms, pair.mu) witness *

  ghost function PreImageOf<S(!new),T>(f: S -> T, domain: iset<S>, b: iset<T>): (a: iset<S>)
    ensures a <= domain
    ensures forall x | x in a :: f(x) in b
  {
    iset x | x in domain && f(x) in b
  }

  // Definition 9
  ghost predicate IsMeasurableFunction<S(!new),T(!new)>(ms1: MeasurableSpace<S>, ms2: MeasurableSpace<T>, f: S -> T) {
    forall e | e in ms2.event_space :: PreImageOf(f, ms1.sample_space, e) in ms1.event_space
  }

  // Definition 12
  type ProbabilitySpace<!T(!new)> = ms: MeasureSpace | ms.mu(ms.ms.sample_space) == 1.0 witness *

  // Definition 13
  ghost predicate Independent<T(!new)>(ms: MeasureSpace<T>, e1: iset<T>, e2: iset<T>) {
    && e1 in ms.ms.event_space
    && e2 in ms.ms.event_space
    && ms.mu(e1 * e2) == ms.mu(e1) * ms.mu(e2)
  }

  // Definition 13 
  ghost predicate IndependentFamilies<T(!new)>(ms: MeasureSpace<T>, a: iset<iset<T>>, b: iset<iset<T>>) {
    forall e1, e2 | e1 in a && e2 in b :: Independent(ms, e1, e2)
  }
}

module RNGProbability {
  import opened RNG
  import opened Probability
  import opened HurdMonad

  /* Axiomatisation for now */
  ghost const sample_space: iset<rng> := iset s: rng | true
  ghost const event_space: iset<iset<rng>>
  ghost const mu: iset<rng> -> real

  lemma {:axiom} LemmaProbabilitySpace()
    ensures IsSigmaAlgebra(event_space, sample_space)
    ensures IsPositive(MeasurableSpaceStructure.Pair(event_space, sample_space), mu)
    ensures IsCountablyAdditive(MeasurableSpaceStructure.Pair(event_space, sample_space), mu)
    ensures mu(sample_space) == 1.0

  // Equation (2.82)
  lemma {:axiom} RandomBit(n: nat)
    ensures 
      var e := (iset s: rng | Head(Drop(n, s)) == true);
      e in event_space && mu(e) == 0.5

  // Definition 30
  ghost predicate IsCompositional<A(!new)>(q: (() -> Hurd<A>) -> bool) {
    && (forall a :: q(() => Unit(a)))
    && (forall f: () -> Hurd<A>, g: A -> Hurd<A> :: q(f) && forall a :: q(() => g(a)) ==> q(() => Bind(f(), g)))
  }

  // function Dice(): Hurd<nat> 

  // function TwoDice(): Hurd<nat> {
  //   Bind(Dice(), (x: nat) => Bind(Dice(), (y: nat) => Unit(x + y)))
  // }

  // Definition 37
  function ProbWhileCut<A>(c: A -> bool, b: A -> Hurd<A>, n: nat, a: A): Hurd<A> {
    if n == 0 then
      Unit(a)
    else 
      if c(a) then 
        Bind(b(a), a' => ProbWhileCut(c, b, n-1, a')) 
      else 
        Unit(a)
  }

  // Theorem 38
  function ProbWhile<A>(c: A -> bool, b: A -> Hurd<A>, arb: (A, rng), a: A): Hurd<A> {
    assume false;
    if c(a) then
      Bind(b(a), (a': A) => ProbWhile(c, b, arb, a'))
    else
      Unit(a)
  }

  // Definition 44
  function ProbUntil<A>(b: Hurd<A>, c: A -> bool, arb: (A, rng)): Hurd<A> {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    Bind(b, (a: A) => ProbWhile(c', b', arb, a))
  }

  // Theorem 45
  lemma {:axiom} LemmaProbUntil<A>(b: Hurd<A>, c: A -> bool, arb: (A, rng), spec: A -> bool)
    // requires ***
    ensures 
      var x := mu(iset s: rng | spec(ProbUntil(b, c, arb)(s).0));
      var spec_and_c := (a: A) => spec(a) && c(a);
      var y := mu(iset s: rng | spec_and_c(ProbUntil(b, c, arb)(s).0));
      var z := mu(iset s: rng | c(ProbUntil(b, c, arb)(s).0));
      z > 0.0 && x == y / z;

  // Definition 46
  ghost function Pseudo(A: nat, B: nat, N: nat, n: nat): rng {
    var h := (x: nat) => (x as int) % 2 == 0;
    var t := (x: nat) => (((A*x + B) as int) % (2*N + 1)) as nat;
    Iter(h, t, n)
  }

  // Equation (3.42)
  lemma AboutPseudoHead(A: nat, B: nat, N: nat, n: nat) 
    ensures Head(Pseudo(A, B, N, n)) == ((n as int) % 2 == 0)
  {}

  // Equation (3.43)
  lemma AboutPseudoTail(A: nat, B: nat, N: nat, n: nat, m: nat)
    ensures Tail(Pseudo(A, B, N, n))(m) == Pseudo(A, B, N, (((A*n + B) as int) % (2*N + 1)) as nat)(m)
  {}

  // Definition 47
  function ProbBinomial(n: nat): Hurd<nat> {
    if n == 0 then
      Unit(0)
    else 
      var f: nat -> Hurd<nat> := 
        (m: nat) =>
          var g: bool -> Hurd<nat> := (b: bool) => Unit(if b then m + 1 else m);
          Bind(Dest, g);
      Bind(ProbBinomial(n - 1), f)
  }

  // Definition 48
  function ProbUnif(n: nat): Hurd<nat> {
    if n == 0 then
      Unit(0)
    else
      var f: nat -> Hurd<nat> := 
        (m: nat) => 
          var g: bool -> Hurd<nat> := (b: bool) => Unit(if b then 2*m + 1 else 2*m);
          Bind(Dest, g);
      Bind(ProbUnif(n / 2), f)
  }

  // Definition 49
  function ProbUniform(n: nat, arb: (nat, rng)): Hurd<nat> 
    requires n > 0
  {
    ProbUntil(ProbUnif(n-1), (x: nat) => x < n, arb)
  }

  // Equation (4.12)
  // lemma LemmaProbUniform(n: nat, arb: (nat, rng), m: nat)
  //   requires m < n 
  //   ensures mu(iset s: rng | ProbUniform(n, arb)(s).0 == m) == 1.0/(n as real)
  // {
  //   var b := ProbUnif(n-1);
  //   var c := (x: nat) => x < n;
  //   var spec := (x: nat) => x == m;
  //   var spec_and_c := (x: nat) => spec(x) && c(x);
  //   LemmaProbUntil(b, c, arb, spec);
  //   forall s: rng ensures spec_and_c(ProbUntil(b, c, arb)(s).0) <==> spec(ProbUntil(b, c, arb)(s).0) {
  //     var x := ProbUntil(b, c, arb)(s).0;
  //     calc {
  //       spec_and_c(x);
  //     <==>
  //       spec(x) && c(x);
  //     <==>
  //       x == m && x < n;
  //     <==>
  //       x == m;
  //     <==>
  //       spec(x);
  //     }
  //   }
  // }


  // Definition 53
  function CoinFlip(a: Hurd<nat>, b: Hurd<nat>): Hurd<nat> {
    Bind(Dest, ((x: bool) => if x then a else b))
  }

  // Equation (4.37)
  function RandomWalk(n: nat, k: nat): Hurd<nat>
  {
    assume false;
    if n == 0 then
      Unit(k)
    else
      CoinFlip(RandomWalk(n+1, k+1), RandomWalk(n-1, k+1))
  }

}

module ExampleFlip {
  import opened RNG
  import opened HurdMonad
  import opened RNGProbability
  import opened Probability

  datatype Coin = Heads | Tails

  // p15
  ghost function RNGSatisfyingSpec<A,B>(spec: (A, B) -> bool, f: A -> Hurd<B>, a: A): iset<rng> {
    iset s: rng | spec(a, f(a)(s).0)
  }

  function Flip(): Hurd<Coin> 
  {
    (s: rng) => (if s(0) then Heads else Tails, Tail(s))
  }

  function Spec1(a: (), b: Coin): bool {
    b == Heads
  }

  function Spec2(a: (), b: Coin): bool {
    b == Tails
  }

  lemma AboutFlip() 
    requires RNGSatisfyingSpec(Spec1, (x: ()) => Flip(), ()) in event_space
    requires RNGSatisfyingSpec(Spec2, (x: ()) => Flip(), ()) in event_space
    ensures mu(RNGSatisfyingSpec(Spec1, (x: ()) => Flip(), ())) == 0.5 
    ensures mu(RNGSatisfyingSpec(Spec2, (x: ()) => Flip(), ())) == 0.5 
  {
    var e1 := RNGSatisfyingSpec(Spec1, (x: ()) => Flip(), ());
    var e2 := RNGSatisfyingSpec(Spec2, (x: ()) => Flip(), ());
    RandomBit(0);
    assert mu((iset s: rng | Head(Drop(0, s)) == true)) == 0.5;
    assert mu(e1) == 0.5 by { assert e1 == (iset s: rng | Head(Drop(0, s)) == true); }
    assert e1 + e2 == sample_space;
    assert IsSigmaAlgebra(event_space, sample_space) by { LemmaProbabilitySpace(); }
    var ms := MeasurableSpaceStructure.Pair(event_space, sample_space);
    assert IsPositive(ms, mu) by { LemmaProbabilitySpace(); }
    assert IsCountablyAdditive(ms, mu) by { LemmaProbabilitySpace(); }
    LemmaPosCountAddImpliesAdd(ms, mu);
    assert mu(sample_space) == 1.0 by { LemmaProbabilitySpace(); }
    assert mu(e2) == 0.5;
  }

}