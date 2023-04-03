module RNG {
  type rng = nat -> bool

  function hd(s: rng): bool {
    s(0)
  }

  function tl(s: rng): rng {
    (n: nat) => s(n+1)
  }

  function cons(a: bool, s: rng, n: nat): bool {
    if n == 0 then 
      a 
    else 
      s(n-1)
  }

  function take(n: nat, s: rng): seq<bool> {
    if n == 0 then
      []
    else
      [hd(s)] + take(n-1, tl(s))
  }

  function drop(n: nat, s: rng): rng {
    if n == 0 then
      s
    else
      drop(n-1, tl(s))
  }

  function dest(s: rng): (bool, rng) {
    (hd(s), tl(s))
  }

  ghost function prefix_set(l: seq<bool>): iset<rng> {
    iset s: rng | take(|l|, s) == l
  }

  ghost function prefix_seq(l: seq<bool>, a: bool): seq<bool> {
    if l == [] then
      [a]
    else
      [l[0]] + prefix_seq(l[1..], a)
  }
  
}

module HurdMonad {
  import opened RNG

  type Hurd<A> = rng -> (A, rng)

  function Unit<A>(a: A): Hurd<A> {
    (s: rng) => (a, s)
  }

  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (s: rng) =>
      var (a, s') := f(s);
      g(a)(s')
  }

  function Join<A>(ff: Hurd<Hurd<A>>): Hurd<A> {
    (s: rng) =>
      var (f, s') := ff(s);
      f(s')
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }
}

module Probability {
  ghost function EmptyIset<T(!new)>(): iset<T> {
    iset x: T | false
  }

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

  ghost predicate IsSigmaAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>) {
    && IsAlgebra(event_space, sample_space)
    && forall f: nat -> iset<T> | (forall n :: f(n) in event_space) :: CountableUnion(f) in event_space 
  }

  datatype MeasurableSpaceStructure<!T> = Pair(event_space: iset<iset<T>>, sample_space: iset<T>)

  type MeasurableSpace<!T(!new)> = pair: MeasurableSpaceStructure | IsSigmaAlgebra(pair.event_space, pair.sample_space) witness *

  ghost predicate IsPositive<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
    && mu(EmptyIset()) == 0.0
    && forall e | e in ms.event_space :: 0.0 <= mu(e)
  }

  ghost predicate IsIncreasing<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
    forall e1, e2 | e1 in ms.event_space && e2 in ms.event_space && e1 <= e2 :: mu(e1) <= mu(e2)
  }

  ghost predicate IsCountablyAdditive<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
    forall f: nat -> iset<T> | (forall n :: f(n) in ms.event_space) && (forall m, n | m != n :: f(m) * f(n) == EmptyIset()) && (CountableUnion(f) in ms.event_space) :: (CountableSum((n: nat) => mu(f(n))) == mu(CountableUnion(f)))
  }

  lemma {:axiom} LemmaIsBinaryAdditive<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real, e1: iset<T>, e2: iset<T>)
    requires IsCountablyAdditive(ms, mu)
    requires e1 in ms.event_space
    requires e2 in ms.event_space
    requires e1 * e2 == EmptyIset()
    ensures mu(e1) + mu(e2) == mu(e1 + e2)
  
  datatype MeasureSpaceStructure<!T(!new)> = Pair(ms: MeasurableSpace, mu: iset<T> -> real) 

  type MeasureSpace<!T(!new)> = pair: MeasureSpaceStructure | IsPositive(pair.ms, pair.mu) && IsCountablyAdditive(pair.ms, pair.mu) witness *

  ghost function PreImageOf<S(!new),T>(f: S -> T, domain: iset<S>, b: iset<T>): (a: iset<S>)
    ensures a <= domain
    ensures forall x | x in a :: f(x) in b
  {
    iset x | x in domain && f(x) in b
  }

  ghost predicate IsMeasurableFunction<S(!new),T(!new)>(ms1: MeasurableSpace<S>, ms2: MeasurableSpace<T>, f: S -> T)
  {
    forall e | e in ms2.event_space :: PreImageOf(f, ms1.sample_space, e) in ms1.event_space
  }

  type ProbabilitySpace<!T(!new)> = ms: MeasureSpace | ms.mu(ms.ms.sample_space) == 1.0 witness *
}

module RNGProbability {
  import opened RNG
  import opened Probability

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
      var e := (iset s: rng | hd(drop(n, s)) == true);
      e in event_space && mu(e) == 0.5
}

module Examples {
  import opened RNG
  import opened HurdMonad
  import opened RNGProbability
  import opened Probability

  datatype Coin = Head | Tail

  ghost function RNGSatisfyingSpec<A,B>(spec: (A, B) -> bool, f: A -> Hurd<B>, a: A): iset<rng> {
    iset s: rng | spec(a, f(a)(s).0)
  }

  function Flip(x: ()): Hurd<Coin> 
  {
    (s: rng) => (if s(0) then Head else Tail, tl(s))
  }

  function Spec1(a: (), b: Coin): bool {
    b == Head
  }

  function Spec2(a: (), b: Coin): bool {
    b == Tail
  }

  lemma AboutFlip() 
    requires RNGSatisfyingSpec(Spec1, Flip, ()) in event_space
    requires RNGSatisfyingSpec(Spec2, Flip, ()) in event_space
    ensures mu(RNGSatisfyingSpec(Spec1, Flip, ())) == 0.5 
    ensures mu(RNGSatisfyingSpec(Spec2, Flip, ())) == 0.5 
  {
    var e1 := RNGSatisfyingSpec(Spec1, Flip, ());
    var e2 := RNGSatisfyingSpec(Spec2, Flip, ());
    assert e1 == iset s: rng | s(0) == true;
    assert e2 == iset s: rng | s(0) == false;
    RandomBit(0);
    assert mu((iset s: rng | hd(drop(0, s)) == true)) == 0.5;
    assert mu(e1) == 0.5 by { assert e1 == (iset s: rng | hd(drop(0, s)) == true); }
    assert e1 + e2 == sample_space;
    assert e1 * e2 == EmptyIset();
    assert IsSigmaAlgebra(event_space, sample_space) by { LemmaProbabilitySpace(); }
    assert sample_space in event_space by { LemmaSampleSpaceInAlgebra(event_space, sample_space); }
    assert e1 + e2 in event_space;
    var ms := MeasurableSpaceStructure.Pair(event_space, sample_space);
    assert IsCountablyAdditive(ms, mu) by { LemmaProbabilitySpace(); }
    LemmaIsBinaryAdditive(ms, mu, e1, e2);
    assert mu(e1 + e2) == mu(e1) + mu(e2);
    assert mu(sample_space) == 1.0 by { LemmaProbabilitySpace(); }
    assert mu(e2) == 0.5;
  }

}