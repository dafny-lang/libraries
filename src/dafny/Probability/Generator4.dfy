module {:options "-functionSyntax:4"} Generator {
  type rbs = nat -> bool

  // Definition 29
  type Hurd<+A> = rbs -> (A, rbs)

  datatype Option<+A> = None | Some(value: A)

  function IsSome<A>(o: Option<A>): bool {
    o.Some?
  }

  function ToSome<A>(a: A): Option<A> {
    Some(a)
  }

  // Definition 14
  function Head(s: rbs): bool {
    s(0)
  }

  // Definition 14
  function Tail(s: rbs): rbs {
    (n: nat) => s(n+1)
  }

  // Definition 14
  function Dest(s: rbs): (bool, rbs) {
    (Head(s), Tail(s))
  }

  // Definition 15
  function Iter<A>(h: A -> bool, t: A -> A, x: A, n: nat): bool {
    if n == 0 then
      h(x)
    else 
      Iter(h, t, t(x), n-1)
  }
  
  // Definition 46
  function Pseudo(A: nat, B: nat, N: nat, n: nat): rbs {
    var h := (x: nat) => (x as int) % 2 == 0;
    var t := (x: nat) => (((A*x + B) as int) % (2*N + 1)) as nat;
    (m: nat) => Iter(h, t, n, m)
  }

  // Definition 29
  function Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>): Hurd<B> {
    (s: rbs) =>
      var (a, s') := f(s);
      g(a)(s')
  }

  function Composition<A,B,C>(f: A -> Hurd<B>, g: B -> Hurd<C>): A -> Hurd<C> {
    (a: A) => Bind(f(a), g)
  }

  // Definition 29
  function Unit<A>(a: A): Hurd<A> {
    (s: rbs) => (a, s)
  }

  // Definition 53
  function Map<A,B>(f: A -> B, m: Hurd<A>): Hurd<B> {
    Bind(m, (a: A) => Unit(f(a)))
  }

  // Theorem 38
  function ProbWhile<A>(c: A -> bool, b: A -> Hurd<A>, a: A): (f: Hurd<A>)
    ensures forall s :: !c(f(s).0)
  {
    assume {:axiom} false;
    if c(a) then
      Bind(b(a), (a': A) => ProbWhile(c, b, a'))
    else
      Unit(a)
  }

  // Definition 44
  function ProbUntil<A>(b: Hurd<A>, c: A -> bool): (f: Hurd<A>) {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    Bind(b, (a: A) => ProbWhile(c', b', a))
  }

  lemma LemmaInvariantProbUntil<A>(b: Hurd<A>, c: A -> bool, s: rbs) 
    ensures c(ProbUntil(b, c)(s).0)
  {
    var (a, s') := b(s);
  }

  // Definition 48
  function ProbUnif(n: nat): Hurd<nat> {
    if n == 0 then
      Unit(0)
    else
      var f := (m: nat) => 
        var g := (b: bool) => 
          Unit(if b then 2*m + 1 else 2*m);
        Bind(Dest, g);
      Bind(ProbUnif(n / 2), f)
  }

  // Definition 49
  function ProbUniform(n: nat): Hurd<nat> 
    requires n > 0
  {
    ProbUntil(ProbUnif(n-1), (x: nat) => x < n)
  }

  // Equation (4.23)
  function ProbBernoulli(p: real): Hurd<bool> 
    requires 0.0 <= p <= 1.0
  {
    assume {:axiom} false;
    var f := 
      (b: bool) =>
        if b then
          if p <= 0.5 then 
            Unit(false)
          else 
            ProbBernoulli(2.0 * p - 1.0)
        else
          if p <= 0.5 then 
            ProbBernoulli(2.0 * p)
          else 
            Unit(true);
    Bind(Dest, f)
  }

  // Definition 53
  function CoinFlip<A>(a: Hurd<A>, b: Hurd<A>): Hurd<A> {
    Bind(Dest, (x: bool) => if x then a else b)
  }

/*
  // Definition 53
  function ProbRepeat<A>(a: Hurd<Option<A>>): (Hurd<A>) {
    var f := ProbUntil(a, IsSome);
    (s: rbs) => 
      var a' := f(s).0;
      assert IsSome(a') by { LemmaInvariantProbUntil(a, IsSome, s); }
      Unit(a'.value)
  }
 
   // Definition 54
  function Dice(): (f: Hurd<nat>)
    ensures forall s: rbs :: 1 <= f(s).0 <= 6
  {
    CoinFlip<bat>(
      ProbRepeat<nat>(
        CoinFlip<Option<nat>>(
          CoinFlip<Option<nat>>(Unit(None), Unit(Some(1))), 
          Map(ToSome, CoinFlip<nat>(Unit(2), Unit(3)))
        )
      ),
      CoinFlip<Option<nat>>(
        Map(ToSome, CoinFlip(Unit(4), Unit(5))),
        CoinFlip(Unit(Some(6)), Unit(None))
      )
    )
  } */


}

method Main() {
  var s := Generator.Pseudo(103, 95, 75, 94);
  for i := 0 to 100 {
    var b := if s(i) then "1" else "0";
    print b;
  }
  print "\n\n";
  for i := 0 to 30 {
    var (n, t) := Generator.ProbUniform(6)(s);
    print n;
    s := t;
  }
}