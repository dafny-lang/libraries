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
  
  // Definition 46 (Should be implemented external with seeds chosen non-deterministically for each call)
  function RandomBitSeq(A: nat := 103, B: nat := 95, N: nat := 75, n: nat := 94): rbs {
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
  function Uniform(n: nat): Hurd<nat> 
    requires n > 0
  {
    ProbUntil(ProbUnif(n-1), (x: nat) => x < n)
  }

  // Equation (4.23)
  function Bernoulli(p: real): Hurd<bool> 
    requires 0.0 <= p <= 1.0
  {
    assume {:axiom} false;
    var f := 
      (b: bool) =>
        if b then
          if p <= 0.5 then 
            Unit(false)
          else 
            Bernoulli(2.0 * p - 1.0)
        else
          if p <= 0.5 then 
            Bernoulli(2.0 * p)
          else 
            Unit(true);
    Bind(Dest, f)
  }

  // Definition 53
  function CoinFlip<A>(a: Hurd<A>, b: Hurd<A>): Hurd<A> {
    Bind(Dest, (x: bool) => if x then a else b)
  }

  function Factorial(k: nat): (r: nat)
    ensures r > 0
  {
    if k <= 1 then 
      1
    else 
      k * Factorial(k-1)
  }

  function Power(x: real, k: nat): real {
    match k 
      case 0 => 1.0
      case 1 => x 
      case _ => x * Power(x, k-1) 
  }

  function Exp(x: real, max: nat, k: nat := 0): (r: real)
    requires k <= max
    ensures x <= 1.0 ==> 0.0 <= r <= 1.0
  {
    assume {:axiom} false;
    var y := Power(x, k) / (Factorial(k) as real);
    if k == max then 
      y 
    else
      y + Exp(x, max, k+1)
  }

  function LaPlaceLoop(max: nat, v: nat := 0): Hurd<nat> {
    (s: rbs) => 
      var (a, s') := Bernoulli(Exp(-1.0, max))(s);
      if a then
        (v, s') 
      else
        assume {:axiom} false;
        LaPlaceLoop(max, v+1)(s')
  }

  // Algorithm 2 (Paper: The Discrete Gaussian for Differential Privacy)
  function LaPlace(m: nat, n: nat, max: nat := 10): Hurd<nat>
    requires m >= 1 && n >= 1
  {
    assume {:axiom} false;
    (s: rbs) => 
      var (u, s2) := Uniform(n-1)(s);
      var (d, s3) := Bernoulli(Exp((-u as real)/(n as real), max))(s2);
      if !d then
        LaPlace(m, n, max)(RandomBitSeq())
      else 
        var (v, s4) := LaPlaceLoop(max)(s3);
        var x := (u + n * v) as real;
        var y := (x / (m as real)).Floor;
        var (b, s5) := Bernoulli(0.5)(s4);
        if b && y == 0 then 
          LaPlace(m, n, max)(RandomBitSeq())
        else
          var z := if b then -y else y;
          (z, s5)
  }

}

import opened Generator

method Main() {
  print "Prefix of length 100 of the countable-infinite initial random bit sequence:\n";
  var s := RandomBitSeq();
  for i := 0 to 100 {
    var b := if s(i) then "1" else "0";
    print b;
  }
  print "\nSample of 15 Uniform(6)-distributed integers: \n";
  for i := 0 to 15 {
    var (n, t) := Uniform(6)(s);
    print n,", ";
    s := t;
  }
  print "\n\n";
  print "Prefix of length 100 of the countable-infinite initial random bit sequence:\n";
  s := RandomBitSeq();
  for i := 0 to 100 {
    var b := if s(i) then "1" else "0";
    print b;
  }
  print "\nSample of 15 Bernoulli(0.2)-distributed bits: \n";
  for i := 0 to 15 {
    var (b, t) := Bernoulli(0.2)(s);
    var b' := if b then "1" else "0";
    print b',", ";
    s := t;
  }
  print "\n\n";
  print "Prefix of length 100 of the countable-infinite initial random bit sequence:\n";
  s := RandomBitSeq();
  for i := 0 to 100 {
    var b := if s(i) then "1" else "0";
    print b;
  }
  print "\nSample of 5 LaPlace(5/3)-distributed integers: \n";
  for i := 0 to 5 {
    var (n, t) := LaPlace(3, 5)(s);
    print n,", ";
    s := t;
  }

  



}