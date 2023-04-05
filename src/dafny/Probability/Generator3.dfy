module {:options "-functionSyntax:4"} Generator {
  type rbs = nat -> bool

  // Definition 29
  type Hurd<A> = rbs -> (A, rbs)

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

  // Theorem 38
  function ProbWhile<A>(c: A -> bool, b: A -> Hurd<A>): A -> Hurd<A> {
    assume {:axiom} false;
    (a: A) =>
      if c(a) then
        Composition(b, ProbWhile(c, b))(a)
      else
        Unit(a)
  }

  // Definition 44
  function ProbUntil<A>(b: Hurd<A>, c: A -> bool): Hurd<A> {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    Bind(b, ProbWhile(c', b'))
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