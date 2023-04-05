module {:options "-functionSyntax:4"} Generator {
  type rbs = nat -> bool

  // Definition 14
  method Cons(a: bool, s: rbs, n: nat) returns (b: bool) {
    if n == 0 { 
      b := a;
    } else {
      b := s(n-1);
    }
  }

  // Definition 14
  method Head(s: rbs) returns (b: bool) {
    b := s(0);
  }

  // Definition 14
  method Tail(s: rbs) returns (t: rbs) {
    t := (n: nat) => s(n+1);
  }

  // Definition 14
  method Dest(s: rbs) returns (x: (bool, rbs)) {
    x := (Head(s), Tail(s));
  }

  // Definition 15
  method Iter<A>(h: A -> bool, t: A -> A, x: A) returns (s: rbs)
    decreases *
  {
    s := (n: nat) => Cons(h(x), Iter(h, t, t(x)), n);
  }
  
  // Definition 46
  method PseudoSeq(A: nat, B: nat, N: nat, n: nat) returns (s: rbs) 
    decreases *
  {
    var h := (x: nat) => (x as int) % 2 == 0;
    var t := (x: nat) => (((A*x + B) as int) % (2*N + 1)) as nat;
    s := Iter(h, t, n);
  }

  // Definition 29
  type Hurd<A> = rbs -> (A, rbs)

  // Definition 29
  method Bind<A,B>(f: Hurd<A>, g: A -> Hurd<B>) returns (h: Hurd<B>) {
    h := (s: rbs) =>
      var (a, s') := f(s);
      g(a)(s');
  }

  // Definition 29
  method Unit<A>(a: A) returns (f: Hurd<A>) {
    f := (s: rbs) => (a, s);
  }

  // Theorem 38
  method ProbWhile<A>(c: A -> bool, b: A -> Hurd<A>, arb: (A, rbs), a: A) returns (f: Hurd<A>)
    decreases *
  {
    if c(a) {
      f := Bind(b(a), (a': A) => ProbWhile(c, b, arb, a'));
    } else {
      f := Unit(a);
    }
  }

  // Definition 44
  method ProbUntil<A>(b: Hurd<A>, c: A -> bool, arb: (A, rbs)) returns (f: Hurd<A>)
    decreases *
  {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    f := Bind(b, (a: A) => ProbWhile(c', b', arb, a));
  }

  // Definition 48
  method ProbUnif(n: nat) returns (h: Hurd<nat>) 
    decreases *
  {
    if n == 0 {
      h := Unit(0);
    }
      var f: nat -> Hurd<nat> := 
        (m: nat) => 
          var g: bool -> Hurd<nat> := (b: bool) => Unit(if b then 2*m + 1 else 2*m);
          Bind(Dest, g);
      h := Bind(ProbUnif(n / 2), f);
  }

  // Definition 49
  method ProbUniform(n: nat, arb: (nat, rbs)) returns (f: Hurd<nat>)
    decreases *
    requires n > 0
  {
    f := ProbUntil(ProbUnif(n-1), (x: nat) => x < n, arb);
  }
}

/* method Main() {
  var xs := Generator.PseudoSeq(103, 95, 75, 94, 100);
  for i := 0 to |xs| {
    var b := if xs[i] then "1" else "0";
    print b;
  }
  print "\n\n";
  for i := 0 to 20 {
    var (n, ys) := Generator.ProbUniformSeq(6, (0,[]), |xs|)(xs);
    print n;
    xs := ys;
  }
} */