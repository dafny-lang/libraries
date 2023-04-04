module {:options "-functionSyntax:4"} Generator {
  // Variation of Definition 14
  function ConsSeq(a: bool, s: seq<bool>): seq<bool> {
    [a] + s
  }

  // Variation of Definition 14
  function HeadSeq(s: seq<bool>): bool {
    if |s| == 0 then
      false
    else 
      s[0]
  }

  // Variation of Definition 14
  function TailSeq(s: seq<bool>): seq<bool> {
    if |s| == 0 then
      []
    else
      s[1..]
  }

  // Variation of Definition 14
  function DestSeq(s: seq<bool>): (bool, seq<bool>) {
    (HeadSeq(s), TailSeq(s))
  }

  // Variation of Definition 15
  function IterSeq<A>(h: A -> bool, t: A -> A, x: A, length: nat): seq<bool> {
    if length == 0 then
      []
    else 
      ConsSeq(h(x), IterSeq(h, t, t(x), length-1))
  }
  
  // Variation of Definition 46
  function PseudoSeq(A: nat, B: nat, N: nat, n: nat, length: nat): seq<bool> {
    var h := (x: nat) => (x as int) % 2 == 0;
    var t := (x: nat) => (((A*x + B) as int) % (2*N + 1)) as nat;
    IterSeq(h, t, n, length)
  }

  // Variation of Definition 29
  type HurdSeq<A> = seq<bool> -> (A, seq<bool>)

  // Variation of Definition 29
  function BindSeq<A,B>(f: HurdSeq<A>, g: A -> HurdSeq<B>): HurdSeq<B> {
    (s: seq<bool>) =>
      var (a, s') := f(s);
      g(a)(s')
  }

  // Variation of Definition 29
  function UnitSeq<A>(a: A): HurdSeq<A> {
    (s: seq<bool>) => (a, s)
  }

  // Variation of Theorem 38
  function ProbWhileSeq<A>(c: A -> bool, b: A -> HurdSeq<A>, arb: (A, seq<bool>), a: A, length: nat): HurdSeq<A> 
    decreases length
  {
    if c(a) && length > 0 then
      BindSeq(b(a), (a': A) => ProbWhileSeq(c, b, arb, a', length-1))
    else
      UnitSeq(a)
  }

  // Variation of Definition 44
  function ProbUntilSeq<A>(b: HurdSeq<A>, c: A -> bool, arb: (A, seq<bool>), length: nat): HurdSeq<A> {
    var c' := (a: A) => !c(a);
    var b' := (a: A) => b;
    BindSeq(b, (a: A) => ProbWhileSeq(c', b', arb, a, length))
  }

  // Variaton of Definition 48
  function ProbUnifSeq(n: nat): HurdSeq<nat> {
    if n == 0 then
      UnitSeq(0)
    else
      var f: nat -> HurdSeq<nat> := 
        (m: nat) => 
          var g: bool -> HurdSeq<nat> := (b: bool) => UnitSeq(if b then 2*m + 1 else 2*m);
          BindSeq(DestSeq, g);
      BindSeq(ProbUnifSeq(n / 2), f)
  }

  // Variation of Definition 49
  function ProbUniformSeq(n: nat, arb: (nat, seq<bool>), length: nat): HurdSeq<nat> 
    requires n > 0
  {
    ProbUntilSeq(ProbUnifSeq(n-1), (x: nat) => x < n, arb, length)
  }
}

method Main() {
  var xs := Generator.PseudoSeq(103, 95, 79, 0, 1000);
  for i := 0 to |xs| {
    var b := if xs[i] then "1" else "0";
    print b;
  }
  print "\n\n";
  for i := 0 to 100 {
    var (n, ys) := Generator.ProbUniformSeq(6, (0,[]), |xs|)(xs);
    print n;
    xs := ys;
  }
}