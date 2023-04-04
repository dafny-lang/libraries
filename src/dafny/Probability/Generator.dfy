module {:options "-functionSyntax:4"} Generator {
  // Variation of Definition 15
  function Iter<A>(h: A -> bool, t: A -> A, x: A, length: nat): seq<bool> {
    if length == 0 then
      []
    else
      [h(x)] + Iter(h, t, t(x), length - 1)
  }

  // Variation of Definition 46
  function Pseudo(A: nat, B: nat, N: nat, n: nat, length: nat): seq<bool> {
    var h := (x: nat) => (x as int) % 2 == 0;
    var t := (x: nat) => (((A*x + B) as int) % (2*N + 1)) as nat;
    Iter(h, t, n, length)
  }
}

method Main() {
  var xs := Generator.Pseudo(103, 95, 79, 0, 100);
  for i := 0 to |xs| {
    var b := if xs[i] then "1" else "0";
    print b;
  }
}