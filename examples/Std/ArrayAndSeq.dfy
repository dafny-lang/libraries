include "../../src/Std.dfy"

module Demo {
  import opened Std

  method Main() {
    // Going from an array to a sequence is easy using `[..]`
    var a: array<nat> := new nat[3];
    a[0] := 1;
    a[1] := 10;
    a[2] := 100;
    var aAsSeq: seq<nat> := a[..];
    print aAsSeq[2], "\n";

    // On the other hand, to go from a sequence to an array,
    // Dafny doesn't have a builtin construct, but we have
    // one in the standard library:
    var s: seq<nat> := [3, 4, 5];
    var sAsArray: array<nat> := ArrayOfSeq(s);
    print sAsArray[2], "\n";
  }
}
