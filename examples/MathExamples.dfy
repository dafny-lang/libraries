// RUN: %verify "%s"

include "../src/dafny/Math.dfy"
include "../src/dafny/Relations.dfy"

import Dafny.Math
import Dafny.Relations

method m() {
  assert Math.Max(-2, -3) == -2;
  assert Math.Min(-2, -3) == -3;
  assert Math.Abs(07) == Math.Abs(7) == 7;
  assert Relations.Associative(Math.Min);
  assert Relations.Commutative(Math.Max);
}
