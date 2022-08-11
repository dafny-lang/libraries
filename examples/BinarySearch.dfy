


method BinarySearch<T>(a: array<T>, key: T,compare: (T, T) -> bool) returns (r: int)
  requires forall i,j :: 0 <= i < j < a.Length ==> compare(a[i],a[j])
  ensures 0 <= r ==> r < a.Length && a[r] == key
  ensures r < 0 ==> key !in a[..]
{
  var lo, hi := 0, a.Length;
  while lo < hi
    invariant 0 <= lo <= hi <= a.Length
    invariant key !in a[..lo] && key !in a[hi..]
  {
    var mid := (lo + hi) / 2;
    if compare(key,a[mid]) {
      hi := mid;
    } else if compare(a[mid],key) {
      lo := mid + 1;
    } else {
      return mid;
    }
  }
  return -1;
}