// Implemetation of Heap sort
include "../src/Collections/Sequences/Seq.dfy"

method SortArray<T>(a: array<T>, compare: (T, T) -> bool)
  requires multiset(a[..]) == multiset(old(a[..]))
  modifies a
  ensures forall i, j :: 0 <= i < j < a.Length ==> compare(a[i], a[j])
  {
    var n := a.Length;
    for i := n/2 -1 downto 0
    invariant 0 <= i <= a.Length
    {
      heapify(a,n,i,compare);
    }

    for i:= n-1 downto 1
    invariant 0 <= i <= a.Length
    {
      var temp:= a[0];
      a[0]:= a[i];
      a[i]:= temp;
      heapify(a,i,0,compare);
      }
    }

method heapify<T>(a: array<T>, n:int, i:int, compare: (T, T) -> bool ) 
ensures multiset(a[..]) == multiset(old(a[..]))
modifies a
{ 
 var largest := i;
 var left := 2* i+ 1;
 var right := 2* 1+ 2;

  if ((left > n) && compare(a[left], a[largest]))
  {
    largest := left;
  }

  if (right < n && compare(a[right], a[largest]))
  {
    largest := right;
  }
    

  if (largest != i)
  {
    largest := i;
    heapify(a,n,largest,compare);
  }
}

method Sort<T>(s: seq<T>, compare: (T, T) -> bool) returns (result :array<T>)
 {
    var a := Seq.ToArray(s);   
    SortArray(a, compare);
    return a;
  }