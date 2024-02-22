

datatype Option<+T> = Some(value: T) | None

function SeqEnumeratorFn<T>(s: seq<T>): Option<(seq<T>, T)> {
  if |s| == 0 then
    None
  else
    Some((s[1..], s[0]))
}

function SetEnumeratorFn<T>(s: set<T>): Option<(set<T>, T)> {
  if |s| == 0 then
    None
  else
    var t :| t in s;
    Some((s - {t}, t))
}

type EnumeratorFn<!S, T> = S -> Option<(S, T)>
datatype Enumerator_<!S(!new), T> = Enumerator(state: S, fn: EnumeratorFn<S, T>, ghost decreasesFn: S -> nat) {
  ghost predicate Valid() {
    Decreases(fn, decreasesFn)
  }
}
ghost predicate Decreases<S(!new), T>(fn: EnumeratorFn<S, T>, decreasesFn: S -> nat) {
  forall s: S :: match fn(s)
      case Some((s', _)) => decreasesFn(s') < decreasesFn(s)
      case None => true
}

type Enumerator<!S(!new), T> = e: Enumerator_<S, T> | e.Valid() witness *

function {:tailrecursion} Enumerate<S(!new), T>(e: Enumerator<S, T>): seq<T>
  decreases e.decreasesFn(e.state)
{
  match e.fn(e.state)
  case Some((s, t)) => [t] + Enumerate(Enumerator(s, e.fn, e.decreasesFn))
  case None => []
}

function ConcatEnumeratorFn<A, B, T>(first: EnumeratorFn<A, T>, second: EnumeratorFn<B, T>): EnumeratorFn<(A, B), T> {
  x =>
    var (a, b) := x;
    match first(a)
    case Some((a', t)) => Some(((a', b), t))
    case None =>
      match second(b)
      case Some((b', t)) => Some(((a, b'), t))
      case None => None
}

function ConcatDecreasesFn<A, B>(first: A -> nat, second: B -> nat): ((A, B)) -> nat {
  x => 
    var (a, b) := x;
    var result: nat := first(a) + second(b);
    result
}

function ConcatEnumerator<A(!new), B(!new), T>(first: Enumerator<A, T>, second: Enumerator<B, T>): Enumerator<(A, B), T> {
  var result := Enumerator((first.state, second.state), 
                            ConcatEnumeratorFn(first.fn, second.fn),
                            ConcatDecreasesFn(first.decreasesFn, second.decreasesFn));
  result
}

lemma ConcatEnumeratesConcat<A(!new), B(!new), T>(first: Enumerator<A, T>, second: Enumerator<B, T>)
  ensures Enumerate(ConcatEnumerator(first, second)) == Enumerate(first) + Enumerate(second)
{

}