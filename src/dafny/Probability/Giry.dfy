// Definition 4 in Hurd's thesis
ghost predicate IsAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>) {
  && (forall e | e in event_space :: e <= sample_space)
  && iset{} in event_space
  && (forall e | e in event_space :: (sample_space - e) in event_space)
  && (forall e1, e2 | e1 in event_space && e2 in event_space :: e1 + e2 in event_space)
}  

ghost function CountableUnion<T>(f: nat -> iset<T>, i: nat := 0): iset<T> {
  assume false;
  f(i) + CountableUnion(f, i+1)
}

// Definition 4 in Hurd's thesis
ghost predicate IsSigmaAlgebra<T(!new)>(event_space: iset<iset<T>>, sample_space: iset<T>) {
  && IsAlgebra(event_space, sample_space)
  && forall f: nat -> iset<T> | (forall n :: f(n) in event_space) :: CountableUnion(f) in event_space 
}

datatype MeasurableSpaceStructure<!T> = Pair(event_space: iset<iset<T>>, sample_space: iset<T>)

type MeasurableSpace<!T(!new)> = pair: MeasurableSpaceStructure | IsSigmaAlgebra(pair.event_space, pair.sample_space) witness *

ghost function CountableSum(f: nat -> real, i: nat := 0): real {
  assume false;
  f(i) + CountableSum(f, i+1)
}

ghost predicate IsMeasure<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
  && mu(iset{}) == 0.0
  && forall e | e in ms.event_space :: 0.0 <= mu(e)
  && forall f: nat -> iset<T> | (forall n :: f(n) in ms.event_space) && (forall m, n | m != n :: f(m) * f(n) == iset{}) && (CountableUnion(f) in ms.event_space) :: (CountableSum((n: nat) => mu(f(n))) == mu(CountableUnion(f)))
}

ghost predicate IsProbabilityMeasure<T(!new)>(ms: MeasurableSpace<T>, mu: iset<T> -> real) {
  && IsMeasure(ms, mu)
  && mu(ms.sample_space) == 1.0
}

// Definition 6 in Hurd's thesis
datatype MeasureSpaceStructure<!T(!new)> = Pair(ms: MeasurableSpace, mu: iset<T> -> real) 

type MeasureSpace<!T(!new)> = pair: MeasureSpaceStructure | IsMeasure(pair.ms, pair.mu) witness *

// type ProbabilitySpace<!T(!new)> = pair: MeasureSpaceStructure | IsProbabilityMeasure(pair.ms, pair.mu) witness *

ghost function PreImageOf<S(!new),T>(f: S -> T, domain: iset<S>, b: iset<T>): (a: iset<S>)
  ensures a <= domain
  ensures forall x | x in a :: f(x) in b
{
  iset x | x in domain && f(x) in b
}

// Definition 9
ghost predicate IsMeasurableFunction<S(!new),T(!new)>(ms1: MeasurableSpace<S>, ms2: MeasurableSpace<T>, f: S -> T) {
  forall e | e in ms2.event_space :: PreImageOf(f, ms1.sample_space, e) in ms1.event_space
}

ghost function GiryObject<T(!new)>(ms: MeasurableSpace<T>): (ms': MeasurableSpace<iset<T>->real>)
  ensures ms'.sample_space == iset mu | IsProbabilityMeasure(ms, mu);

ghost function GiryMorphism<S(!new), T(!new)>(ms1: MeasurableSpace<S>, ms2: MeasurableSpace<T>, f: S -> T): (g: (iset<S>->real) -> (iset<T>->real))
  requires IsMeasurableFunction(ms1, ms2, f)
  ensures IsMeasurableFunction(GiryObject(ms1), GiryObject(ms2), g)

ghost function GiryReturn<T(!new)>(ms: MeasurableSpace<T>, x: T): (mu_x: iset<T> -> real)
  requires x in ms.sample_space
  ensures mu_x in GiryObject(ms).sample_space
  ensures forall s: iset<T> :: mu_x(s) == if x in s then 1.0 else 0.0


