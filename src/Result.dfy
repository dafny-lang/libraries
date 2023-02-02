include "Wrappers.dfy"

module {:options "-functionSyntax:4"} Result {

  import opened Wrappers 

  /**********************************************************
  *
  *  Monadic structure in terms of Return, Bind, Join, Map, Composition 
  *
  ***********************************************************/

  datatype Result<+T,+E> = | Success(value: T) | Failure(error: E)

  function Return<T,E>(v: T): Result<T,E> {
    Result.Success(v)
  }

  function Bind<S,T,E>(r: Result<S,E>, f: S -> Result<T,E>): Result<T,E> {
    match r
    case Success(v) => f(v)
    case Failure(e) => Result<T,E>.Failure(e)
  }

  function Join<T,E>(rr: Result<Result<T,E>,E>): Result<T,E> {
    match rr
    case Success(v) => v
    case Failure(e) => Result<T,E>.Failure(e)
  }

  function Map<S,T,E>(f: S -> T): Result<S,E> -> Result<T,E> {
    (r: Result<S,E>) =>
      match r 
      case Success(v) => Result<T,E>.Success(f(v))
      case Failure(e) => Result<T,E>.Failure(e)
  }

  function MapError<T,E1,E2>(f: E1 -> E2): Result<T,E1> -> Result<T,E2> {
    (r: Result<T,E1>) =>
      match r 
      case Success(v) => Result<T,E2>.Success(v)
      case Failure(e) => Result<T,E2>.Failure(f(e))
  } 

  function Composition<S,T,U,E>(f: S -> Result<T,E>, g: T -> Result<U,E>): S -> Result<U,E> {
    s => Bind(f(s), g)
  }

  /**********************************************************
  *
  *  Get and set
  *
  ***********************************************************/

  function Success<T,E>(v: T): Result<T,E> {
    Result.Success(v)
  }

  function Failure<T,E>(e: E): Result<T,E> {
    Result.Failure(e)
  } 

  predicate IsSuccess<T,E>(r: Result<T,E>) {
    r.Success?
  }  

  predicate IsFailure<T,E>(r: Result<T,E>) {
    r.Failure?
  }  

  function GetValue<T,E>(r: Result<T,E>): T
    requires r.Success?
  {
    r.value
  }

  function GetValueDefault<T,E>(r: Result<T,E>, default: T): T {
    match r 
    case Success(v) => v
    case Failure(_) => default
  }

  function GetError<T,E>(r: Result<T,E>): E 
    requires r.Failure?
  {
    r.error
  }

  /**********************************************************
  *
  *  Fold
  *
  ***********************************************************/

  function Fold<T,E,U>(f: T -> U, g: E -> U): Result<T,E> -> U {
    (r: Result<T,E>) =>
      match r 
      case Success(v) => f(v)
      case Failure(e) => g(e)
  }

  /**********************************************************
  *
  *  Comparison
  *
  ***********************************************************/

  function Equal<T,E>(eqs: (T, T) -> bool, eqf: (E, E) -> bool): (Result<T,E>, Result<T,E>) -> bool {
    (r1: Result<T,E>, r2: Result<T,E>) =>
      match (r1, r2)
      case (Success(v1), Success(v2)) => eqs(v1, v2)
      case (Failure(e1), Failure(e2)) => eqf(e1, e2)
      case _ => false
  }

  function Compare<T,E>(cmps: (T, T) -> int, cmpf: (E, E) -> int): (Result<T,E>, Result<T,E>) -> int {
    (r1: Result<T,E>, r2: Result<T,E>) =>
      match (r1, r2)
      case (Success(v1), Success(v2)) => cmps(v1, v2)
      case (Failure(e1), Failure(e2)) => cmpf(e1, e2)
      case (Success(_), Failure(_)) => -1
      case (Failure(_), Success(_)) => 1
  }

  /**********************************************************
  *
  *  Conversion to other datatypes
  *
  ***********************************************************/

  function ToSeq<T,E>(r: Result<T,E>): seq<T> {
    match r
    case Success(v) => [v]
    case Failure(_) => []
  }

  function ToSet<T,E>(r: Result<T,E>): set<T> {
    match r
    case Success(v) => {v}
    case Failure(_) => {}   
  }

  function ToOption<T,E>(r: Result<T,E>): Option<T> {
    match r
    case Success(v) => Some(v)
    case Failure(_) => None()
  }

  /**********************************************************
  *
  *  Monad laws in terms of Join and Map
  *
  ***********************************************************/

  lemma LemmaUnitalityJoin<T,E>(r: Result<T,E>)
    ensures Join(Map(Return<T,E>)(r)) == r == Join(Return<Result<T,E>,E>(r))
  {
  }

  lemma LemmaAssociativityJoin<T,E>(rrr: Result<Result<Result<T,E>,E>,E>) 
    ensures Join(Map(Join<T,E>)(rrr)) == Join(Join<Result<T,E>,E>(rrr))
  {
  }  

  /**********************************************************
  *
  *  Monad laws in terms of Bind and Return
  *
  ***********************************************************/

  lemma LemmaLeftUnitalityBind<S,T,E>(v: S, f: S -> Result<T,E>)
    ensures Bind(Return(v), f) == f(v)
  {
  }

  lemma LemmaRightUnitalityBind<T,E>(r: Result<T,E>)
    ensures Bind(r, Return) == r
  {
  }

  lemma LemmaAssociativityBind<S,T,U,E>(r: Result<S,E>, f: S -> Result<T,E>, g: T -> Result<U,E>)
    ensures Bind(Bind(r, f), g) == Bind(r, Composition(f, g))
  {
  }

  /**********************************************************
  *
  *  Monad laws in terms of (Kleisli) Composition and Return
  *
  ***********************************************************/

  lemma LemmaAssociativityComposition<S,T,U,V,E>(f: S -> Result<T,E>, g: T -> Result<U,E>, h: U -> Result<V,E>)
    ensures forall s: S :: Composition(Composition(f, g), h)(s) == Composition(f, Composition(g, h))(s)
  {
  }

  lemma LemmaIdentityExtract<S,T,E>(f: S -> Result<T,E>)
    ensures forall s: S :: Composition(f, Return<T,E>)(s) == f(s) == Composition(Return<S,E>, f)(s)
  {
  }

}


