include "Wrappers.dfy"

module {:options "-functionSyntax:4"} Result {

  import opened Wrappers 

  datatype Result<+S,+E> = | Success(value: S) | Failure(error: E)

  function Success<S,E>(v: S): Result<S,E> {
    Result.Success(v)
  }

  function Failure<S,E>(e: E): Result<S,E> {
    Result.Failure(e)
  }

  predicate IsSuccess<S,E>(r: Result<S,E>) {
    r.Success?
  }  

  predicate IsFailure<S,E>(r: Result<S,E>) {
    r.Failure?
  }  

  function GetValue<S,E>(r: Result<S,E>): S 
    requires r.Success?
  {
    r.value
  }

  function GetValueDefault<S,E>(r: Result<S,E>, default: S): S {
    match r 
    case Success(v) => v
    case Failure(_) => default
  }

  function GetError<S,E>(r: Result<S,E>): E 
    requires r.Failure?
  {
    r.error
  }

  function Bind<S1,S2,E>(r: Result<S1,E>, f: S1 -> Result<S2,E>): Result<S2,E> {
    match r
    case Success(v) => f(v)
    case Failure(e) => Result<S2,E>.Failure(e)
  }

  function Join<S,E>(rr: Result<Result<S,E>,E>): Result<S,E> {
    match rr
    case Success(v) => v
    case Failure(e) => Result<S,E>.Failure(e)
  }

  function Map<S1,S2,E>(f: S1 -> S2): Result<S1,E> -> Result<S2,E> {
    (r: Result<S1,E>) =>
      match r 
      case Success(v) => Result<S2,E>.Success(f(v))
      case Failure(e) => Result<S2,E>.Failure(e)
  }

  function MapError<S,E1,E2>(f: E1 -> E2): Result<S,E1> -> Result<S,E2> {
    (r: Result<S,E1>) =>
      match r 
      case Success(v) => Result<S,E2>.Success(v)
      case Failure(e) => Result<S,E2>.Failure(f(e))
  }  

  function ToOption<S,E>(r: Result<S,E>): Option<S> {
    match r
    case Success(v) => Some(v)
    case Failure(_) => None()
  }

  function Fold<S,E,T>(f: S -> T, g: E -> T): Result<S,E> -> T {
    (r: Result<S,E>) =>
      match r 
      case Success(v) => f(v)
      case Failure(e) => g(e)
  }

  function ToSeq<S,E>(r: Result<S,E>): seq<S> {
    match r
    case Success(v) => [v]
    case Failure(_) => []
  }

  function ToSet<S,E>(r: Result<S,E>): set<S> {
    match r
    case Success(v) => {v}
    case Failure(_) => {}   
  }

  function Composition<S1,S2,S3,E>(f: S1 -> Result<S2,E>, g: S2 -> Result<S3,E>): S1 -> Result<S3,E> {
    x => Bind(f(x), g)
  }

  lemma LemmaUnitalityJoin<S,E>(r: Result<S,E>)
    ensures Join(Map(Success<S,E>)(r)) == r == Join(Success<Result<S,E>,E>(r))
  {
  }

  lemma LemmaAssociativityJoin<S,E>(rrr: Result<Result<Result<S,E>,E>,E>) 
    ensures Join(Map(Join<S,E>)(rrr) ) == Join(Join<Result<S,E>,E>(rrr))
  {
  }  

  lemma LemmaLeftUnitalityBind<S1,S2,E>(v: S1, f: S1 -> Result<S2,E>)
    ensures Bind(Success(v), f) == f(v)
  {
  }

  lemma LemmaRightUnitalityBind<S,E>(r: Result<S,E>)
    ensures Bind(r, Success) == r
  {
  }

  lemma LemmaAssociativityBind<S1,S2,S3,E>(r: Result<S1,E>, f: S1 -> Result<S2,E>, g: S2 -> Result<S3,E>)
    ensures Bind(Bind(r, f), g) == Bind(r, Composition(f, g))
  {
  }

}


