// RUN: %dafny /compile:0 "%s"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/
include "Relations.dfy"

module {:options "-functionSyntax:4"} Wrappers {
  module {:options "-functionSyntax:4"} Result {
    import opened Option

    datatype Result<T(!new,==),E(!new)> = | Success(value: T) | Failure(error: E) {
      predicate IsSuccess() {
        Success?
      }  

      predicate IsFailure() {
        Failure?
      }  

      function GetValue(): T
        requires Success?
      {
        value
      }

      function GetValueDefault(default: T): T {
        match this 
        case Success(v) => v
        case Failure(_) => default
      }

      function PropagateFailure<S>(): Result<S,E>
        requires Failure?
      {
        Failure(error)
      }

      function GetError(): E 
        requires Failure?
      {
        error
      }

      function Extract(): T
        requires Success?
      {
        value
      }

      function ToOption(): Option<T> {
        match this
        case Success(v) => Some(v)
        case Failure(_) => None
      }

      function ToSeq(): seq<T> {
        match this
        case Success(v) => [v]
        case Failure(_) => []
      }

      function ToSet(): set<T> {
        match this
        case Success(v) => {v}
        case Failure(_) => {}   
      }
    }
    
    function Return<T,E>(v: T): Result<T,E> {
      Result.Success(v)
    }

    function Bind<S(!new),T(!new),E(!new)>(r: Result<S,E>, f: S -> Result<T,E>): Result<T,E> {
      match r
      case Success(v) => f(v)
      case Failure(e) => Result<T,E>.Failure(e)
    }

    function Join<T(!new,==),E(!new,==)>(rr: Result<Result<T,E>,E>): Result<T,E> {
      match rr
      case Success(v) => v
      case Failure(e) => Result<T,E>.Failure(e)
    }

    function Map<S(!new),T(!new),E(!new)>(f: S -> T): Result<S,E> -> Result<T,E> {
      (r: Result<S,E>) =>
        match r 
        case Success(v) => Result<T,E>.Success(f(v))
        case Failure(e) => Result<T,E>.Failure(e)
    }

    function MapError<T(!new),E1(!new),E2(!new)>(f: E1 -> E2): Result<T,E1> -> Result<T,E2> {
      (r: Result<T,E1>) =>
        match r 
        case Success(v) => Result<T,E2>.Success(v)
        case Failure(e) => Result<T,E2>.Failure(f(e))
    } 

    function KleisliComposition<S(!new),T(!new),U(!new),E(!new)>(f: S -> Result<T,E>, g: T -> Result<U,E>): S -> Result<U,E> {
      s => Bind(f(s), g)
    }

    function Success<T,E>(v: T): Result<T,E> {
      Result.Success(v)
    }

    function Failure<T,E>(e: E): Result<T,E> {
      Result.Failure(e)
    } 

    function Fold<T(!new),E(!new),U>(f: T -> U, g: E -> U): Result<T,E> -> U {
      (r: Result<T,E>) =>
        match r 
        case Success(v) => f(v)
        case Failure(e) => g(e)
    }

    function Equal<T(!new),E(!new)>(eqt: (T, T) -> bool, eqe: (E, E) -> bool): (Result<T,E>, Result<T,E>) -> bool {
      (r1: Result<T,E>, r2: Result<T,E>) =>
        match (r1, r2)
        case (Success(v1), Success(v2)) => eqt(v1, v2)
        case (Failure(e1), Failure(e2)) => eqe(e1, e2)
        case _ => false
    }

    function Compare<T(!new),E(!new)>(cmps: (T, T) -> int, cmpf: (E, E) -> int): (Result<T,E>, Result<T,E>) -> int {
      (r1: Result<T,E>, r2: Result<T,E>) =>
        match (r1, r2)
        case (Success(v1), Success(v2)) => cmps(v1, v2)
        case (Failure(e1), Failure(e2)) => cmpf(e1, e2)
        case (Success(_), Failure(_)) => -1
        case (Failure(_), Success(_)) => 1
    }
  }

  module {:options "-functionSyntax:4"} Writer {
    datatype Writer<T> = Result(value: T, log: string) {
      function GetValue<T>(w: Writer<T>): T {
        w.value
      }

      function GetLog<T>(w: Writer<T>): string {
        w.log
      }
    }

    function Return<T>(v: T): Writer<T> {
      Result(v, "")
    }

    function Bind<S,T>(w: Writer<S>, f: S -> Writer<T>): Writer<T> {
      Writer<T>.Result(f(w.value).value, w.log + f(w.value).log)
    }

    function Join<T>(ww: Writer<Writer<T>>): Writer<T> {
      Result((ww.value).value, (ww.value).log + ww.log)
    }

    function Map<S,T>(f: S -> T): Writer<S> -> Writer<T> {
      (w: Writer<S>) => Writer<T>.Result(f(w.value), w.log)
    }

    function KleisliComposition<S,T,U>(f: S -> Writer<T>, g: T -> Writer<U>): S -> Writer<U> {
      s => Bind(f(s), g)
    }

    function Result<T>(v: T, s: string): Writer<T> {
      Writer<T>.Result(v, s)
    }

    ghost function Equal<T(!new)>(eq: (T, T) -> bool): (Writer<T>, Writer<T>) -> bool {
      (w1: Writer<T>, w2: Writer<T>) => 
        && eq(w1.value, w2.value) 
        && w1.log == w2.log
    }
  }

  module {:options "-functionSyntax:4"} Option {
    datatype Option<+T(==)> = None | Some(value: T) {
      function GetValueDefault(default: T): T {
        match this
        case None => default
        case Some(v) => v
      }

      function GetValue(): T
        requires Some?
      {
        value
      }

      predicate IsFailure() {
        None?
      }

      function Extract(): T
        requires Some?
      {
        value
      }

      function PropagateFailure<S>(): Option<S>
        requires None?
      {
        None
      }

      function ToSeq(): seq<T> {
        match this 
        case None => []
        case Some(v) => [v]
      }

      function ToSet(): set<T> {
        match this
        case None => {}
        case Some(v) => {v}
      }
    }

    function Return<T>(v: T): Option<T> {
      Option.Some(v)
    }

    function Bind<S,T>(o: Option<S>, f: S -> Option<T>): Option<T> {
      match o 
      case None => Option<T>.None
      case Some(v) => f(v)
    }

    function Join<T>(oo: Option<Option<T>>): Option<T> {
      match oo
      case None => Option<T>.None
      case Some(o) => o
    }

    function Map<S,T>(f: S -> T): Option<S> -> Option<T>
    {
      (o: Option<S>) =>
        match o 
        case None => Option<T>.None
        case Some(v) => Option<T>.Some(f(v))
    }

    function KleisliComposition<S,T,U>(f: S -> Option<T>, g: T-> Option<U>): S -> Option<U> {
      s => Bind(f(s), g)
    }

    function Fold<T,U>(u: U, f: T -> U): Option<T> -> U {
      (o: Option<T>) =>
        match o 
        case None => u
        case Some(v) => f(v)
    }

    function Equal<T>(eq: (T, T) -> bool): (Option<T>, Option<T>) -> bool {
      (o1: Option<T>, o2: Option<T>) =>
        match (o1, o2)
        case (Some(v1), Some(v2)) => eq(v1, v2)
        case (None, None) => true
        case _ => false
    }
    
    function Compare<T>(cmp: (T, T) -> int): (Option<T>, Option<T>) -> int {
      (o1: Option<T>, o2: Option<T>) =>
        match (o1, o2)
        case (Some(v1), Some(v2)) => cmp(v1, v2)
        case (None, None) => 0
        case (None, Some(_)) => -1
        case (Some(_), None) => 1
    }
  }

  module {:options "-functionSyntax:4"} Either {
    import opened Option

    datatype Either<+S,+T> = Left(left: S) | Right(right: T) {
      predicate IsLeft() {
        Left?
      }

      predicate IsRight() {
        Right?
      }

      function FindLeft(): Option<S> {
        match this 
        case Left(v) => Some(v)
        case Right(v) => None
      }

      function FindRight(): Option<T> {
        match this
        case Left(v) => None
        case Right(v) => Some(v)
      }
    }

    function ReturnLeft<S,T>(v: S): Either<S,T> {
      Either.Left(v)
    }

    function ReturnRight<S,T>(v: T): Either<S,T> {
      Either.Right(v)
    }

    function JoinRight<S,T>(ee: Either<S,Either<S,T>>): Either<S,T> {
      match ee
      case Left(v) => Either<S,T>.Left(v)
      case Right(v) => v
    }

    function JoinLeft<S,T>(ee: Either<Either<S,T>,T>): Either<S,T> {
      match ee
      case Left(v) => v
      case Right(v) => Either<S,T>.Right(v)
    }

    function MapLeft<S,T,U>(f: S -> T): Either<S,U> -> Either<T,U> {
      (e: Either<S,U>) =>
      match e 
      case Left(v) => Either<T,U>.Left(f(v))
      case Right(v) => Either<T,U>.Right(v)
    }

    function MapRight<S,T,U>(f: T -> U): Either<S,T> -> Either<S,U> {
      (e: Either<S,T>) =>
      match e 
      case Left(v) => Either<S,U>.Left(v)
      case Right(v) => Either<S,U>.Right(f(v))
    }

    function Map<S1,S2,T1,T2>(f: S1 -> S2, g: T1 -> T2): Either<S1,T1> -> Either<S2,T2> {
      (e: Either<S1,T1>) =>
        match e
        case Left(v) => Either<S2,T2>.Left(f(v))
        case Right(v) => Either<S2,T2>.Right(g(v))
    }

    function Fold<S,T,U>(f: S -> U, g: T -> U): Either<S,T> -> U {
      (e: Either<S,T>) =>
        match e
        case Left(v) => f(v)
        case Right(v) => g(v)
    }

    function Equal<S,T>(eql: (S, S) -> bool, eqr: (T, T) -> bool): (Either<S,T>, Either<S,T>) -> bool {
      (e1: Either<S,T>, e2: Either<S,T>) =>
        match (e1, e2)
        case (Left(v1), Left(v2)) => eql(v1, v2)
        case (Right(v1), Right(v2)) => eqr(v1, v2)
        case _ => false
    }

    function Compare<S,T>(cmpl: (S, S) -> int, cmpr: (T, T) -> int): (Either<S,T>, Either<S,T>) -> int {
      (e1: Either<S,T>, e2: Either<S,T>) =>
        match (e1, e2)
        case (Left(v1), Left(v2)) => cmpl(v1, v2)
        case (Right(v1), Right(v2)) => cmpr(v1, v2)
        case (Left(_), Right(_)) => -1
        case (Right(_), Left(_)) => 1
    }
  }

  module {:options "-functionSyntax:4"} Reader {
    datatype Reader<-X,+T> = Reader(f: X -> T)

    function Return<X,T>(t: T): Reader<X,T> {
      Reader(x => t)
    }

    function Bind<X,S,T>(r: Reader<X,S>, f: S -> Reader<X,T>): Reader<X,T> {
      Reader(x => (f((r.f)(x)).f)(x))
    }

    function Join<X,T>(rr: Reader<X,Reader<X,T>>): Reader<X,T> {
      Reader(x => (rr.f(x)).f(x))
    }

    function Map<X,S,T>(f: S -> T): Reader<X,S> -> Reader<X,T> {
      (r: Reader<X,S>) => 
        Reader(x => f((r.f)(x)))
    }

    function MapContra<X,Y,T>(f: X -> Y): Reader<Y,T> -> Reader<X,T> {
      (r: Reader<Y,T>) =>
        Reader(x => r.f(f(x)))
    }

    function KleisliComposition<X,S,T,U>(f: S -> Reader<X,T>, g: T -> Reader<X,U>): S -> Reader<X,U> {
      s => Bind(f(s), g)
    } 

    ghost function Equal<X(!new),T>(eq: (T, T) -> bool): (Reader<X,T>, Reader<X,T>) -> bool 
    {
      (r1: Reader<X,T>, r2: Reader<X,T>) => 
        forall x: X :: eq(r1.f(x), r2.f(x))
    }
  }

  module {:options "-functionSyntax:4"} List {
    type List<+T> = seq<T>

    function MapCurry<S,T>(f: S -> T, xs: List<S>): List<T> {
      if xs == [] then 
        []
      else 
        [f(xs[0])] + MapCurry(f, xs[1..])
    }

    function Map<S,T>(f: S -> T): (List<S> -> List<T>) {
      xs => MapCurry(f, xs)
    }

    function Return<T>(t: T): List<T> {
      [t]
    }

    function Join<T>(xxs: List<List<T>>): List<T> {
      if xxs == [] then
        []
      else
        xxs[0] + Join(xxs[1..])
    }

    function Bind<S,T>(xs: List<S>, f: S -> List<T>): List<T> {
      Join(Map(f)(xs))
    }

    function KleisliComposition<S,T,U>(f: S -> List<T>, g: T -> List<U>): S -> List<U> {
      s => Bind(f(s), g)
    } 

    ghost function Equal<T>(eq: (T, T) -> bool): (List<T>, List<T>) -> bool 
    {
      (xs: List<T>, ys: List<T>) => 
        && |xs| == |ys| 
        && forall i | 0 <= i < |xs| :: eq(xs[i], ys[i])
    }
  }

  module {:options "-functionSyntax:4"} Powerset {
    type Set<T> = set<T>

    ghost function Return<T>(x: T): Set<T> {
      {x}
    }

    ghost function MapCurry<S,T>(f: S -> T, xs: Set<S>): Set<T> 
      decreases |xs|
    {
      if xs == {} then
        {}
      else 
        var x :| x in xs;
        {f(x)} + MapCurry(f, xs - {x})
    }

    ghost function Map<S,T>(f: S -> T): Set<S> -> Set<T> {
      (xs: Set<S>) => MapCurry(f, xs)
    }

    ghost function Join<T>(xxs: Set<Set<T>>): Set<T> {
      if xxs == {} then
        {}
      else 
        var xs :| xs in xxs;
        xs + Join(xxs - {xs})
    }

    ghost function Bind<S,T>(xs: Set<S>, f: S -> Set<T>): Set<T> {
      Join(Map(f)(xs))
    }

    ghost function KleisliComposition<S,T,U>(f: S -> Set<T>, g: T -> Set<U>): S -> Set<U> {
      s => Bind(f(s), g)
    }

    ghost function Equal<T>(eq: (T, T) -> bool): (Set<T>, Set<T>) -> bool 
    {
      (s1: Set<T>, s2: Set<T>) =>
        && (forall x | x in s1 :: (exists y | y in s2 :: eq(x, y)))
        && (forall x | x in s2 :: (exists y | y in s1 :: eq(x, y)))
    }
  }
    

  module {:options "-functionSyntax:4"} Outcome {
    import Result 

    datatype Outcome<E> = Pass | Fail(error: E) {
        predicate IsFailure() {
          Fail?
        }
        // Note: PropagateFailure returns a Result, not an Outcome.
        function PropagateFailure<U>(): Result.Result<U, E>
          requires Fail?
        {
          Result.Failure(this.error)
        }
        // Note: no Extract method
      }

      // A helper function to ensure a requirement is true at runtime
      // :- Need(5 == |mySet|, "The set MUST have 5 elements.")
      function Need<E>(condition: bool, error: E): (result: Outcome<E>)
      {
        if condition then Pass else Fail(error)
    }
  }

  function ToResult<T>(o: Option.Option<T>): Result.Result<T,string> {
    match o
    case Some(v) => Result.Success(v)
    case None => Result.Failure("Option is None")
  }
}  