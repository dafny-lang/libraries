module {:options "-functionSyntax:4"} Writer {

  /**********************************************************
  *
  *  Monadic structure in terms of Return, Bind, Join, Map, Composition 
  *
  ***********************************************************/

  datatype Writer<T> = Result(value: T, log: string)

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

  function Composition<S,T,U>(f: S -> Writer<T>, g: T -> Writer<U>): S -> Writer<U> {
    s => Bind(f(s), g)
  }

  /**********************************************************
  *
  *  Get and set
  *
  ***********************************************************/

  function GetValue<T>(w: Writer<T>): T {
    w.value
  }

  function GetLog<T>(w: Writer<T>): string {
    w.log
  }

  function Result<T>(v: T, s: string): Writer<T> {
    Writer<T>.Result(v, s)
  }

  /**********************************************************
  *
  *  Monad laws in terms of Join and Map
  *
  ***********************************************************/

  lemma LemmaUnitalityJoin<T>(w: Writer<T>)
    ensures Join(Map(Return<T>)(w)) == w == Join(Return<Writer<T>>(w))
  {
  }

  lemma LemmaAssociativityJoin<T>(www: Writer<Writer<Writer<T>>>) 
    ensures Join(Map(Join<T>)(www)) == Join(Join<Writer<T>>(www))
  {
  }  

  /**********************************************************
  *
  *  Monad laws in terms of Bind and Return
  *
  ***********************************************************/

  lemma LemmaLeftUnitalityBind<S,T>(v: S, f: S -> Writer<T>)
    ensures Bind(Return(v), f) == f(v)
  {
  }

  lemma LemmaRightUnitalityBind<T>(w: Writer<T>)
    ensures Bind(w, Return) == w
  {
  }

  lemma LemmaAssociativityBind<S,T,U>(w: Writer<S>, f: S -> Writer<T>, g: T -> Writer<U>)
    ensures Bind(Bind(w, f), g) == Bind(w, Composition(f, g))
  {
  }

  /**********************************************************
  *
  *  Monad laws in terms of (Kleisli) Composition and Return
  *
  ***********************************************************/

  lemma LemmaAssociativityComposition<S,T,U,V>(f: S -> Writer<T>, g: T -> Writer<U>, h: U -> Writer<V>)
    ensures forall s: S :: Composition(Composition(f, g), h)(s) == Composition(f, Composition(g, h))(s)
  {
  }

  lemma LemmaIdentityExtract<S,T>(f: S -> Writer<T>)
    ensures forall s: S :: Composition(f, Return<T>)(s) == f(s) == Composition(Return<S>, f)(s)
  {
  }
}
