module {:options "-functionSyntax:4"} Writer {

  datatype Writer<T> = Result(value: T, log: string)

  function GetValue<T>(w: Writer<T>): T {
    w.value
  }

  function GetLog<T>(w: Writer<T>): string {
    w.log
  }

  function Return<T>(v: T): Writer<T> {
    Result(v, "")
  }

  function Join<T>(ww: Writer<Writer<T>>): Writer<T> {
    Result((ww.value).value, (ww.value).log + ww.log)
  }

  function Map<S,T>(f: S -> T): Writer<S> -> Writer<T> {
    (w: Writer<S>) => Writer<T>.Result(f(w.value), w.log)
  }

  function Bind<S,T>(w: Writer<S>, f: S -> Writer<T>): Writer<T> {
    Writer<T>.Result(f(w.value).value, w.log + f(w.value).log)
  }

  lemma LemmaUnitalityJoin<T>(w: Writer<T>)
    ensures Join(Map(Return<T>)(w)) == w == Join(Return<Writer<T>>(w))
  {
  }

}
