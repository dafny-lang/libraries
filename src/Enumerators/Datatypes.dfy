module DatatypeEnumerator {

  datatype E<T> = Done | Next(T, Enum<T>)
  type Enum<T> = () -> E<T>

  function OneTwoThree(): Enum<nat> {
    () => Next(1, () => Next(2, () => Next(3, () => Done)))
  }

  function CountdownFrom(n: nat): Enum<nat> {
    () => 
      if n > 0 then
        Next(n, CountdownFrom(n - 1))
      else
        Done
  }

  // Doesn't terminate so you can't do this
  // function CountupFrom(n: nat): Enum<nat> {
  //   () => Next(n, CountupFrom(n + 1))
  // }
}