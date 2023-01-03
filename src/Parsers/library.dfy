module {:options "/functionSyntax:4"} Library {
  // Library
  datatype Option<T> = Some(value: T) | None
  datatype Result<T> = Success(value: T) | Failure(s: string, pos: int) {
    predicate IsFailure() {
      Failure?
    }
    function PropagateFailure<U>(): Result<U>
      requires IsFailure()
    {
      Failure(s, pos)
    }
    function Extract(): T
      requires !IsFailure()
    {
      value
    }
  }
}
module {:options "/functionSyntax:4"} Printer {

  type stringNat = s: string |
    |s| > 0 && (|s| > 1 ==> s[0] != '0') &&
    forall i | 0 <= i < |s| :: s[i] in "0123456789"
    witness "1"

  function natToString(n: nat): stringNat {
    match n
    case 0 => "0" case 1 => "1" case 2 => "2" case 3 => "3" case 4 => "4"
    case 5 => "5" case 6 => "6" case 7 => "7" case 8 => "8" case 9 => "9"
    case _ => natToString(n / 10) + natToString(n % 10)
  }

  function stringToNat(s: stringNat): nat
    decreases |s|
  {
    if |s| == 1 then
      match s[0]
      case '0' => 0 case '1' => 1 case '2' => 2 case '3' => 3 case '4' => 4
      case '5' => 5 case '6' => 6 case '7' => 7 case '8' => 8 case '9' => 9
    else
      stringToNat(s[..|s|-1])*10 + stringToNat(s[|s|-1..|s|])
  }

  lemma natToStringThenStringToNatIdem(n: nat)
    ensures stringToNat(natToString(n)) == n
  { // Proof is automatic
  }
  lemma stringToNatThenNatToStringIdem(n: stringNat)
    ensures natToString(stringToNat(n)) == n
  { // Proof is automatic
  }
}