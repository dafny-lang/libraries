module {:options "-functionSyntax:4"} JSON.AST {
  datatype KV = KV(k: string, v: Value)
  datatype Decimal = Decimal(n: int, e10: nat) // (n) * 10^(e10)
  datatype Value =
    | Null
    | Bool(b: bool)
    | String(str: string)
    | Number(num: Decimal)
    | Object(obj: seq<KV>) // Not a map to preserve order
    | Array(arr: seq<Value>)
}
