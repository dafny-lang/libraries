module {:options "-functionSyntax:4"} JSON.AST {
  datatype Decimal =
    Decimal(n: int, e10: int) // (n) * 10^(e10)
  datatype JSON =
    | Null
    | Bool(b: bool)
    | String(str: string)
    | Number(num: Decimal)
    | Object(obj: seq<(string, JSON)>) // Not a map to preserve order
    | Array(arr: seq<JSON>)
}
