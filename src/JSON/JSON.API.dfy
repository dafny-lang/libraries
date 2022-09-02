include "JSON.Errors.dfy"
include "JSON.Grammar.dfy"
include "JSON.Spec.dfy"
include "JSON.Serializer.dfy"
include "JSON.Deserializer.dfy"
include "JSON.ZeroCopy.API.dfy"

module {:options "-functionSyntax:4"} JSON.API {
  // TODO: Propagate proofs

  import opened BoundedInts
  import opened Wrappers
  import Vs = Views.Core

  import opened Errors
  import opened AST
  import Spec
  import S = Serializer
  import DS = Deserializer
  import ZAPI = ZeroCopy.API

  function {:opaque} Serialize(js: JSON) : (bs: SerializationResult<seq<byte>>)
  {
    var js :- S.JSON(js);
    Success(ZAPI.Serialize(js))
  }

  method SerializeAlloc(js: JSON) returns (bs: SerializationResult<array<byte>>)
  {
    var js :- S.JSON(js);
    bs := ZAPI.SerializeAlloc(js);
  }

  method SerializeBlit(js: JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
    modifies bs
  {
    var js :- S.JSON(js);
    len := ZAPI.SerializeBlit(js, bs);
  }

  function {:opaque} Deserialize(bs: seq<byte>) : (js: DeserializationResult<JSON>)
  {
    var js :- ZAPI.Deserialize(bs);
    DS.JSON(js)
  }
}
