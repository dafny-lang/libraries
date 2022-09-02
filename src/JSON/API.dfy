include "Errors.dfy"
include "Grammar.dfy"
include "Spec.dfy"
include "Serializer.dfy"
include "Deserializer.dfy"
include "ZeroCopy/API.dfy"

module {:options "-functionSyntax:4"} JSON.API {
  // TODO: Propagate proofs

  import opened BoundedInts
  import opened Wrappers
  import Vs = Utils.Views.Core

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
