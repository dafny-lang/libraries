// RUN: %verify "%s"

include "Serializer.dfy"
include "Deserializer.dfy"
include "ZeroCopy/API.dfy"

module {:options "-functionSyntax:4"} JSON.API {
  import opened BoundedInts
  import opened Errors
  import AST
  import Serializer
  import Deserializer
  import ZeroCopy = ZeroCopy.API

  function {:opaque} Serialize(js: AST.JSON) : (bs: SerializationResult<seq<byte>>)
  {
    var js :- Serializer.JSON(js);
    ZeroCopy.Serialize(js)
  }

  method SerializeAlloc(js: AST.JSON) returns (bs: SerializationResult<array<byte>>)
  {
    var js :- Serializer.JSON(js);
    bs := ZeroCopy.SerializeAlloc(js);
  }

  method SerializeInto(js: AST.JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
    modifies bs
  {
    var js :- Serializer.JSON(js);
    len := ZeroCopy.SerializeInto(js, bs);
  }

  function {:opaque} Deserialize(bs: seq<byte>) : (js: DeserializationResult<AST.JSON>)
  {
    var js :- ZeroCopy.Deserialize(bs);
    Deserializer.JSON(js)
  }
}
