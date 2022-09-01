include "JSON.Errors.dfy"
include "JSON.Grammar.dfy"
include "JSON.Spec.dfy"
include "JSON.Serializer.dfy"
include "JSON.ZeroCopy.Serializer.dfy"

module {:options "-functionSyntax:4"} JSON.API {
  import opened BoundedInts
  import opened Wrappers
  import Vs = Views.Core

  import opened Errors
  import opened AST
  import Spec
  import S = Serializer
  import ZS = ZeroCopy.Serializer
  // import Deserializer

  function {:opaque} Serialize(js: JSON) : (bs: SerializationResult<seq<byte>>)
    // TODO: Carry proofs all the way
    // ensures bs.Success? ==> bs.value == Spec.JSON(js)
  {
    var js :- S.JSON(js);
    Success(ZS.Text(js).Bytes())
  }

  method SerializeAlloc(js: JSON) returns (bs: SerializationResult<array<byte>>)
    // TODO: Carry proofs all the way
    // ensures bs.Success? ==> fresh(bs.value)
    // ensures bs.Success? ==> bs.value[..] == Spec.JSON(js)
  {
    var js :- S.JSON(js);
    bs := ZS.Serialize(js);
  }

  method SerializeBlit(js: JSON, bs: array<byte>) returns (len: SerializationResult<uint32>)
    modifies bs
    // TODO: Carry proofs all the way
    // ensures len.Success? ==> len.value as int <= bs.Length
    // ensures len.Success? ==> bs[..len.value] == Spec.JSON(js)
    // ensures len.Success? ==> bs[len.value..] == old(bs[len.value..])
    // ensures len.Failure? ==> unchanged(bs)
  {
    var js :- S.JSON(js);
    len := ZS.SerializeTo(js, bs);
  }

  // function {:opaque} Deserialize(bs: seq<byte>) : (js: Result<JSON, Deserializer.Error>)
  //   ensures js.Success? ==> bs == Spec.JSON(js.value)
  // {
  //   Deserializer.API.OfBytes(bs)
  // }
}
