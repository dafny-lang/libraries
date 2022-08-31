include "JSON.Grammar.dfy"
include "JSON.LowLevel.Spec.dfy"
include "JSON.ZeroCopy.Serializer.dfy"
include "JSON.ZeroCopy.Deserializer.dfy"

module {:options "/functionSyntax:4"} JSON.ZeroCopy.API {
  import opened BoundedInts
  import opened Wrappers
  import Vs = Views.Core

  import opened Grammar
  import Spec
  import Serializer
  import Deserializer

  function {:opaque} Serialize(js: JSON) : (bs: seq<byte>)
    ensures bs == Spec.JSON(js)
  {
    Serializer.Text(js).Bytes()
  }

  method SerializeAlloc(js: JSON) returns (bs: Result<array<byte>, Serializer.Error>)
    ensures bs.Success? ==> fresh(bs.value)
    ensures bs.Success? ==> bs.value[..] == Spec.JSON(js)
  {
    bs := Serializer.Serialize(js);
  }

  method SerializeBlit(js: JSON, bs: array<byte>) returns (len: Result<uint32, Serializer.Error>)
    modifies bs
    ensures len.Success? ==> len.value as int <= bs.Length
    ensures len.Success? ==> bs[..len.value] == Spec.JSON(js)
    ensures len.Success? ==> bs[len.value..] == old(bs[len.value..])
    ensures len.Failure? ==> unchanged(bs)
  {
    len := Serializer.SerializeTo(js, bs);
  }

  function {:opaque} Deserialize(bs: seq<byte>) : (js: Result<JSON, Deserializer.Error>)
    ensures js.Success? ==> bs == Spec.JSON(js.value)
  {
    Deserializer.API.OfBytes(bs)
  }
}
