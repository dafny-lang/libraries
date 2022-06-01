include "../JSON.ZeroCopy.API.dfy"

module {:extern "Benchmarks"} Benchmarks {
  import opened BoundedInts

  import opened JSON.Grammar
  import JSON.ZeroCopy.Serializer
  import JSON.ZeroCopy.Deserializer
  import JSON.ZeroCopy.API

  const WARMUP:  uint32 := 20
  const REPEATS: uint32 := 80

  class {:extern} {:compile false} Interop {
    static method {:extern} ReadInput() returns (s: array<byte>) ensures fresh(s)
    static method {:extern} StartTimer()
    static method {:extern} ReportTimer(lbl: string, nBytes: int, repeats: uint32)
  }

  method Serialize(bytes: seq<byte>) {
    for i := 0 to WARMUP {
      var _ := API.Deserialize(bytes);
    }
    Interop.StartTimer();
    for i := 0 to REPEATS {
      var _ := API.Deserialize(bytes);
    }
    Interop.ReportTimer("Serialize", |bytes|, REPEATS);
  }

  method Deserialize(js: JSON, target: array<byte>)
    modifies target
  {
    for i := 0 to WARMUP {
      var _ := API.SerializeBlit(js, target);
    }
    Interop.StartTimer();
    for i := 0 to REPEATS {
      var _ := API.SerializeBlit(js, target);
    }
    Interop.ReportTimer("Deserialize", target.Length, REPEATS);
  }

  method Main() {
    var input_array := Interop.ReadInput();
    var output_array := new byte[input_array.Length];

    var bytes := input_array[..];
    var jsr := API.Deserialize(bytes);
    expect jsr.Success?;

    var js := jsr.value;
    var output := API.SerializeAlloc(js);
    expect output.Success?;

    Serialize(bytes);
    Deserialize(js, output_array);
  }
}
