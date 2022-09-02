include "../ZeroCopy/API.dfy"

module {:extern "Benchmarks"} JSON.Benchmarks.Benchmark {
  import opened BoundedInts

  import opened Grammar
  import ZeroCopy.Serializer
  import ZeroCopy.Deserializer
  import ZeroCopy.API

  const WARMUP:  uint32 := 20
  const REPEATS: uint32 := 80

  class {:extern} {:compile false} Interop {
    static method {:extern} ReadInput() returns (s: array<byte>) ensures fresh(s)
    static method {:extern} StartTimer()
    static method {:extern} ReportTimer(lbl: string, nBytes: int, repeats: uint32)
  }

  method Deserialize(bytes: seq<byte>) {
    for i := 0 to WARMUP {
      var _ := API.Deserialize(bytes);
    }
    Interop.StartTimer();
    for i := 0 to REPEATS {
      var _ := API.Deserialize(bytes);
    }
    Interop.ReportTimer("Deserialize", |bytes|, REPEATS);
  }

  method Serialize(js: JSON, target: array<byte>)
    modifies target
  {
    for i := 0 to WARMUP {
      var _ := API.SerializeBlit(js, target);
    }
    Interop.StartTimer();
    for i := 0 to REPEATS {
      var _ := API.SerializeBlit(js, target);
    }
    Interop.ReportTimer("Serialize", target.Length, REPEATS);
  }

  method Main() {
    var input_array := Interop.ReadInput();
    var bytes := input_array[..];

    var output_array := new byte[input_array.Length];
    var jsr := API.Deserialize(bytes);
    expect jsr.Success?;
    Deserialize(bytes);

    var js := jsr.value;
    var output := API.SerializeAlloc(js);
    expect output.Success?;
    Serialize(js, output_array);
  }
}
