// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run --no-verify --target:cs "%s" --input "%S/../../src/FileIO/FileIO.cs" -- "%S/data.txt" "System.ArgumentException:" >> "%t"
// RUN: %baredafny run --no-verify --target:java "%s" --input "%S/../../src/FileIO/FileIO.java" -- "%S/data.txt" "java.io.IOException:" >> "%t"
// RUN: %baredafny run --no-verify --target:js "%s" --input "%S/../../src/FileIO/FileIO.js" -- "%S/data.txt" "Error: ENOENT" >> "%t"
// TODO: %baredafny run --no-verify --target:py "%s" --input "%S/../../src/FileIO/FileIO.py" -- "%S/data.txt" "[Errno 2]" >> "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/FileIO/FileIO.dfy"

module ReadBytesFromFile {
  import FileIO

  method Main(args: seq<string>) {
    expect |args| > 0;
    expect |args| == 3, "usage: " + args[0] + " DATA_PATH EXPECTED_ERROR_PREFIX";
    var dataPath := args[1];
    var expectedErrorPrefix := args[2];

    {
      var expectedStr := "Hello world\nGoodbye\n";
      var expectedBytes := seq(|expectedStr|, i requires 0 <= i < |expectedStr| => expectedStr[i] as int);

      var res := FileIO.ReadBytesFromFile(dataPath);
      expect res.Success?, "unexpected failure: " + res.error;

      var readBytes := seq(|res.value|, i requires 0 <= i < |res.value| => res.value[i] as int);
      expect readBytes == expectedBytes, "read unexpected byte sequence";
    }

    {
      var res := FileIO.ReadBytesFromFile("");
      expect res.Failure?, "unexpected success";
      expect expectedErrorPrefix <= res.error, "unexpected error message: " + res.error;
    }
  }
}
