// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../../src/FileIO/AbstractFileIO.dfy"

abstract module AbstractTest {
  import AbstractFileIO : AbstractFileIO

  function method ExpectedErrorMessagePrefix(): string

  method Main(args: seq<string>) {
    {
      var expectedStr := "Hello world\nGoodbye\n";
      var expectedBytes := seq(|expectedStr|, i requires 0 <= i < |expectedStr| => expectedStr[i] as int);

      expect |args| == 2;
      var dataFilePath := args[1];

      var res := AbstractFileIO.ReadBytesFromFile(dataFilePath);
      expect res.Success?, "unexpected failure: " + res.error;

      var readBytes := seq(|res.value|, i requires 0 <= i < |res.value| => res.value[i] as int);
      expect readBytes == expectedBytes, "read unexpected byte sequence";
    }

    {
      var res := AbstractFileIO.ReadBytesFromFile("");
      expect res.Failure?, "unexpected success";
      expect ExpectedErrorMessagePrefix() <= res.error, "unexpected error message: " + res.error;
    }
  }
}
