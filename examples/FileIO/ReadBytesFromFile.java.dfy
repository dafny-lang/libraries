// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run --no-verify --target:java "%s" --input "%S/../../src/FileIO/FileIO.java" -- "%S/ReadBytesFromFile.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.expect" "%t"

include "./AbstractReadBytesFromFile.dfy"
include "../../src/FileIO/FileIO.java.dfy"

module Test refines AbstractTest {
  import AbstractFileIO = FileIO

  function method ExpectedErrorMessagePrefix(): string {
    "java.io.IOException: "
  }
}
