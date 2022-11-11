// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run --no-verify --target:js "%s" --input "%S/../../src/FileIO/FileIO.js" -- "%S/ReadBytesFromFile.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.expect" "%t"

include "./AbstractReadBytesFromFile.dfy"
include "../../src/FileIO/FileIO.js.dfy"

module Test refines AbstractTest {
  import AbstractFileIO = FileIO

  function method ExpectedErrorMessagePrefix(): string {
    "Error: ENOENT"
  }
}
