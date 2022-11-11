// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run --no-verify --target:js "%s" --input "%S/../../src/FileIO/FileIO.js" -- "%t.data" >> "%t"
// RUN: %diff "%S/WriteBytesToFile.expect" "%t"
// RUN: %diff "%S/WriteBytesToFile.data.expect" "%t.data"

include "./AbstractWriteBytesToFile.dfy"
include "../../src/FileIO/FileIO.js.dfy"

module Test refines AbstractTest {
  import AbstractFileIO = FileIO

  function method ExpectedErrorMessagePrefix(): string {
    "Error: ENOENT"
  }
}
