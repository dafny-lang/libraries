// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run --no-verify --target:py "%s" --input "%S/../../src/FileIO/FileIO.py" -- "%S/ReadBytesFromFile.data" >> "%t"
// RUN: %diff "%S/ReadBytesFromFile.expect" "%t"

include "./AbstractReadBytesFromFile.dfy"
include "../../src/FileIO/FileIO.dfy"

module Test refines AbstractTest {
  function method ExpectedErrorMessagePrefix(): string {
    "[Errno 2]"
  }
}
