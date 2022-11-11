/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT
*******************************************************************************/

// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %baredafny run --no-verify --target:cs "%s" --input "%S/../../src/FileIO/FileIO.cs" -- "%t.cs.out" "System.ArgumentException:" >> "%t"
// RUN: %baredafny run --no-verify --target:java "%s" --input "%S/../../src/FileIO/FileIO.java" -- "%t.java.out" "java.nio.file.FileSystemException:" >> "%t"
// RUN: %baredafny run --no-verify --target:js "%s" --input "%S/../../src/FileIO/FileIO.js" -- "%t.js.out" "Error: ENOENT" >> "%t"
// TODO: %baredafny run --no-verify --target:py "%s" --input "%S/../../src/FileIO/FileIO.py" -- "%t.py.out" "[Errno 2]" >> "%t"
// RUN: %diff "%s.expect" "%t"

//// Check that written files match expectations
// RUN: %diff "data.txt" "%t.cs.out"
// RUN: %diff "data.txt" "%t.java.out"
// RUN: %diff "data.txt" "%t.js.out"
// TODO: %diff "data.txt" "%t.py.out"

include "../../src/FileIO/FileIO.dfy"

module WriteBytesToFile {
  import FileIO

  method Main(args: seq<string>) {
    expect |args| > 0;
    expect |args| == 3, "usage: " + args[0] + " OUTPUT_PATH EXPECTED_ERROR_PREFIX";
    var outputPath := args[1];
    var expectedErrorPrefix := args[2];

    // Happy path: write to the output path. (The %diff LIT commands check that we wrote the correct content.)
    {
      // Ideally we would define `str` as a constant and compute `bytes` automatically.
      // To do so, we would need to convert each `char` in `str` to a `bv8` value, by using `as bv8`.
      // But that triggers a bug in the Java compiler: <https://github.com/dafny-lang/dafny/issues/2942>.
      // So for now we settle for manually writing out the desired `bytes`,
      // and statically verifying that these values match the characters of `str`.
      ghost var str := "Hello world\nGoodbye\n";
      var bytes: seq<bv8> := [
        // "Hello world\n"
        0x48, 0x65, 0x6c, 0x6c, 0x6f, 0x20, 0x77, 0x6f, 0x72, 0x6c, 0x64, 0x0a,
        // "Goodbye\n"
        0x47, 0x6f, 0x6f, 0x64, 0x62, 0x79, 0x65, 0x0a
      ];
      assert forall i | 0 <= i < |bytes| :: bytes[i] as int == str[i] as int;

      var res := FileIO.WriteBytesToFile(outputPath, bytes);
      expect res.Success?, "unexpected failure: " + res.error;
    }

    // Failure path: attempting to write to a blank file path should never work.
    {
      var res := FileIO.WriteBytesToFile("", []);
      expect res.Failure?, "unexpected success";
      expect expectedErrorPrefix <= res.error, "unexpected error message: " + res.error;
    }
  }
}
