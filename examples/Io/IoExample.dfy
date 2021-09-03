// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

include "../../src/Io/Io.dfy"
include "../../src/NativeTypes.dfy"

module IoExample {

  import opened Io
  import opened NativeTypes

  /* Useful to convert Dafny strings into arrays of characters. */
  method ArrayFromSeq<A>(s: seq<A>) returns (a: array<A>)
    ensures a[..] == s
  {
    a := new A[|s|] ( i requires 0 <= i < |s| => s[i] );
  }

  method {:main} Main(ghost env: HostEnvironment)
    requires env.ok.ok()
    modifies env.ok
  {
      var fname := ArrayFromSeq("foo.txt");
      var f: FileStream;
      var ok: bool;
      
      var numArgs := HostConstants.NumCommandLineArgs(env);
      if numArgs < 1 {
        print "Error: invalid number of command line arguments\n";
        return;
      }
      print "# command line args: ";
      print numArgs;
      print "\n";

      var arg0 := HostConstants.GetCommandLineArg(0, env);
      print "command: " + arg0[..] + "\n";
      
      var fileExists := FileStream.FileExists(fname, env);
      if fileExists {
        print fname[..] + " exists!\n";

        var ok, len := FileStream.FileLength(fname, env);
        if !ok { print "Error: invalid file length\n"; return; }
        print fname[..] + " length: ";
        print len;
        print "\n";
      }

      ok, f := FileStream.Open(fname, env);
      if !ok { print "Error: open failed\n"; return; }

      /* This is "hello world!" in ascii. */
      var data: array<uint8> := ArrayFromSeq([104, 101, 108, 108, 111, 32, 119, 111, 114, 108, 100, 33, 10]);

      ok := f.Write(0, data, 0, data.Length as int32);
      if !ok { print "Error: write failed\n"; return; }

      ok := f.Close();

      print "done!\n";
  }

}
