// RUN: %dafny /compile:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

include "../NativeTypes.dfy"

module {:extern "IoNative"} Io {

  import opened NativeTypes

  //////////////////////////////////////////////////////////////////////////////
  // Per-host constants
  //////////////////////////////////////////////////////////////////////////////

  class HostConstants
  {
    constructor {:extern} () requires false

    /* Result of C# System.Environment.GetCommandLineArgs(); argument 0 is name
    of executable. */  
    function {:extern} CommandLineArgs(): seq<string> reads this

    static method {:extern} NumCommandLineArgs(ghost env: HostEnvironment) returns (n: uint32)
      ensures n as int == |env.constants.CommandLineArgs()|

    static method {:extern} GetCommandLineArg(i: uint64, ghost env: HostEnvironment) returns (arg: array<char>)
      requires 0 <= i as int < |env.constants.CommandLineArgs()|
      ensures  arg[..] == env.constants.CommandLineArgs()[i]
  }

  //////////////////////////////////////////////////////////////////////////////
  // Failure
  //////////////////////////////////////////////////////////////////////////////

  class OkState
  {
    constructor {:extern} () requires false
    function {:extern} ok(): bool reads this
  }

  //////////////////////////////////////////////////////////////////////////////
  // File System
  //////////////////////////////////////////////////////////////////////////////

  class FileSystemState
  {
    constructor {:extern} () requires false

    /* File system maps file names to their contents. */
    function {:extern} state(): map<string, seq<uint8>>
      reads this
  }

  class HostEnvironment
  {
    ghost var constants: HostConstants
    ghost var ok: OkState
    ghost var files: FileSystemState
  }

  class FileStream
  {
    ghost var env: HostEnvironment
    function {:extern} Name(): string reads this
    function {:extern} IsOpen(): bool reads this
    constructor {:extern} () requires false

    static method {:extern} FileExists(name: array<char>, ghost env: HostEnvironment) returns (result: bool)
      requires env.ok.ok()      
      ensures  result <==> old(name[..]) in env.files.state()      

    static method {:extern} FileLength(name: array<char>, ghost env: HostEnvironment) returns (success: bool, len: int32)
      requires env.ok.ok()   
      requires name[..] in env.files.state()
      modifies env.ok
      ensures  env.ok.ok() == success
      ensures  success ==> len as int == |env.files.state()[name[..]]|

    static method {:extern} Open(name: array<char>, ghost env: HostEnvironment)
      returns (ok: bool, f: FileStream)
      requires env.ok.ok()
      modifies env.ok
      ensures  env.ok.ok() == ok
      ensures  ok ==> fresh(f) && f.env == env && f.IsOpen() && f.Name() == name[..]

    method {:extern} Close() returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      modifies this
      modifies env.ok
      ensures  env == old(env)
      ensures  env.ok.ok() == ok

    method {:extern} Read(fileOffset: nat32, buffer: array<uint8>, start: int32, end: int32) returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      requires 0 <= start as int <= end as int <= buffer.Length
      modifies this
      modifies env.ok
      modifies buffer
      ensures  env == old(env)
      ensures  env.ok.ok() == ok
      ensures  Name() == old(Name())
      ensures  forall i:int :: 0 <= i < buffer.Length && !(start as int <= i < end as int) ==> buffer[i] == old(buffer[i])
      ensures  ok ==> IsOpen()

    method {:extern} Write(fileOffset: nat32, buffer: array<uint8>, start: int32, end: int32) returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      requires 0 <= start as int <= end as int <= buffer.Length
      modifies this
      modifies env.ok
      ensures  env == old(env)
      ensures  env.ok.ok() == ok
      ensures  Name() == old(Name())
      ensures  ok ==> IsOpen()

    method {:extern} Flush() returns (ok: bool)
      requires env.ok.ok()
      requires IsOpen()
      modifies this
      modifies env.ok
      ensures  env == old(env)
      ensures  env.ok.ok() == ok
      ensures  Name() == old(Name())
      ensures  ok ==> IsOpen()
  }

}
