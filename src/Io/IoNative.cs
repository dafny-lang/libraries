using System;
using FStream = System.IO.FileStream;

namespace @IoNative {

public partial class HostConstants
{
  public static uint NumCommandLineArgs()
  {
    return (uint)System.Environment.GetCommandLineArgs().Length;
  }

  public static char[] GetCommandLineArg(ulong i)
  {
    return System.Environment.GetCommandLineArgs()[i].ToCharArray();
  }
}

public partial class FileStream
{
  internal FStream fstream;
  internal FileStream(FStream fstream) { this.fstream = fstream; }

  public static bool FileExists(char[] name)
  {
    return System.IO.File.Exists(new string(name));      
  }
  
  public static void FileLength(char[] name, out bool success, out int len)
  {
    len = -1;
    try {
      System.IO.FileInfo fi = new System.IO.FileInfo(new string(name));
      if (fi.Length < System.Int32.MaxValue) {  // We only support small files
        len = (int)fi.Length;
        success = true;
      }
      else {
        success = false;
      }
      
    }
    catch (Exception e) {
      System.Console.Error.WriteLine(e);
      success = false;
    }     
  }

  public static void Open(char[] name, out bool ok, out FileStream f)
  {
    try {
      f = new FileStream(new FStream(new string(name), System.IO.FileMode.OpenOrCreate, System.IO.FileAccess.ReadWrite));
      ok = true;
    }
    catch (Exception e) {
      System.Console.Error.WriteLine(e);
      f = null;
      ok = false;
    }
  }

  public bool Close()
  {
    try {
      fstream.Close();
      return true;
    }
    catch (Exception e) {
      System.Console.Error.WriteLine(e);
      return false;
    }
  }

  public bool Read(int fileOffset, byte[] buffer, int start, int end)
  {
    try {
      fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
      fstream.Read(buffer, start, end - start);
      return true;
    }
    catch (Exception e) {
      System.Console.Error.WriteLine(e);
      return false;
    }
  }

  public bool Write(int fileOffset, byte[] buffer, int start, int end)
  {
    try {
      fstream.Seek(fileOffset, System.IO.SeekOrigin.Begin);
      fstream.Write(buffer, start, end - start);
      return true;
    }
    catch (Exception e) {
      System.Console.Error.WriteLine(e);
      return false;
    }
  }

  public bool Flush()
  {
    try {
      fstream.Flush();
      return true;
    }
    catch (Exception e) {
      System.Console.Error.WriteLine(e);
      return false;
    }
  }
}

}
