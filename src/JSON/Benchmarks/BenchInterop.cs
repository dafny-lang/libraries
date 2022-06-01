using System.Diagnostics;
using System.Numerics;

namespace Benchmarks {
  public class Interop {
    private static readonly Stopwatch Chrono = new();

    public static byte[] ReadInput() {
      return File.ReadAllBytes("twitter.json");
    }

    public static void StartTimer() {
      Chrono.Start();
    }

    public static void ReportTimer(Dafny.ISequence<char> label, BigInteger nBytes, uint repeats) {
      Chrono.Stop();
      var sizeMB = (long)(nBytes * repeats) / 1000.0 / 1000.0;
      var speed = sizeMB * 1000 / Chrono.ElapsedMilliseconds ;
      Console.WriteLine($"{label}: {sizeMB} MB in {Chrono.Elapsed} ({speed} MB/s)");
    }
  }
}
