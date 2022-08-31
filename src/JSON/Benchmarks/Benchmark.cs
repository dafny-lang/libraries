// Dafny program Benchmark.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using System.Runtime.CompilerServices;
using Cursors_Compile;
using JSON_mGrammar_Compile;

namespace Dafny {
  internal class ArrayHelpers {
    public static T[] InitNewArray1<T>(T z, BigInteger size0) {
      int s0 = (int)size0;
      T[] a = new T[s0];
      for (int i0 = 0; i0 < s0; i0++) {
        a[i0] = z;
      }
      return a;
    }
  }
} // end of namespace Dafny
public static class FuncExtensions {
  public static Func<U, UResult> DowncastClone<T, TResult, U, UResult>(this Func<T, TResult> F, Func<U, T> ArgConv, Func<TResult, UResult> ResConv) {
    return arg => ResConv(F(ArgConv(arg)));
  }
  public static Func<UResult> DowncastClone<TResult, UResult>(this Func<TResult> F, Func<TResult, UResult> ResConv) {
    return () => ResConv(F());
  }
  public static Func<U1, U2, UResult> DowncastClone<T1, T2, TResult, U1, U2, UResult>(this Func<T1, T2, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<TResult, UResult> ResConv) {
    return (arg1, arg2) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2)));
  }
  public static Func<U1, U2, U3, UResult> DowncastClone<T1, T2, T3, TResult, U1, U2, U3, UResult>(this Func<T1, T2, T3, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3)));
  }
  public static Func<U1, U2, U3, U4, U5, UResult> DowncastClone<T1, T2, T3, T4, T5, TResult, U1, U2, U3, U4, U5, UResult>(this Func<T1, T2, T3, T4, T5, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<U5, T5> ArgConv5, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4, arg5) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4), ArgConv5(arg5)));
  }
  public static Func<U1, U2, U3, U4, UResult> DowncastClone<T1, T2, T3, T4, TResult, U1, U2, U3, U4, UResult>(this Func<T1, T2, T3, T4, TResult> F, Func<U1, T1> ArgConv1, Func<U2, T2> ArgConv2, Func<U3, T3> ArgConv3, Func<U4, T4> ArgConv4, Func<TResult, UResult> ResConv) {
    return (arg1, arg2, arg3, arg4) => ResConv(F(ArgConv1(arg1), ArgConv2(arg2), ArgConv3(arg3), ArgConv4(arg4)));
  }
}
namespace _System {

  public partial class nat {
    private static readonly Dafny.TypeDescriptor<BigInteger> _TYPE = new Dafny.TypeDescriptor<BigInteger>(BigInteger.Zero);
    public static Dafny.TypeDescriptor<BigInteger> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public struct Tuple3GOO<T1, T2> {
    public readonly T1 _0;
    public readonly T2 _1;
    public Tuple3GOO(T1 _0, T2 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public Tuple3GOO<__T1, __T2> DowncastClone<__T1, __T2>(Func<T1, __T1> converter0, Func<T2, __T2> converter1) {
      if (this is Tuple3GOO<__T1, __T2> dt) { return dt; }
      return new Tuple3GOO<__T1, __T2>(converter0(_0), converter1(_1));
    }
    public override bool Equals(object other) {
      return other is  _System.Tuple3GOO<T1, T2> oth && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._0));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this._1));
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += Dafny.Helpers.ToString(this._0);
      s += ", ";
      s += Dafny.Helpers.ToString(this._1);
      s += ")";
      return s;
    }
    public static Tuple3GOO<T1, T2> Default(T1 _default_T1, T2 _default_T2) {
      return create(_default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System.Tuple3GOO<T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System.Tuple3GOO<T1, T2>>(_System.Tuple3GOO<T1, T2>.Default(_td_T1.Default(), _td_T2.Default()));
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Tuple3GOO<T1, T2> create(T1 _0, T2 _1) {
      return new Tuple3GOO<T1, T2>(_0, _1);
    }
    public T1 dtor__0 {
      get {
        return this._0;
      }
    }
    public T2 dtor__1 {
      get {
        return this._1;
      }
    }
  }

  public struct Tuple0 {
    public Tuple0() {
    }
    public Tuple0 DowncastClone() {
      if (this is Tuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      return other is _System.Tuple0;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly Tuple0 theDefault = create();
    public static Tuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System.Tuple0> _TYPE = new Dafny.TypeDescriptor<_System.Tuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System.Tuple0> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Tuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<Tuple0> AllSingletonConstructors {
      get {
        yield return Tuple0.create();
      }
    }
  }
} // end of namespace _System
namespace BoundedInts_Compile {

  public partial class uint8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class uint64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int8 {
    public static System.Collections.Generic.IEnumerable<sbyte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (sbyte)j; }
    }
    private static readonly Dafny.TypeDescriptor<sbyte> _TYPE = new Dafny.TypeDescriptor<sbyte>(0);
    public static Dafny.TypeDescriptor<sbyte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int16 {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int32 {
    public static System.Collections.Generic.IEnumerable<int> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (int)j; }
    }
    private static readonly Dafny.TypeDescriptor<int> _TYPE = new Dafny.TypeDescriptor<int>(0);
    public static Dafny.TypeDescriptor<int> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class int64 {
    public static System.Collections.Generic.IEnumerable<long> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (long)j; }
    }
    private static readonly Dafny.TypeDescriptor<long> _TYPE = new Dafny.TypeDescriptor<long>(0);
    public static Dafny.TypeDescriptor<long> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat8 {
    public static System.Collections.Generic.IEnumerable<byte> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (byte)j; }
    }
    private static readonly Dafny.TypeDescriptor<byte> _TYPE = new Dafny.TypeDescriptor<byte>(0);
    public static Dafny.TypeDescriptor<byte> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat16 {
    public static System.Collections.Generic.IEnumerable<ushort> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ushort)j; }
    }
    private static readonly Dafny.TypeDescriptor<ushort> _TYPE = new Dafny.TypeDescriptor<ushort>(0);
    public static Dafny.TypeDescriptor<ushort> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat32 {
    public static System.Collections.Generic.IEnumerable<uint> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (uint)j; }
    }
    private static readonly Dafny.TypeDescriptor<uint> _TYPE = new Dafny.TypeDescriptor<uint>(0);
    public static Dafny.TypeDescriptor<uint> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class nat64 {
    public static System.Collections.Generic.IEnumerable<ulong> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (ulong)j; }
    }
    private static readonly Dafny.TypeDescriptor<ulong> _TYPE = new Dafny.TypeDescriptor<ulong>(0);
    public static Dafny.TypeDescriptor<ulong> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class opt__byte {
    public static System.Collections.Generic.IEnumerable<short> IntegerRange(BigInteger lo, BigInteger hi) {
      for (var j = lo; j < hi; j++) { yield return (short)j; }
    }
    private static readonly Dafny.TypeDescriptor<short> _TYPE = new Dafny.TypeDescriptor<short>(0);
    public static Dafny.TypeDescriptor<short> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static BigInteger TWO__TO__THE__8 { get {
      return new BigInteger(256);
    } }
    public static byte UINT8__MAX { get {
      return 255;
    } }
    public static BigInteger TWO__TO__THE__16 { get {
      return new BigInteger(65536);
    } }
    public static ushort UINT16__MAX { get {
      return 65535;
    } }
    public static BigInteger TWO__TO__THE__32 { get {
      return new BigInteger(4294967296L);
    } }
    public static uint UINT32__MAX { get {
      return 4294967295U;
    } }
    public static BigInteger TWO__TO__THE__64 { get {
      return BigInteger.Parse("18446744073709551616");
    } }
    public static ulong UINT64__MAX { get {
      return 18446744073709551615UL;
    } }
    public static sbyte INT8__MIN { get {
      return -128;
    } }
    public static sbyte INT8__MAX { get {
      return 127;
    } }
    public static short INT16__MIN { get {
      return -32768;
    } }
    public static short INT16__MAX { get {
      return 32767;
    } }
    public static int INT32__MIN { get {
      return -2147483648;
    } }
    public static int INT32__MAX { get {
      return 2147483647;
    } }
    public static long INT64__MIN { get {
      return -9223372036854775808L;
    } }
    public static long INT64__MAX { get {
      return 9223372036854775807L;
    } }
    public static byte NAT8__MAX { get {
      return 127;
    } }
    public static ushort NAT16__MAX { get {
      return 32767;
    } }
    public static uint NAT32__MAX { get {
      return 2147483647U;
    } }
    public static ulong NAT64__MAX { get {
      return 9223372036854775807UL;
    } }
    public static BigInteger TWO__TO__THE__0 { get {
      return BigInteger.One;
    } }
    public static BigInteger TWO__TO__THE__1 { get {
      return new BigInteger(2);
    } }
    public static BigInteger TWO__TO__THE__2 { get {
      return new BigInteger(4);
    } }
    public static BigInteger TWO__TO__THE__4 { get {
      return new BigInteger(16);
    } }
    public static BigInteger TWO__TO__THE__5 { get {
      return new BigInteger(32);
    } }
    public static BigInteger TWO__TO__THE__24 { get {
      return new BigInteger(16777216);
    } }
    public static BigInteger TWO__TO__THE__40 { get {
      return new BigInteger(1099511627776L);
    } }
    public static BigInteger TWO__TO__THE__48 { get {
      return new BigInteger(281474976710656L);
    } }
    public static BigInteger TWO__TO__THE__56 { get {
      return new BigInteger(72057594037927936L);
    } }
    public static BigInteger TWO__TO__THE__128 { get {
      return BigInteger.Parse("340282366920938463463374607431768211456");
    } }
    public static BigInteger TWO__TO__THE__256 { get {
      return BigInteger.Parse("115792089237316195423570985008687907853269984665640564039457584007913129639936");
    } }
    public static BigInteger TWO__TO__THE__512 { get {
      return BigInteger.Parse("13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084096");
    } }
  }
} // end of namespace BoundedInts_Compile
namespace Views_mCore_Compile {

  public partial class View {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(Views_mCore_Compile.View.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public struct View__ {
    public readonly Dafny.ISequence<byte> s;
    public readonly uint beg;
    public readonly uint end;
    public View__(Dafny.ISequence<byte> s, uint beg, uint end) {
      this.s = s;
      this.beg = beg;
      this.end = end;
    }
    public View__ DowncastClone() {
      if (this is View__ dt) { return dt; }
      return new View__(s, beg, end);
    }
    public override bool Equals(object other) {
      return other is Views_mCore_Compile.View__ oth && object.Equals(this.s, oth.s) && this.beg == oth.beg && this.end == oth.end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Views_mCore_Compile.View_.View";
      ss += "(";
      ss += Dafny.Helpers.ToString(this.s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.end);
      ss += ")";
      return ss;
    }
    private static readonly View__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0);
    public static View__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(Views_mCore_Compile.View__.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static View__ create(Dafny.ISequence<byte> s, uint beg, uint end) {
      return new View__(s, beg, end);
    }
    public bool is_View { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this.s;
      }
    }
    public uint dtor_beg {
      get {
        return this.beg;
      }
    }
    public uint dtor_end {
      get {
        return this.end;
      }
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public static Views_mCore_Compile.View__ OfBytes(Dafny.ISequence<byte> bs) {
      return Views_mCore_Compile.View__.create(bs, (uint)(0U), (uint)(bs).LongCount);
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public short Peek() {
      if ((this).Empty_q) {
        return -1;
      } else {
        return (short)((this).At(0U));
      }
    }
    public void Blit(byte[] bs, uint start)
    {
      uint _hi0 = (this).Length();
      for (uint _0_idx = 0U; _0_idx < _hi0; _0_idx++) {
        var ndex0 = (start) + (_0_idx);
        (bs)[(int)(ndex0)] = ((this).dtor_s).Select(((this).dtor_beg) + (_0_idx));
      }
    }
    public static Views_mCore_Compile.View__ Empty { get {
      return Views_mCore_Compile.View__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U);
    } }
    public bool Empty_q { get {
      return ((this).dtor_beg) == ((this).dtor_end);
    } }
  }

  public partial class __default {
    public static bool Adjacent(Views_mCore_Compile.View__ lv, Views_mCore_Compile.View__ rv)
    {
      return (((lv).dtor_s).Equals(((rv).dtor_s))) && (((lv).dtor_end) == ((rv).dtor_beg));
    }
    public static Views_mCore_Compile.View__ Merge(Views_mCore_Compile.View__ lv, Views_mCore_Compile.View__ rv)
    {
      Views_mCore_Compile.View__ _1_dt__update__tmp_h0 = lv;
      uint _2_dt__update_hend_h0 = (rv).dtor_end;
      return Views_mCore_Compile.View__.create((_1_dt__update__tmp_h0).dtor_s, (_1_dt__update__tmp_h0).dtor_beg, _2_dt__update_hend_h0);
    }
  }
} // end of namespace Views_mCore_Compile
namespace Wrappers_Compile {


  public abstract class Option<T> {
    public Option() { }
    public static Option<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile.Option<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile.Option<T>>(Wrappers_Compile.Option<T>.Default());
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Option<T> create_None() {
      return new Option_None<T>();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Option<T> create_Some(T @value) {
      return new Option_Some<T>(@value);
    }
    public bool is_None { get { return this is Option_None<T>; } }
    public bool is_Some { get { return this is Option_Some<T>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Option_Some<T>)d).@value;
      }
    }
    public abstract Option<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers_Compile.Result<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile.Option<T> _source0 = this;
      if (_source0.is_None) {
        return new Wrappers_Compile.Result_Failure<T, Dafny.ISequence<char>>(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _3___mcc_h0 = _source0.dtor_value;
        T _4_v = _3___mcc_h0;
        return new Wrappers_Compile.Result_Success<T, Dafny.ISequence<char>>(_4_v);
      }
    }
    public static T UnwrapOr(Wrappers_Compile.Option<T> _this, T @default) {
      Wrappers_Compile.Option<T> _source1 = _this;
      if (_source1.is_None) {
        return @default;
      } else {
        T _5___mcc_h0 = _source1.dtor_value;
        T _6_v = _5___mcc_h0;
        return _6_v;
      }
    }
    public bool IsFailure() {
      return (this).is_None;
    }
    public Wrappers_Compile.Option<__U> PropagateFailure<__U>() {
      return Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public sealed class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override Option<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is Option<__T> dt) { return dt; }
      return new Option_None<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_None<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.None";
      return s;
    }
  }
  public sealed class Option_Some<T> : Option<T> {
    public readonly T @value;
    public Option_Some(T @value) {
      this.@value = @value;
    }
    public override Option<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is Option<__T> dt) { return dt; }
      return new Option_Some<__T>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Option_Some<T>;
      return oth != null && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Option.Some";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }

  public abstract class Result<T, R> {
    public static Result<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile.Result<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile.Result<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Result<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Result<T, R> create_Failure(R error) {
      return new Result_Failure<T, R>(error);
    }
    public bool is_Success { get { return this is Result_Success<T, R>; } }
    public bool is_Failure { get { return this is Result_Failure<T, R>; } }
    public T dtor_value {
      get {
        var d = this;
        return ((Result_Success<T, R>)d).@value;
      }
    }
    public R dtor_error {
      get {
        var d = this;
        return ((Result_Failure<T, R>)d).error;
      }
    }
    public abstract Result<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers_Compile.Option<T> ToOption() {
      Wrappers_Compile.Result<T, R> _source2 = this;
      if (_source2.is_Success) {
        T _7___mcc_h0 = _source2.dtor_value;
        T _8_s = _7___mcc_h0;
        return Wrappers_Compile.Option<T>.create_Some(_8_s);
      } else {
        R _9___mcc_h1 = _source2.dtor_error;
        R _10_e = _9___mcc_h1;
        return Wrappers_Compile.Option<T>.create_None();
      }
    }
    public static T UnwrapOr(Wrappers_Compile.Result<T, R> _this, T @default) {
      Wrappers_Compile.Result<T, R> _source3 = _this;
      if (_source3.is_Success) {
        T _11___mcc_h0 = _source3.dtor_value;
        T _12_s = _11___mcc_h0;
        return _12_s;
      } else {
        R _13___mcc_h1 = _source3.dtor_error;
        R _14_e = _13___mcc_h1;
        return @default;
      }
    }
    public bool IsFailure() {
      return (this).is_Failure;
    }
    public Wrappers_Compile.Result<__U, R> PropagateFailure<__U>() {
      return new Wrappers_Compile.Result_Failure<__U, R>((this).dtor_error);
    }
    public static Wrappers_Compile.Result<T, __NewR> MapFailure<__NewR>(Wrappers_Compile.Result<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers_Compile.Result<T, R> _source4 = _this;
      if (_source4.is_Success) {
        T _15___mcc_h0 = _source4.dtor_value;
        T _16_s = _15___mcc_h0;
        return new Wrappers_Compile.Result_Success<T, __NewR>(_16_s);
      } else {
        R _17___mcc_h1 = _source4.dtor_error;
        R _18_e = _17___mcc_h1;
        return new Wrappers_Compile.Result_Failure<T, __NewR>(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_18_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public sealed class Result_Success<T, R> : Result<T, R> {
    public readonly T @value;
    public Result_Success(T @value) {
      this.@value = @value;
    }
    public override Result<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is Result<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(@value));
    }
    public override bool Equals(object other) {
      return other is Wrappers_Compile.Result_Success<T, R> oth && object.Equals(this.@value, oth.@value);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.@value));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Success";
      s += "(";
      s += Dafny.Helpers.ToString(this.@value);
      s += ")";
      return s;
    }
  }
  public sealed class Result_Failure<T, R> : Result<T, R> {
    public readonly R error;
    public Result_Failure(R error) {
      this.error = error;
    }
    public override Result<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is Result<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(error));
    }
    public override bool Equals(object other) {
      return other is Wrappers_Compile.Result_Failure<T, R> oth && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Result.Failure";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public abstract class Outcome<E> {
    public Outcome() { }
    public static Outcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile.Outcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile.Outcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Outcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Outcome<E> create_Fail(E error) {
      return new Outcome_Fail<E>(error);
    }
    public bool is_Pass { get { return this is Outcome_Pass<E>; } }
    public bool is_Fail { get { return this is Outcome_Fail<E>; } }
    public E dtor_error {
      get {
        var d = this;
        return ((Outcome_Fail<E>)d).error;
      }
    }
    public abstract Outcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile.Result<__U, E> PropagateFailure<__U>() {
      return new Wrappers_Compile.Result_Failure<__U, E>((this).dtor_error);
    }
  }
  public sealed class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override Outcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is Outcome<__E> dt) { return dt; }
      return new Outcome_Pass<__E>();
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Pass<E>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Pass";
      return s;
    }
  }
  public sealed class Outcome_Fail<E> : Outcome<E> {
    public readonly E error;
    public Outcome_Fail(E error) {
      this.error = error;
    }
    public override Outcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is Outcome<__E> dt) { return dt; }
      return new Outcome_Fail<__E>(converter0(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Outcome_Fail<E>;
      return oth != null && object.Equals(this.error, oth.error);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.error));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Wrappers_Compile.Outcome.Fail";
      s += "(";
      s += Dafny.Helpers.ToString(this.error);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static Wrappers_Compile.Outcome<__E> Need<__E>(bool condition, __E error)
    {
      if (condition) {
        return Wrappers_Compile.Outcome<__E>.create_Pass();
      } else {
        return Wrappers_Compile.Outcome<__E>.create_Fail(error);
      }
    }
  }
} // end of namespace Wrappers_Compile
namespace Views_mWriters_Compile {

  public abstract class Chain {
    public Chain() { }
    private static readonly Chain theDefault = create_Empty();
    public static Chain Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile.Chain> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile.Chain>(Views_mWriters_Compile.Chain.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile.Chain> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Chain create_Empty() {
      return new Chain_Empty();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Chain create_Chain(Views_mWriters_Compile.Chain previous, Views_mCore_Compile.View__ v) {
      return new Chain_Chain(previous, v);
    }
    public bool is_Empty { get { return this is Chain_Empty; } }
    public bool is_Chain { get { return this is Chain_Chain; } }
    public Views_mWriters_Compile.Chain dtor_previous {
      get {
        var d = this;
        return ((Chain_Chain)d).previous;
      }
    }
    public Views_mCore_Compile.View__ dtor_v {
      get {
        var d = this;
        return ((Chain_Chain)d).v;
      }
    }
    public abstract Chain DowncastClone();
    public BigInteger Length() {
      BigInteger _19___accumulator = BigInteger.Zero;
      Chain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_19___accumulator);
      } else {
        _19___accumulator = (new BigInteger(((_this).dtor_v).Length())) + (_19___accumulator);
        var n0 = (_this).dtor_previous;
        _this = n0;
        goto TAIL_CALL_START;
      }
    }
    public BigInteger Count() {
      BigInteger _20___accumulator = BigInteger.Zero;
      Chain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_20___accumulator);
      } else {
        _20___accumulator = (BigInteger.One) + (_20___accumulator);
        var n1 = (_this).dtor_previous;
        _this = n1;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      Dafny.ISequence<byte> _21___accumulator = Dafny.Sequence<byte>.FromElements();
      Chain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(), _21___accumulator);
      } else {
        _21___accumulator = Dafny.Sequence<byte>.Concat(((_this).dtor_v).Bytes(), _21___accumulator);
        var n2 = (_this).dtor_previous;
        _this = n2;
        goto TAIL_CALL_START;
      }
    }
    public Views_mWriters_Compile.Chain Append(Views_mCore_Compile.View__ v_k) {
      if (((this).is_Chain) && (Views_mCore_Compile.__default.Adjacent((this).dtor_v, v_k))) {
        return Views_mWriters_Compile.Chain.create_Chain((this).dtor_previous, Views_mCore_Compile.__default.Merge((this).dtor_v, v_k));
      } else {
        return Views_mWriters_Compile.Chain.create_Chain(this, v_k);
      }
    }
    public void Blit(byte[] bs, uint end)
    {
      Chain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Chain) {
        uint _22_end;
        _22_end = (end) - (((_this).dtor_v).Length());
        ((_this).dtor_v).Blit(bs, _22_end);
        var n3 = (_this).dtor_previous;
        byte[] n4 = bs;
        uint n5 = _22_end;
        _this = n3;
        bs = n4;
        end = n5;
        goto TAIL_CALL_START;
      }
    }
  }
  public sealed class Chain_Empty : Chain {
    public Chain_Empty() {
    }
    public override Chain DowncastClone() {
      if (this is Chain dt) { return dt; }
      return new Chain_Empty();
    }
    public override bool Equals(object other) {
      var oth = other as Views_mWriters_Compile.Chain_Empty;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Views_mWriters_Compile.Chain.Empty";
      return s;
    }
  }
  public sealed class Chain_Chain : Chain {
    public readonly Views_mWriters_Compile.Chain previous;
    public readonly Views_mCore_Compile.View__ v;
    public Chain_Chain(Views_mWriters_Compile.Chain previous, Views_mCore_Compile.View__ v) {
      this.previous = previous;
      this.v = v;
    }
    public override Chain DowncastClone() {
      if (this is Chain dt) { return dt; }
      return new Chain_Chain(previous, v);
    }
    public override bool Equals(object other) {
      var oth = other as Views_mWriters_Compile.Chain_Chain;
      return oth != null && object.Equals(this.previous, oth.previous) && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.previous));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Views_mWriters_Compile.Chain.Chain";
      s += "(";
      s += Dafny.Helpers.ToString(this.previous);
      s += ", ";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
  }

  public partial class Writer {
    private static readonly Views_mWriters_Compile.Writer__ Witness = Views_mWriters_Compile.Writer__.create(0U, Views_mWriters_Compile.Chain.create_Empty());
    public static Views_mWriters_Compile.Writer__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile.Writer__> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile.Writer__>(Views_mWriters_Compile.Writer.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile.Writer__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public struct Writer__ {
    public readonly uint length;
    public readonly Views_mWriters_Compile.Chain chain;
    public Writer__(uint length, Views_mWriters_Compile.Chain chain) {
      this.length = length;
      this.chain = chain;
    }
    public Writer__ DowncastClone() {
      if (this is Writer__ dt) { return dt; }
      return new Writer__(length, chain);
    }
    public override bool Equals(object other) {
      return other is  Views_mWriters_Compile.Writer__ oth && this.length == oth.length && object.Equals(this.chain, oth.chain);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.length));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.chain));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Views_mWriters_Compile.Writer_.Writer";
      s += "(";
      s += Dafny.Helpers.ToString(this.length);
      s += ", ";
      s += Dafny.Helpers.ToString(this.chain);
      s += ")";
      return s;
    }
    private static readonly Writer__ theDefault = create(0, Views_mWriters_Compile.Chain.Default());
    public static Writer__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile.Writer__> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile.Writer__>(Views_mWriters_Compile.Writer__.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile.Writer__> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Writer__ create(uint length, Views_mWriters_Compile.Chain chain) {
      return new Writer__(length, chain);
    }
    public bool is_Writer { get { return true; } }
    public uint dtor_length {
      get {
        return this.length;
      }
    }
    public Views_mWriters_Compile.Chain dtor_chain {
      get {
        return this.chain;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_chain).Bytes();
    }
    public static uint SaturatedAddU32(uint a, uint b)
    {
      if ((a) <= ((BoundedInts_Compile.__default.UINT32__MAX) - (b))) {
        return (a) + (b);
      } else {
        return BoundedInts_Compile.__default.UINT32__MAX;
      }
    }
    public Views_mWriters_Compile.Writer__ Append(Views_mCore_Compile.View__ v_k) {
      return Views_mWriters_Compile.Writer__.create(Views_mWriters_Compile.Writer__.SaturatedAddU32((this).dtor_length, (v_k).Length()), ((this).dtor_chain).Append(v_k));
    }
    public Views_mWriters_Compile.Writer__ Then(Func<Views_mWriters_Compile.Writer__, Views_mWriters_Compile.Writer__> fn) {
      return Dafny.Helpers.Id<Func<Views_mWriters_Compile.Writer__, Views_mWriters_Compile.Writer__>>(fn)(this);
    }
    public void Blit(byte[] bs)
    {
      ((this).dtor_chain).Blit(bs, (this).dtor_length);
    }
    public byte[] ToArray()
    {
      byte[] bs = new byte[0];
      byte[] _nw0 = new byte[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked((this).dtor_length, "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      bs = _nw0;
      (this).Blit(bs);
      return bs;
    }
    public static Views_mWriters_Compile.Writer__ Empty { get {
      return Views_mWriters_Compile.Writer__.create(0U, Views_mWriters_Compile.Chain.create_Empty());
    } }
    public bool Unsaturated_q { get {
      return ((this).dtor_length) != (BoundedInts_Compile.__default.UINT32__MAX);
    } }
    public bool Empty_q { get {
      return ((this).dtor_chain).is_Empty;
    } }
  }

} // end of namespace Views_mWriters_Compile
namespace Views_Compile {

} // end of namespace Views_Compile
namespace JSON_mGrammar_Compile {

  public partial class jchar {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('b')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jchar.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jperiod {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('.')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jperiod.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class je {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('e')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.je.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcolon {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(':')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jcolon.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jcomma {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(',')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jcomma.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbrace {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('{')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jlbrace.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbrace {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('}')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jrbrace.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jlbracket {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('[')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jlbracket.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jrbracket {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)(']')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jrbracket.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jminus {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jminus.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jsign {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jsign.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jblanks {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jblanks.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public struct Structural<T> {
    public readonly Views_mCore_Compile.View__ before;
    public readonly T t;
    public readonly Views_mCore_Compile.View__ after;
    public Structural(Views_mCore_Compile.View__ before, T t, Views_mCore_Compile.View__ after) {
      this.before = before;
      this.t = t;
      this.after = after;
    }
    public Structural<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is Structural<__T> dt) { return dt; }
      return new Structural<__T>(before, converter0(t), after);
    }
    public override bool Equals(object other) {
      return other is JSON_mGrammar_Compile.Structural<T> oth && object.Equals(this.before, oth.before) && object.Equals(this.t, oth.t) && object.Equals(this.after, oth.after);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.before));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.after));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Structural.Structural";
      s += "(";
      s += Dafny.Helpers.ToString(this.before);
      s += ", ";
      s += Dafny.Helpers.ToString(this.t);
      s += ", ";
      s += Dafny.Helpers.ToString(this.after);
      s += ")";
      return s;
    }
    public static Structural<T> Default(T _default_T) {
      return create(JSON_mGrammar_Compile.jblanks.Default(), _default_T, JSON_mGrammar_Compile.jblanks.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.Structural<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile.Structural<T>>(JSON_mGrammar_Compile.Structural<T>.Default(_td_T.Default()));
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Structural<T> create(Views_mCore_Compile.View__ before, T t, Views_mCore_Compile.View__ after) {
      return new Structural<T>(before, t, after);
    }
    public bool is_Structural { get { return true; } }
    public Views_mCore_Compile.View__ dtor_before {
      get {
        return this.before;
      }
    }
    public T dtor_t {
      get {
        return this.t;
      }
    }
    public Views_mCore_Compile.View__ dtor_after {
      get {
        return this.after;
      }
    }
  }

  public abstract class Maybe<T> {
    public Maybe() { }
    public static Maybe<T> Default() {
      return create_Empty();
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.Maybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile.Maybe<T>>(JSON_mGrammar_Compile.Maybe<T>.Default());
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Maybe<T> create_Empty() {
      return new Maybe_Empty<T>();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Maybe<T> create_NonEmpty(T t) {
      return new Maybe_NonEmpty<T>(t);
    }
    public bool is_Empty { get { return this is Maybe_Empty<T>; } }
    public bool is_NonEmpty { get { return this is Maybe_NonEmpty<T>; } }
    public T dtor_t {
      get {
        var d = this;
        return ((Maybe_NonEmpty<T>)d).t;
      }
    }
    public abstract Maybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public sealed class Maybe_Empty<T> : Maybe<T> {
    public Maybe_Empty() {
    }
    public override Maybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is Maybe<__T> dt) { return dt; }
      return new Maybe_Empty<__T>();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Maybe_Empty<T>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Maybe.Empty";
      return s;
    }
  }
  public sealed class Maybe_NonEmpty<T> : Maybe<T> {
    public readonly T t;
    public Maybe_NonEmpty(T t) {
      this.t = t;
    }
    public override Maybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is Maybe<__T> dt) { return dt; }
      return new Maybe_NonEmpty<__T>(converter0(t));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Maybe_NonEmpty<T>;
      return oth != null && object.Equals(this.t, oth.t);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Maybe.NonEmpty";
      s += "(";
      s += Dafny.Helpers.ToString(this.t);
      s += ")";
      return s;
    }
  }

  public struct Suffixed<T, S> {
    public readonly T t;
    public readonly JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<S>> suffix;
    public Suffixed(T t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<S>> suffix) {
      this.t = t;
      this.suffix = suffix;
    }
    public Suffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1) {
      if (this is Suffixed<__T, __S> dt) { return dt; }
      return new Suffixed<__T, __S>(converter0(t), (suffix).DowncastClone<JSON_mGrammar_Compile.Structural<__S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile.Structural<S>, JSON_mGrammar_Compile.Structural<__S>>));
    }
    public override bool Equals(object other) {
      return other is JSON_mGrammar_Compile.Suffixed<T, S> oth && object.Equals(this.t, oth.t) && object.Equals(this.suffix, oth.suffix);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.suffix));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Suffixed.Suffixed";
      s += "(";
      s += Dafny.Helpers.ToString(this.t);
      s += ", ";
      s += Dafny.Helpers.ToString(this.suffix);
      s += ")";
      return s;
    }
    public static Suffixed<T, S> Default(T _default_T) {
      return create(_default_T, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<S>>.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.Suffixed<T, S>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile.Suffixed<T, S>>(JSON_mGrammar_Compile.Suffixed<T, S>.Default(_td_T.Default()));
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Suffixed<T, S> create(T t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<S>> suffix) {
      return new Suffixed<T, S>(t, suffix);
    }
    public bool is_Suffixed { get { return true; } }
    public T dtor_t {
      get {
        return this.t;
      }
    }
    public JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<S>> dtor_suffix {
      get {
        return this.suffix;
      }
    }
  }

  public partial class SuffixedSequence<D, S> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<D, S>>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<D, S>>>(Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<D, S>>.Empty);
    }
  }

  public struct Bracketed<L, D, S, R> {
    public readonly JSON_mGrammar_Compile.Structural<L> l;
    public readonly Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<D, S>> data;
    public readonly JSON_mGrammar_Compile.Structural<R> r;
    public Bracketed(JSON_mGrammar_Compile.Structural<L> l, Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<D, S>> data, JSON_mGrammar_Compile.Structural<R> r) {
      this.l = l;
      this.data = data;
      this.r = r;
    }
    public Bracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3) {
      if (this is Bracketed<__L, __D, __S, __R> dt) { return dt; }
      return new Bracketed<__L, __D, __S, __R>((l).DowncastClone<__L>(Dafny.Helpers.CastConverter<L, __L>), (data).DowncastClone<JSON_mGrammar_Compile.Suffixed<__D, __S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile.Suffixed<D, S>, JSON_mGrammar_Compile.Suffixed<__D, __S>>), (r).DowncastClone<__R>(Dafny.Helpers.CastConverter<R, __R>));
    }
    public override bool Equals(object other) {
      return other is  JSON_mGrammar_Compile.Bracketed<L, D, S, R> oth && object.Equals(this.l, oth.l) && object.Equals(this.data, oth.data) && object.Equals(this.r, oth.r);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.l));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.data));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.r));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Bracketed.Bracketed";
      s += "(";
      s += Dafny.Helpers.ToString(this.l);
      s += ", ";
      s += Dafny.Helpers.ToString(this.data);
      s += ", ";
      s += Dafny.Helpers.ToString(this.r);
      s += ")";
      return s;
    }
    public static Bracketed<L, D, S, R> Default(L _default_L, R _default_R) {
      return create(JSON_mGrammar_Compile.Structural<L>.Default(_default_L), Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<D, S>>.Empty, JSON_mGrammar_Compile.Structural<R>.Default(_default_R));
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.Bracketed<L, D, S, R>> _TypeDescriptor(Dafny.TypeDescriptor<L> _td_L, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile.Bracketed<L, D, S, R>>(JSON_mGrammar_Compile.Bracketed<L, D, S, R>.Default(_td_L.Default(), _td_R.Default()));
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Bracketed<L, D, S, R> create(JSON_mGrammar_Compile.Structural<L> l, Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<D, S>> data, JSON_mGrammar_Compile.Structural<R> r) {
      return new Bracketed<L, D, S, R>(l, data, r);
    }
    public bool is_Bracketed { get { return true; } }
    public JSON_mGrammar_Compile.Structural<L> dtor_l {
      get {
        return this.l;
      }
    }
    public Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<D, S>> dtor_data {
      get {
        return this.data;
      }
    }
    public JSON_mGrammar_Compile.Structural<R> dtor_r {
      get {
        return this.r;
      }
    }
  }

  public partial class jstring {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jstring.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jnull {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(JSON_mGrammar_Compile.__default.NULL);
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jnull.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jbool {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(JSON_mGrammar_Compile.__default.TRUE);
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jbool.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jdigits {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jdigits.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jnum {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('0')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jnum.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jint {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements((byte)('0')));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mGrammar_Compile.jint.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public struct jkv {
    public readonly Views_mCore_Compile.View__ k;
    public readonly JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__> colon;
    public readonly JSON_mGrammar_Compile.Value v;
    public jkv(Views_mCore_Compile.View__ k, JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__> colon, JSON_mGrammar_Compile.Value v) {
      this.k = k;
      this.colon = colon;
      this.v = v;
    }
    public jkv DowncastClone() {
      if (this is jkv dt) { return dt; }
      return new jkv(k, colon, v);
    }
    public override bool Equals(object other) {
      return other is JSON_mGrammar_Compile.jkv oth && object.Equals(this.k, oth.k) && object.Equals(this.colon, oth.colon) && object.Equals(this.v, oth.v);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.k));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.colon));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.v));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jkv.KV";
      s += "(";
      s += Dafny.Helpers.ToString(this.k);
      s += ", ";
      s += Dafny.Helpers.ToString(this.colon);
      s += ", ";
      s += Dafny.Helpers.ToString(this.v);
      s += ")";
      return s;
    }
    private static readonly jkv theDefault = create(JSON_mGrammar_Compile.jstring.Default(), JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>.Default(JSON_mGrammar_Compile.jcolon.Default()), JSON_mGrammar_Compile.Value.Default());
    public static jkv Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile.jkv> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile.jkv>(JSON_mGrammar_Compile.jkv.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.jkv> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static jkv create(Views_mCore_Compile.View__ k, JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__> colon, JSON_mGrammar_Compile.Value v) {
      return new jkv(k, colon, v);
    }
    public bool is_KV { get { return true; } }
    public Views_mCore_Compile.View__ dtor_k {
      get {
        return this.k;
      }
    }
    public JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__> dtor_colon {
      get {
        return this.colon;
      }
    }
    public JSON_mGrammar_Compile.Value dtor_v {
      get {
        return this.v;
      }
    }
  }

  public struct jfrac {
    public readonly Views_mCore_Compile.View__ period;
    public readonly Views_mCore_Compile.View__ num;
    public jfrac(Views_mCore_Compile.View__ period, Views_mCore_Compile.View__ num) {
      this.period = period;
      this.num = num;
    }
    public jfrac DowncastClone() {
      if (this is jfrac dt) { return dt; }
      return new jfrac(period, num);
    }
    public override bool Equals(object other) {
      return other is  JSON_mGrammar_Compile.jfrac oth && object.Equals(this.period, oth.period) && object.Equals(this.num, oth.num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.period));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jfrac.JFrac";
      s += "(";
      s += Dafny.Helpers.ToString(this.period);
      s += ", ";
      s += Dafny.Helpers.ToString(this.num);
      s += ")";
      return s;
    }
    private static readonly jfrac theDefault = create(JSON_mGrammar_Compile.jperiod.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static jfrac Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile.jfrac> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile.jfrac>(JSON_mGrammar_Compile.jfrac.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.jfrac> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static jfrac create(Views_mCore_Compile.View__ period, Views_mCore_Compile.View__ num) {
      return new jfrac(period, num);
    }
    public bool is_JFrac { get { return true; } }
    public Views_mCore_Compile.View__ dtor_period {
      get {
        return this.period;
      }
    }
    public Views_mCore_Compile.View__ dtor_num {
      get {
        return this.num;
      }
    }
  }

  public struct jexp {
    public readonly Views_mCore_Compile.View__ e;
    public readonly Views_mCore_Compile.View__ sign;
    public readonly Views_mCore_Compile.View__ num;
    public jexp(Views_mCore_Compile.View__ e, Views_mCore_Compile.View__ sign, Views_mCore_Compile.View__ num) {
      this.e = e;
      this.sign = sign;
      this.num = num;
    }
    public jexp DowncastClone() {
      if (this is jexp dt) { return dt; }
      return new jexp(e, sign, num);
    }
    public override bool Equals(object other) {
      return other is  JSON_mGrammar_Compile.jexp oth && object.Equals(this.e, oth.e) && object.Equals(this.sign, oth.sign) && object.Equals(this.num, oth.num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.e));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.sign));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jexp.JExp";
      s += "(";
      s += Dafny.Helpers.ToString(this.e);
      s += ", ";
      s += Dafny.Helpers.ToString(this.sign);
      s += ", ";
      s += Dafny.Helpers.ToString(this.num);
      s += ")";
      return s;
    }
    private static readonly jexp theDefault = create(JSON_mGrammar_Compile.je.Default(), JSON_mGrammar_Compile.jsign.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static jexp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile.jexp> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile.jexp>(JSON_mGrammar_Compile.jexp.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.jexp> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static jexp create(Views_mCore_Compile.View__ e, Views_mCore_Compile.View__ sign, Views_mCore_Compile.View__ num) {
      return new jexp(e, sign, num);
    }
    public bool is_JExp { get { return true; } }
    public Views_mCore_Compile.View__ dtor_e {
      get {
        return this.e;
      }
    }
    public Views_mCore_Compile.View__ dtor_sign {
      get {
        return this.sign;
      }
    }
    public Views_mCore_Compile.View__ dtor_num {
      get {
        return this.num;
      }
    }
  }

  public struct jnumber {
    public readonly Views_mCore_Compile.View__ minus;
    public readonly Views_mCore_Compile.View__ num;
    public readonly JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac> frac;
    public readonly JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp> exp;
    public jnumber(Views_mCore_Compile.View__ minus, Views_mCore_Compile.View__ num, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac> frac, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp> exp) {
      this.minus = minus;
      this.num = num;
      this.frac = frac;
      this.exp = exp;
    }
    public jnumber DowncastClone() {
      if (this is jnumber dt) { return dt; }
      return new jnumber(minus, num, frac, exp);
    }
    public override bool Equals(object other) {
      return other is JSON_mGrammar_Compile.jnumber oth && object.Equals(this.minus, oth.minus) && object.Equals(this.num, oth.num) && object.Equals(this.frac, oth.frac) && object.Equals(this.exp, oth.exp);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.minus));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.frac));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.exp));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.jnumber.JNumber";
      s += "(";
      s += Dafny.Helpers.ToString(this.minus);
      s += ", ";
      s += Dafny.Helpers.ToString(this.num);
      s += ", ";
      s += Dafny.Helpers.ToString(this.frac);
      s += ", ";
      s += Dafny.Helpers.ToString(this.exp);
      s += ")";
      return s;
    }
    private static readonly jnumber theDefault = create(JSON_mGrammar_Compile.jminus.Default(), JSON_mGrammar_Compile.jnum.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>.Default());
    public static jnumber Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile.jnumber> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile.jnumber>(JSON_mGrammar_Compile.jnumber.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.jnumber> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static jnumber create(Views_mCore_Compile.View__ minus, Views_mCore_Compile.View__ num, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac> frac, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp> exp) {
      return new jnumber(minus, num, frac, exp);
    }
    public bool is_JNumber { get { return true; } }
    public Views_mCore_Compile.View__ dtor_minus {
      get {
        return this.minus;
      }
    }
    public Views_mCore_Compile.View__ dtor_num {
      get {
        return this.num;
      }
    }
    public JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac> dtor_frac {
      get {
        return this.frac;
      }
    }
    public JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp> dtor_exp {
      get {
        return this.exp;
      }
    }
  }

  public abstract class Value {
    public Value() { }
    private static readonly Value theDefault = create_Null(JSON_mGrammar_Compile.jnull.Default());
    public static Value Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile.Value> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile.Value>(JSON_mGrammar_Compile.Value.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile.Value> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value create_Null(Views_mCore_Compile.View__ n) {
      return new Value_Null(n);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value create_Bool(Views_mCore_Compile.View__ b) {
      return new Value_Bool(b);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value create_String(Views_mCore_Compile.View__ str) {
      return new Value_String(str);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value create_Number(JSON_mGrammar_Compile.jnumber num) {
      return new Value_Number(num);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value create_Object(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj) {
      return new Value_Object(obj);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Value create_Array(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr) {
      return new Value_Array(arr);
    }
    public bool is_Null { get { return this is Value_Null; } }
    public bool is_Bool { get { return this is Value_Bool; } }
    public bool is_String { get { return this is Value_String; } }
    public bool is_Number { get { return this is Value_Number; } }
    public bool is_Object { get { return this is Value_Object; } }
    public bool is_Array { get { return this is Value_Array; } }
    public Views_mCore_Compile.View__ dtor_n {
      get {
        var d = this;
        return ((Value_Null)d).n;
      }
    }
    public Views_mCore_Compile.View__ dtor_b {
      get {
        var d = this;
        return ((Value_Bool)d).b;
      }
    }
    public Views_mCore_Compile.View__ dtor_str {
      get {
        var d = this;
        return ((Value_String)d).str;
      }
    }
    public JSON_mGrammar_Compile.jnumber dtor_num {
      get {
        var d = this;
        return ((Value_Number)d).num;
      }
    }
    public JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> dtor_obj {
      get {
        var d = this;
        return ((Value_Object)d).obj;
      }
    }
    public JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> dtor_arr {
      get {
        var d = this;
        return ((Value_Array)d).arr;
      }
    }
    public abstract Value DowncastClone();
  }
  public sealed class Value_Null : Value {
    public readonly Views_mCore_Compile.View__ n;
    public Value_Null(Views_mCore_Compile.View__ n) {
      this.n = n;
    }
    public override Value DowncastClone() {
      if (this is Value dt) { return dt; }
      return new Value_Null(n);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Null;
      return oth != null && object.Equals(this.n, oth.n);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.n));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Null";
      s += "(";
      s += Dafny.Helpers.ToString(this.n);
      s += ")";
      return s;
    }
  }
  public sealed class Value_Bool : Value {
    public readonly Views_mCore_Compile.View__ b;
    public Value_Bool(Views_mCore_Compile.View__ b) {
      this.b = b;
    }
    public override Value DowncastClone() {
      if (this is Value dt) { return dt; }
      return new Value_Bool(b);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Bool;
      return oth != null && object.Equals(this.b, oth.b);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Bool";
      s += "(";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public sealed class Value_String : Value {
    public readonly Views_mCore_Compile.View__ str;
    public Value_String(Views_mCore_Compile.View__ str) {
      this.str = str;
    }
    public override Value DowncastClone() {
      if (this is Value dt) { return dt; }
      return new Value_String(str);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_String;
      return oth != null && object.Equals(this.str, oth.str);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.str));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.String";
      s += "(";
      s += Dafny.Helpers.ToString(this.str);
      s += ")";
      return s;
    }
  }
  public sealed class Value_Number : Value {
    public readonly JSON_mGrammar_Compile.jnumber num;
    public Value_Number(JSON_mGrammar_Compile.jnumber num) {
      this.num = num;
    }
    public override Value DowncastClone() {
      if (this is Value dt) { return dt; }
      return new Value_Number(num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Number;
      return oth != null && object.Equals(this.num, oth.num);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.num));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Number";
      s += "(";
      s += Dafny.Helpers.ToString(this.num);
      s += ")";
      return s;
    }
  }
  public sealed class Value_Object : Value {
    public readonly JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj;
    public Value_Object(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj) {
      this.obj = obj;
    }
    public override Value DowncastClone() {
      if (this is Value dt) { return dt; }
      return new Value_Object(obj);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Object;
      return oth != null && object.Equals(this.obj, oth.obj);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 4;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.obj));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Object";
      s += "(";
      s += Dafny.Helpers.ToString(this.obj);
      s += ")";
      return s;
    }
  }
  public sealed class Value_Array : Value {
    public readonly JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr;
    public Value_Array(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr) {
      this.arr = arr;
    }
    public override Value DowncastClone() {
      if (this is Value dt) { return dt; }
      return new Value_Array(arr);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Value_Array;
      return oth != null && object.Equals(this.arr, oth.arr);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 5;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.arr));
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mGrammar_Compile.Value.Array";
      s += "(";
      s += Dafny.Helpers.ToString(this.arr);
      s += ")";
      return s;
    }
  }

  public partial class __default {
    public static bool Blank_q(byte b) {
      return ((((b) == (32)) || ((b) == (9))) || ((b) == (10))) || ((b) == (13));
    }
    public static bool Digit_q(byte b) {
      return (((byte)('0')) <= (b)) && ((b) <= ((byte)('9')));
    }
    public static Dafny.ISequence<byte> NULL { get {
      return Dafny.Sequence<byte>.FromElements((byte)('n'), (byte)('u'), (byte)('l'), (byte)('l'));
    } }
    public static Dafny.ISequence<byte> TRUE { get {
      return Dafny.Sequence<byte>.FromElements((byte)('t'), (byte)('r'), (byte)('u'), (byte)('e'));
    } }
    public static Dafny.ISequence<byte> FALSE { get {
      return Dafny.Sequence<byte>.FromElements((byte)('f'), (byte)('a'), (byte)('l'), (byte)('s'), (byte)('e'));
    } }
  }
} // end of namespace JSON_mGrammar_Compile
namespace JSON_mSpec_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> View(Views_mCore_Compile.View__ v) {
      return (v).Bytes();
    }
    public static Dafny.ISequence<byte> Structural<__T>(JSON_mGrammar_Compile.Structural<__T> self, Func<__T, Dafny.ISequence<byte>> pt)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_before), Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(pt)((self).dtor_t)), JSON_mSpec_Compile.__default.View((self).dtor_after));
    }
    public static Dafny.ISequence<byte> StructuralView(JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__> self) {
      return JSON_mSpec_Compile.__default.Structural<Views_mCore_Compile.View__>(self, JSON_mSpec_Compile.__default.View);
    }
    public static Dafny.ISequence<byte> Maybe<__T>(JSON_mGrammar_Compile.Maybe<__T> self, Func<__T, Dafny.ISequence<byte>> pt)
    {
      if ((self).is_Empty) {
        return Dafny.Sequence<byte>.FromElements();
      } else {
        return Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(pt)((self).dtor_t);
      }
    }
    public static Dafny.ISequence<byte> ConcatBytes<__T>(Dafny.ISequence<__T> ts, Func<__T, Dafny.ISequence<byte>> pt)
    {
      Dafny.ISequence<byte> _23___accumulator = Dafny.Sequence<byte>.FromElements();
    TAIL_CALL_START: ;
      if ((new BigInteger((ts).Count)).Sign == 0) {
        return Dafny.Sequence<byte>.Concat(_23___accumulator, Dafny.Sequence<byte>.FromElements());
      } else {
        _23___accumulator = Dafny.Sequence<byte>.Concat(_23___accumulator, Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(pt)((ts).Select(BigInteger.Zero)));
        Dafny.ISequence<__T> n6 = (ts).Drop(BigInteger.One);
        Func<__T, Dafny.ISequence<byte>> n7 = pt;
        ts = n6;
        pt = n7;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> Bracketed<__D, __S>(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, __D, __S, Views_mCore_Compile.View__> self, Func<JSON_mGrammar_Compile.Suffixed<__D, __S>, Dafny.ISequence<byte>> pdatum)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.StructuralView((self).dtor_l), JSON_mSpec_Compile.__default.ConcatBytes<JSON_mGrammar_Compile.Suffixed<__D, __S>>((self).dtor_data, pdatum)), JSON_mSpec_Compile.__default.StructuralView((self).dtor_r));
    }
    public static Dafny.ISequence<byte> KV(JSON_mGrammar_Compile.jkv self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_k), JSON_mSpec_Compile.__default.StructuralView((self).dtor_colon)), JSON_mSpec_Compile.__default.Value((self).dtor_v));
    }
    public static Dafny.ISequence<byte> Frac(JSON_mGrammar_Compile.jfrac self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_period), JSON_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Exp(JSON_mGrammar_Compile.jexp self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_e), JSON_mSpec_Compile.__default.View((self).dtor_sign)), JSON_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Number(JSON_mGrammar_Compile.jnumber self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_minus), JSON_mSpec_Compile.__default.View((self).dtor_num)), JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile.jfrac>((self).dtor_frac, JSON_mSpec_Compile.__default.Frac)), JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile.jexp>((self).dtor_exp, JSON_mSpec_Compile.__default.Exp));
    }
    public static Dafny.ISequence<byte> String(Views_mCore_Compile.View__ self) {
      return JSON_mSpec_Compile.__default.View(self);
    }
    public static Dafny.ISequence<byte> CommaSuffix(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> c) {
      return JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>(c, JSON_mSpec_Compile.__default.StructuralView);
    }
    public static Dafny.ISequence<byte> Member(JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.KV((self).dtor_t), JSON_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Item(JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.Value((self).dtor_t), JSON_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Object(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj) {
      return JSON_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>(obj, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>, Func<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>>>((_24_obj) => ((System.Func<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>)((_25_d) => {
        return JSON_mSpec_Compile.__default.Member(_25_d);
      })))(obj));
    }
    public static Dafny.ISequence<byte> Array(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr) {
      return JSON_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>(arr, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>, Func<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>>>((_26_arr) => ((System.Func<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>)((_27_d) => {
        return JSON_mSpec_Compile.__default.Item(_27_d);
      })))(arr));
    }
    public static Dafny.ISequence<byte> Value(JSON_mGrammar_Compile.Value self) {
      JSON_mGrammar_Compile.Value _source5 = self;
      if (_source5.is_Null) {
        Views_mCore_Compile.View__ _28___mcc_h0 = _source5.dtor_n;
        Views_mCore_Compile.View__ _29_n = _28___mcc_h0;
        return JSON_mSpec_Compile.__default.View(_29_n);
      } else if (_source5.is_Bool) {
        Views_mCore_Compile.View__ _30___mcc_h1 = _source5.dtor_b;
        Views_mCore_Compile.View__ _31_b = _30___mcc_h1;
        return JSON_mSpec_Compile.__default.View(_31_b);
      } else if (_source5.is_String) {
        Views_mCore_Compile.View__ _32___mcc_h2 = _source5.dtor_str;
        Views_mCore_Compile.View__ _33_str = _32___mcc_h2;
        return JSON_mSpec_Compile.__default.String(_33_str);
      } else if (_source5.is_Number) {
        JSON_mGrammar_Compile.jnumber _34___mcc_h3 = _source5.dtor_num;
        JSON_mGrammar_Compile.jnumber _35_num = _34___mcc_h3;
        return JSON_mSpec_Compile.__default.Number(_35_num);
      } else if (_source5.is_Object) {
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _36___mcc_h4 = _source5.dtor_obj;
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _37_obj = _36___mcc_h4;
        return JSON_mSpec_Compile.__default.Object(_37_obj);
      } else {
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _38___mcc_h5 = _source5.dtor_arr;
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _39_arr = _38___mcc_h5;
        return JSON_mSpec_Compile.__default.Array(_39_arr);
      }
    }
    public static Dafny.ISequence<byte> JSON(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js) {
      return JSON_mSpec_Compile.__default.Structural<JSON_mGrammar_Compile.Value>(js, JSON_mSpec_Compile.__default.Value);
    }
  }
} // end of namespace JSON_mSpec_Compile
namespace JSON_mSpecProperties_Compile {

} // end of namespace JSON_mSpecProperties_Compile
namespace JSON_mZeroCopy_mSerializer_Compile {

  public struct Error {
    public Error() {
    }
    public Error DowncastClone() {
      if (this is Error dt) { return dt; }
      return new Error();
    }
    public override bool Equals(object other) {
      return other is JSON_mZeroCopy_mSerializer_Compile.Error;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mSerializer_Compile.Error.OutOfMemory";
      return s;
    }
    private static readonly Error theDefault = create();
    public static Error Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile.Error> _TYPE = new Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile.Error>(JSON_mZeroCopy_mSerializer_Compile.Error.Default());
    public static Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile.Error> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Error create() {
      return new Error();
    }
    public bool is_OutOfMemory { get { return true; } }
    public static System.Collections.Generic.IEnumerable<Error> AllSingletonConstructors {
      get {
        yield return Error.create();
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error> Serialize(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js)
    {
      Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error> rbs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error>.Default(new byte[0]);
      Views_mWriters_Compile.Writer__ _40_writer;
      _40_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile.Error> _41_valueOrError0 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile.Error>.Default();
      _41_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile.Error>((_40_writer).Unsaturated_q, JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_41_valueOrError0).IsFailure()) {
        rbs = (_41_valueOrError0).PropagateFailure<byte[]>();
        return rbs;
      }
      byte[] _42_bs;
      byte[] _out0;
      _out0 = (_40_writer).ToArray();
      _42_bs = _out0;
      rbs = new Wrappers_Compile.Result_Success<byte[], JSON_mZeroCopy_mSerializer_Compile.Error>(_42_bs);
      return rbs;
      return rbs;
    }
    public static Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> SerializeTo(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js, byte[] bs)
    {
      Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error>.Default(0);
      Views_mWriters_Compile.Writer__ _43_writer;
      _43_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile.Error> _44_valueOrError0 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile.Error>.Default();
      _44_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile.Error>((_43_writer).Unsaturated_q, JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_44_valueOrError0).IsFailure()) {
        len = (_44_valueOrError0).PropagateFailure<uint>();
        return len;
      }
      Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile.Error> _45_valueOrError1 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile.Error>.Default();
      _45_valueOrError1 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile.Error>((new BigInteger((_43_writer).dtor_length)) <= (new BigInteger((bs).Length)), JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_45_valueOrError1).IsFailure()) {
        len = (_45_valueOrError1).PropagateFailure<uint>();
        return len;
      }
      (_43_writer).Blit(bs);
      len = new Wrappers_Compile.Result_Success<uint, JSON_mZeroCopy_mSerializer_Compile.Error>((_43_writer).dtor_length);
      return len;
      return len;
    }
    public static Views_mWriters_Compile.Writer__ Text(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js) {
      return JSON_mZeroCopy_mSerializer_Compile.__default.JSON(js, Views_mWriters_Compile.Writer__.Empty);
    }
    public static Views_mWriters_Compile.Writer__ JSON(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js, Views_mWriters_Compile.Writer__ writer)
    {
      return (((writer).Append((js).dtor_before)).Then(Dafny.Helpers.Id<Func<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Func<Views_mWriters_Compile.Writer__, Views_mWriters_Compile.Writer__>>>((_46_js) => ((System.Func<Views_mWriters_Compile.Writer__, Views_mWriters_Compile.Writer__>)((_47_wr) => {
        return JSON_mZeroCopy_mSerializer_Compile.__default.Value((_46_js).dtor_t, _47_wr);
      })))(js))).Append((js).dtor_after);
    }
    public static Views_mWriters_Compile.Writer__ Value(JSON_mGrammar_Compile.Value v, Views_mWriters_Compile.Writer__ writer)
    {
      JSON_mGrammar_Compile.Value _source6 = v;
      if (_source6.is_Null) {
        Views_mCore_Compile.View__ _48___mcc_h0 = _source6.dtor_n;
        Views_mCore_Compile.View__ _49_n = _48___mcc_h0;
        return (writer).Append(_49_n);
      } else if (_source6.is_Bool) {
        Views_mCore_Compile.View__ _50___mcc_h1 = _source6.dtor_b;
        Views_mCore_Compile.View__ _51_b = _50___mcc_h1;
        return (writer).Append(_51_b);
      } else if (_source6.is_String) {
        Views_mCore_Compile.View__ _52___mcc_h2 = _source6.dtor_str;
        Views_mCore_Compile.View__ _53_str = _52___mcc_h2;
        return JSON_mZeroCopy_mSerializer_Compile.__default.String(_53_str, writer);
      } else if (_source6.is_Number) {
        JSON_mGrammar_Compile.jnumber _54___mcc_h3 = _source6.dtor_num;
        JSON_mGrammar_Compile.jnumber _55_num = _54___mcc_h3;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Number(_55_num, writer);
      } else if (_source6.is_Object) {
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _56___mcc_h4 = _source6.dtor_obj;
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _57_obj = _56___mcc_h4;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Object(_57_obj, writer);
      } else {
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _58___mcc_h5 = _source6.dtor_arr;
        JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _59_arr = _58___mcc_h5;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Array(_59_arr, writer);
      }
    }
    public static Views_mWriters_Compile.Writer__ String(Views_mCore_Compile.View__ str, Views_mWriters_Compile.Writer__ writer)
    {
      return (writer).Append(str);
    }
    public static Views_mWriters_Compile.Writer__ Number(JSON_mGrammar_Compile.jnumber num, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ _60_writer = ((writer).Append((num).dtor_minus)).Append((num).dtor_num);
      Views_mWriters_Compile.Writer__ _61_writer = ((((num).dtor_frac).is_NonEmpty) ? (((_60_writer).Append((((num).dtor_frac).dtor_t).dtor_period)).Append((((num).dtor_frac).dtor_t).dtor_num)) : (_60_writer));
      Views_mWriters_Compile.Writer__ _62_writer = ((((num).dtor_exp).is_NonEmpty) ? ((((_61_writer).Append((((num).dtor_exp).dtor_t).dtor_e)).Append((((num).dtor_exp).dtor_t).dtor_sign)).Append((((num).dtor_exp).dtor_t).dtor_num)) : (_61_writer));
      return _62_writer;
    }
    public static Views_mWriters_Compile.Writer__ StructuralView(JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__> st, Views_mWriters_Compile.Writer__ writer)
    {
      return (((writer).Append((st).dtor_before)).Append((st).dtor_t)).Append((st).dtor_after);
    }
    public static Views_mWriters_Compile.Writer__ Object(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ _63_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_l, writer);
      Views_mWriters_Compile.Writer__ _64_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Members(obj, _63_writer);
      Views_mWriters_Compile.Writer__ _65_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_r, _64_writer);
      return _65_writer;
    }
    public static Views_mWriters_Compile.Writer__ Array(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ _66_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_l, writer);
      Views_mWriters_Compile.Writer__ _67_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Items(arr, _66_writer);
      Views_mWriters_Compile.Writer__ _68_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_r, _67_writer);
      return _68_writer;
    }
    public static Views_mWriters_Compile.Writer__ Members(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ wr = Views_mWriters_Compile.Writer.Default();
      Views_mWriters_Compile.Writer__ _out1;
      _out1 = JSON_mZeroCopy_mSerializer_Compile.__default.MembersImpl(obj, writer);
      wr = _out1;
      return wr;
    }
    public static Views_mWriters_Compile.Writer__ Items(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ wr = Views_mWriters_Compile.Writer.Default();
      Views_mWriters_Compile.Writer__ _out2;
      _out2 = JSON_mZeroCopy_mSerializer_Compile.__default.ItemsImpl(arr, writer);
      wr = _out2;
      return wr;
    }
    public static Views_mWriters_Compile.Writer__ MembersImpl(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ wr = Views_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>> _69_members;
      _69_members = (obj).dtor_data;
      BigInteger _hi1 = new BigInteger((_69_members).Count);
      for (BigInteger _70_i = BigInteger.Zero; _70_i < _hi1; _70_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Member((_69_members).Select(_70_i), wr);
      }
      return wr;
    }
    public static Views_mWriters_Compile.Writer__ ItemsImpl(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ wr = Views_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>> _71_items;
      _71_items = (arr).dtor_data;
      BigInteger _hi2 = new BigInteger((_71_items).Count);
      for (BigInteger _72_i = BigInteger.Zero; _72_i < _hi2; _72_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Item((_71_items).Select(_72_i), wr);
      }
      return wr;
    }
    public static Views_mWriters_Compile.Writer__ Member(JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__> m, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ _73_writer = (writer).Append(((m).dtor_t).dtor_k);
      Views_mWriters_Compile.Writer__ _74_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_t).dtor_colon, _73_writer);
      Views_mWriters_Compile.Writer__ _75_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Value(((m).dtor_t).dtor_v, _74_writer);
      if (((m).dtor_suffix).is_Empty) {
        return _75_writer;
      } else {
        return JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _75_writer);
      }
    }
    public static Views_mWriters_Compile.Writer__ Item(JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__> m, Views_mWriters_Compile.Writer__ writer)
    {
      Views_mWriters_Compile.Writer__ _76_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Value((m).dtor_t, writer);
      if (((m).dtor_suffix).is_Empty) {
        return _76_writer;
      } else {
        return JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _76_writer);
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mSerializer_Compile
namespace Lexers_mCore_Compile {

  public abstract class LexerResult<T, R> {
    public LexerResult() { }
    public static LexerResult<T, R> Default() {
      return create_Accept();
    }
    public static Dafny.TypeDescriptor<Lexers_mCore_Compile.LexerResult<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Lexers_mCore_Compile.LexerResult<T, R>>(Lexers_mCore_Compile.LexerResult<T, R>.Default());
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static LexerResult<T, R> create_Accept() {
      return new LexerResult_Accept<T, R>();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static LexerResult<T, R> create_Reject(R err) {
      return new LexerResult_Reject<T, R>(err);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static LexerResult<T, R> create_Partial(T st) {
      return new LexerResult_Partial<T, R>(st);
    }
    public bool is_Accept { get { return this is LexerResult_Accept<T, R>; } }
    public bool is_Reject { get { return this is LexerResult_Reject<T, R>; } }
    public bool is_Partial { get { return this is LexerResult_Partial<T, R>; } }
    public R dtor_err {
      get {
        var d = this;
        return ((LexerResult_Reject<T, R>)d).err;
      }
    }
    public T dtor_st {
      get {
        var d = this;
        return ((LexerResult_Partial<T, R>)d).st;
      }
    }
    public abstract LexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public sealed class LexerResult_Accept<T, R> : LexerResult<T, R> {
    public LexerResult_Accept() {
    }
    public override LexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is LexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Accept<__T, __R>();
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mCore_Compile.LexerResult_Accept<T, R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mCore_Compile.LexerResult.Accept";
      return s;
    }
  }
  public sealed class LexerResult_Reject<T, R> : LexerResult<T, R> {
    public readonly R err;
    public LexerResult_Reject(R err) {
      this.err = err;
    }
    public override LexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is LexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Reject<__T, __R>(converter1(err));
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mCore_Compile.LexerResult_Reject<T, R>;
      return oth != null && object.Equals(this.err, oth.err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mCore_Compile.LexerResult.Reject";
      s += "(";
      s += Dafny.Helpers.ToString(this.err);
      s += ")";
      return s;
    }
  }
  public sealed class LexerResult_Partial<T, R> : LexerResult<T, R> {
    public readonly T st;
    public LexerResult_Partial(T st) {
      this.st = st;
    }
    public override LexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is LexerResult<__T, __R> dt) { return dt; }
      return new LexerResult_Partial<__T, __R>(converter0(st));
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mCore_Compile.LexerResult_Partial<T, R>;
      return oth != null && object.Equals(this.st, oth.st);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.st));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mCore_Compile.LexerResult.Partial";
      s += "(";
      s += Dafny.Helpers.ToString(this.st);
      s += ")";
      return s;
    }
  }

} // end of namespace Lexers_mCore_Compile
namespace Lexers_mStrings_Compile {

  public abstract class StringLexerState {
    public StringLexerState() { }
    private static readonly StringLexerState theDefault = create_Start();
    public static StringLexerState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Lexers_mStrings_Compile.StringLexerState> _TYPE = new Dafny.TypeDescriptor<Lexers_mStrings_Compile.StringLexerState>(Lexers_mStrings_Compile.StringLexerState.Default());
    public static Dafny.TypeDescriptor<Lexers_mStrings_Compile.StringLexerState> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static StringLexerState create_Start() {
      return new StringLexerState_Start();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static StringLexerState create_Body(bool escaped) {
      return new StringLexerState_Body(escaped);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static StringLexerState create_End() {
      return new StringLexerState_End();
    }
    public bool is_Start { get { return this is StringLexerState_Start; } }
    public bool is_Body { get { return this is StringLexerState_Body; } }
    public bool is_End { get { return this is StringLexerState_End; } }
    public bool dtor_escaped {
      get {
        var d = this;
        return ((StringLexerState_Body)d).escaped;
      }
    }
    public abstract StringLexerState DowncastClone();
  }
  public sealed class StringLexerState_Start : StringLexerState {
    public StringLexerState_Start() {
    }
    public override StringLexerState DowncastClone() {
      if (this is StringLexerState dt) { return dt; }
      return new StringLexerState_Start();
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mStrings_Compile.StringLexerState_Start;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mStrings_Compile.StringLexerState.Start";
      return s;
    }
  }
  public sealed class StringLexerState_Body : StringLexerState {
    public readonly bool escaped;
    public StringLexerState_Body(bool escaped) {
      this.escaped = escaped;
    }
    public override StringLexerState DowncastClone() {
      if (this is StringLexerState dt) { return dt; }
      return new StringLexerState_Body(escaped);
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mStrings_Compile.StringLexerState_Body;
      return oth != null && this.escaped == oth.escaped;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.escaped));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mStrings_Compile.StringLexerState.Body";
      s += "(";
      s += Dafny.Helpers.ToString(this.escaped);
      s += ")";
      return s;
    }
  }
  public sealed class StringLexerState_End : StringLexerState {
    public StringLexerState_End() {
    }
    public override StringLexerState DowncastClone() {
      if (this is StringLexerState dt) { return dt; }
      return new StringLexerState_End();
    }
    public override bool Equals(object other) {
      var oth = other as Lexers_mStrings_Compile.StringLexerState_End;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Lexers_mStrings_Compile.StringLexerState.End";
      return s;
    }
  }

  public partial class __default {
    public static Lexers_mCore_Compile.LexerResult<bool, __R> StringBody<__R>(bool escaped, short @byte)
    {
      if ((@byte) == ((short)('\\'))) {
        return Lexers_mCore_Compile.LexerResult<bool, __R>.create_Partial(!(escaped));
      } else if (((@byte) == ((short)('\"'))) && (!(escaped))) {
        return Lexers_mCore_Compile.LexerResult<bool, __R>.create_Accept();
      } else {
        return Lexers_mCore_Compile.LexerResult<bool, __R>.create_Partial(false);
      }
    }
    public static Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile.StringLexerState, Dafny.ISequence<char>> String(Lexers_mStrings_Compile.StringLexerState st, short @byte)
    {
      Lexers_mStrings_Compile.StringLexerState _source7 = st;
      if (_source7.is_Start) {
        if ((@byte) == ((short)('\"'))) {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile.StringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(false));
        } else {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile.StringLexerState, Dafny.ISequence<char>>.create_Reject(Dafny.Sequence<char>.FromString("String must start with double quote"));
        }
      } else if (_source7.is_Body) {
        bool _77___mcc_h0 = _source7.dtor_escaped;
        bool _78_escaped = _77___mcc_h0;
        if ((@byte) == ((short)('\\'))) {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile.StringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(!(_78_escaped)));
        } else if (((@byte) == ((short)('\"'))) && (!(_78_escaped))) {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile.StringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_End());
        } else {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile.StringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(false));
        }
      } else {
        return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile.StringLexerState, Dafny.ISequence<char>>.create_Accept();
      }
    }
    public static bool StringBodyLexerStart { get {
      return false;
    } }
    public static Lexers_mStrings_Compile.StringLexerState StringLexerStart { get {
      return Lexers_mStrings_Compile.StringLexerState.create_Start();
    } }
  }
} // end of namespace Lexers_mStrings_Compile
namespace Lexers_Compile {

} // end of namespace Lexers_Compile
namespace Cursors_Compile {
  public struct Split<T> {
    public readonly T t;
    public readonly Cursors_Compile.Cursor__ cs;
    public Split(T t, Cursors_Compile.Cursor__ cs) {
      this.t = t;
      this.cs = cs;
    }
    public Split<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is Split<__T> dt) { return dt; }
      return new Split<__T>(converter0(t), cs);
    }
    public override bool Equals(object other) {
      return other is Cursors_Compile.Split<T> oth && object.Equals(this.t, oth.t) && object.Equals(this.cs, oth.cs);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.t));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.cs));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.Split.SP";
      s += "(";
      s += Dafny.Helpers.ToString(this.t);
      s += ", ";
      s += Dafny.Helpers.ToString(this.cs);
      s += ")";
      return s;
    }
    public static Split<T> Default(T _default_T) {
      return create(_default_T, Cursors_Compile.FreshCursor.Default());
    }
    public static Dafny.TypeDescriptor<Cursors_Compile.Split<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Cursors_Compile.Split<T>>(Cursors_Compile.Split<T>.Default(_td_T.Default()));
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Split<T> create(T t, Cursors_Compile.Cursor__ cs) {
      return new Split<T>(t, cs);
    }
    public bool is_SP { get { return true; } }
    public T dtor_t {
      get {
        return this.t;
      }
    }
    public Cursors_Compile.Cursor__ dtor_cs {
      get {
        return this.cs;
      }
    }
  }

  public partial class Cursor {
    private static readonly Cursors_Compile.Cursor__ Witness = Cursors_Compile.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static Cursors_Compile.Cursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Cursors_Compile.Cursor__> _TYPE = new Dafny.TypeDescriptor<Cursors_Compile.Cursor__>(Cursors_Compile.Cursor.Default());
    public static Dafny.TypeDescriptor<Cursors_Compile.Cursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class FreshCursor {
    private static readonly Cursors_Compile.Cursor__ Witness = Cursors_Compile.Cursor__.create(Dafny.Sequence<byte>.FromElements(), 0U, 0U, 0U);
    public static Cursors_Compile.Cursor__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Cursors_Compile.Cursor__> _TYPE = new Dafny.TypeDescriptor<Cursors_Compile.Cursor__>(Cursors_Compile.FreshCursor.Default());
    public static Dafny.TypeDescriptor<Cursors_Compile.Cursor__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public abstract class CursorError<R> {
    public CursorError() { }
    public static CursorError<R> Default() {
      return create_EOF();
    }
    public static Dafny.TypeDescriptor<Cursors_Compile.CursorError<R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Cursors_Compile.CursorError<R>>(Cursors_Compile.CursorError<R>.Default());
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static CursorError<R> create_EOF() {
      return new CursorError_EOF<R>();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static CursorError<R> create_ExpectingByte(byte expected, short b) {
      return new CursorError_ExpectingByte<R>(expected, b);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static CursorError<R> create_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      return new CursorError_ExpectingAnyByte<R>(expected__sq, b);
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static CursorError<R> create_OtherError(R err) {
      return new CursorError_OtherError<R>(err);
    }
    public bool is_EOF { get { return this is CursorError_EOF<R>; } }
    public bool is_ExpectingByte { get { return this is CursorError_ExpectingByte<R>; } }
    public bool is_ExpectingAnyByte { get { return this is CursorError_ExpectingAnyByte<R>; } }
    public bool is_OtherError { get { return this is CursorError_OtherError<R>; } }
    public byte dtor_expected {
      get {
        var d = this;
        return ((CursorError_ExpectingByte<R>)d).expected;
      }
    }
    public short dtor_b {
      get {
        var d = this;
        if (d is CursorError_ExpectingByte<R>) { return ((CursorError_ExpectingByte<R>)d).b; }
        return ((CursorError_ExpectingAnyByte<R>)d).b;
      }
    }
    public Dafny.ISequence<byte> dtor_expected__sq {
      get {
        var d = this;
        return ((CursorError_ExpectingAnyByte<R>)d).expected__sq;
      }
    }
    public R dtor_err {
      get {
        var d = this;
        return ((CursorError_OtherError<R>)d).err;
      }
    }
    public abstract CursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
    public static Dafny.ISequence<char> _ToString(Cursors_Compile.CursorError<R> _this, Func<R, Dafny.ISequence<char>> pr) {
      Cursors_Compile.CursorError<R> _source8 = _this;
      if (_source8.is_EOF) {
        return Dafny.Sequence<char>.FromString("Reached EOF");
      } else if (_source8.is_ExpectingByte) {
        byte _79___mcc_h0 = _source8.dtor_expected;
        short _80___mcc_h1 = _source8.dtor_b;
        short _81_b = _80___mcc_h1;
        byte _82_b0 = _79___mcc_h0;
        Dafny.ISequence<char> _83_c = (((_81_b) > (0)) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_81_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting '"), Dafny.Sequence<char>.FromElements((char)(_82_b0))), Dafny.Sequence<char>.FromString("', read ")), _83_c);
      } else if (_source8.is_ExpectingAnyByte) {
        Dafny.ISequence<byte> _84___mcc_h2 = _source8.dtor_expected__sq;
        short _85___mcc_h3 = _source8.dtor_b;
        short _86_b = _85___mcc_h3;
        Dafny.ISequence<byte> _87_bs0 = _84___mcc_h2;
        Dafny.ISequence<char> _88_c = (((_86_b) > (0)) ? (Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("'"), Dafny.Sequence<char>.FromElements((char)(_86_b))), Dafny.Sequence<char>.FromString("'"))) : (Dafny.Sequence<char>.FromString("EOF")));
        Dafny.ISequence<char> _89_c0s = ((System.Func<Dafny.ISequence<char>>) (() => {
          BigInteger dim0 = new BigInteger((_87_bs0).Count);
          var arr0 = new char[Dafny.Helpers.ToIntChecked(dim0,"C# array size must not be larger than max 32-bit int")];
          for (int i0 = 0; i0 < dim0; i0++) {
            var _90_idx = (BigInteger) i0;
            arr0[(int)(_90_idx)] = (char)((_87_bs0).Select(_90_idx));
          }
          return Dafny.Sequence<char>.FromArray(arr0);
        }))();
        return Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.Concat(Dafny.Sequence<char>.FromString("Expecting one of '"), _89_c0s), Dafny.Sequence<char>.FromString("', read ")), _88_c);
      } else {
        R _91___mcc_h4 = _source8.dtor_err;
        R _92_err = _91___mcc_h4;
        return Dafny.Helpers.Id<Func<R, Dafny.ISequence<char>>>(pr)(_92_err);
      }
    }
  }
  public sealed class CursorError_EOF<R> : CursorError<R> {
    public CursorError_EOF() {
    }
    public override CursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is CursorError<__R> dt) { return dt; }
      return new CursorError_EOF<__R>();
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_EOF<R>;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.EOF";
      return s;
    }
  }
  public sealed class CursorError_ExpectingByte<R> : CursorError<R> {
    public readonly byte expected;
    public readonly short b;
    public CursorError_ExpectingByte(byte expected, short b) {
      this.expected = expected;
      this.b = b;
    }
    public override CursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is CursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingByte<__R>(expected, b);
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_ExpectingByte<R>;
      return oth != null && this.expected == oth.expected && this.b == oth.b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expected));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.ExpectingByte";
      s += "(";
      s += Dafny.Helpers.ToString(this.expected);
      s += ", ";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public sealed class CursorError_ExpectingAnyByte<R> : CursorError<R> {
    public readonly Dafny.ISequence<byte> expected__sq;
    public readonly short b;
    public CursorError_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      this.expected__sq = expected__sq;
      this.b = b;
    }
    public override CursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is CursorError<__R> dt) { return dt; }
      return new CursorError_ExpectingAnyByte<__R>(expected__sq, b);
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_ExpectingAnyByte<R>;
      return oth != null && object.Equals(this.expected__sq, oth.expected__sq) && this.b == oth.b;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.expected__sq));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.b));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.ExpectingAnyByte";
      s += "(";
      s += Dafny.Helpers.ToString(this.expected__sq);
      s += ", ";
      s += Dafny.Helpers.ToString(this.b);
      s += ")";
      return s;
    }
  }
  public sealed class CursorError_OtherError<R> : CursorError<R> {
    public readonly R err;
    public CursorError_OtherError(R err) {
      this.err = err;
    }
    public override CursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is CursorError<__R> dt) { return dt; }
      return new CursorError_OtherError<__R>(converter0(err));
    }
    public override bool Equals(object other) {
      var oth = other as Cursors_Compile.CursorError_OtherError<R>;
      return oth != null && object.Equals(this.err, oth.err);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.err));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Cursors_Compile.CursorError.OtherError";
      s += "(";
      s += Dafny.Helpers.ToString(this.err);
      s += ")";
      return s;
    }
  }

  public struct Cursor__ {
    public readonly Dafny.ISequence<byte> s;
    public readonly uint beg;
    public readonly uint point;
    public readonly uint end;
    public Cursor__(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      this.s = s;
      this.beg = beg;
      this.point = point;
      this.end = end;
    }
    public Cursor__ DowncastClone() {
      if (this is Cursor__ dt) { return dt; }
      return new Cursor__(s, beg, point, end);
    }
    public override bool Equals(object other) {
      return other is Cursors_Compile.Cursor__ oth && object.Equals(this.s, oth.s) && this.beg == oth.beg && this.point == oth.point && this.end == oth.end;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.s));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.beg));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.point));
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.end));
      return (int) hash;
    }
    public override string ToString() {
      string ss = "Cursors_Compile.Cursor_.Cursor";
      ss += "(";
      ss += Dafny.Helpers.ToString(this.s);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.beg);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.point);
      ss += ", ";
      ss += Dafny.Helpers.ToString(this.end);
      ss += ")";
      return ss;
    }
    private static readonly Cursor__ theDefault = create(Dafny.Sequence<byte>.Empty, 0, 0, 0);
    public static Cursor__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Cursors_Compile.Cursor__> _TYPE = new Dafny.TypeDescriptor<Cursors_Compile.Cursor__>(Cursors_Compile.Cursor__.Default());
    public static Dafny.TypeDescriptor<Cursors_Compile.Cursor__> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Cursor__ create(Dafny.ISequence<byte> s, uint beg, uint point, uint end) {
      return new Cursor__(s, beg, point, end);
    }
    public bool is_Cursor { get { return true; } }
    public Dafny.ISequence<byte> dtor_s {
      get {
        return this.s;
      }
    }
    public uint dtor_beg {
      get {
        return this.beg;
      }
    }
    public uint dtor_point {
      get {
        return this.point;
      }
    }
    public uint dtor_end {
      get {
        return this.end;
      }
    }
    public static Cursors_Compile.Cursor__ OfView(Views_mCore_Compile.View__ v) {
      return Cursors_Compile.Cursor__.create((v).dtor_s, (v).dtor_beg, (v).dtor_beg, (v).dtor_end);
    }
    public static Cursors_Compile.Cursor__ OfBytes(Dafny.ISequence<byte> bs) {
      return Cursors_Compile.Cursor__.create(bs, 0U, 0U, (uint)(bs).LongCount);
    }
    public Dafny.ISequence<byte> Bytes() {
      return ((this).dtor_s).Subsequence((this).dtor_beg, (this).dtor_end);
    }
    public Views_mCore_Compile.View__ Prefix() {
      return Views_mCore_Compile.View__.create((this).dtor_s, (this).dtor_beg, (this).dtor_point);
    }
    public Cursors_Compile.Cursor__ Suffix() {
      Cursors_Compile.Cursor__ _93_dt__update__tmp_h0 = this;
      uint _94_dt__update_hbeg_h0 = (this).dtor_point;
      return Cursors_Compile.Cursor__.create((_93_dt__update__tmp_h0).dtor_s, _94_dt__update_hbeg_h0, (_93_dt__update__tmp_h0).dtor_point, (_93_dt__update__tmp_h0).dtor_end);
    }
    public Cursors_Compile.Split<Views_mCore_Compile.View__> Split() {
      return Cursors_Compile.Split<Views_mCore_Compile.View__>.create((this).Prefix(), (this).Suffix());
    }
    public uint PrefixLength() {
      return ((this).dtor_point) - ((this).dtor_beg);
    }
    public uint SuffixLength() {
      return ((this).dtor_end) - ((this).dtor_point);
    }
    public uint Length() {
      return ((this).dtor_end) - ((this).dtor_beg);
    }
    public byte At(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_beg) + (idx));
    }
    public byte SuffixAt(uint idx) {
      return ((this).dtor_s).Select(((this).dtor_point) + (idx));
    }
    public short Peek() {
      if ((this).EOF_q) {
        return -1;
      } else {
        return (short)((this).SuffixAt(0U));
      }
    }
    public bool LookingAt(char c) {
      return ((this).Peek()) == ((short)(c));
    }
    public Cursors_Compile.Cursor__ Skip(uint n) {
      Cursors_Compile.Cursor__ _95_dt__update__tmp_h0 = this;
      uint _96_dt__update_hpoint_h0 = ((this).dtor_point) + (n);
      return Cursors_Compile.Cursor__.create((_95_dt__update__tmp_h0).dtor_s, (_95_dt__update__tmp_h0).dtor_beg, _96_dt__update_hpoint_h0, (_95_dt__update__tmp_h0).dtor_end);
    }
    public Cursors_Compile.Cursor__ Unskip(uint n) {
      Cursors_Compile.Cursor__ _97_dt__update__tmp_h0 = this;
      uint _98_dt__update_hpoint_h0 = ((this).dtor_point) - (n);
      return Cursors_Compile.Cursor__.create((_97_dt__update__tmp_h0).dtor_s, (_97_dt__update__tmp_h0).dtor_beg, _98_dt__update_hpoint_h0, (_97_dt__update__tmp_h0).dtor_end);
    }
    public Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>> Get<__R>(__R err) {
      if ((this).EOF_q) {
        return new Wrappers_Compile.Result_Failure<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>(Cursors_Compile.CursorError<__R>.create_OtherError(err));
      } else {
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>((this).Skip(1U));
      }
    }
    public Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>> AssertByte<__R>(byte b) {
      short _99_nxt = (this).Peek();
      if ((_99_nxt) == ((short)(b))) {
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>((this).Skip(1U));
      } else {
        return new Wrappers_Compile.Result_Failure<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>(Cursors_Compile.CursorError<__R>.create_ExpectingByte(b, _99_nxt));
      }
    }
    public Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset)
    {
      Cursor__ _this = this;
    TAIL_CALL_START: ;
      if ((offset) == ((uint)(bs).LongCount)) {
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>(_this);
      } else {
        Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>> _100_valueOrError0 = (_this).AssertByte<__R>((byte)((bs).Select(offset)));
        if ((_100_valueOrError0).IsFailure()) {
          return (_100_valueOrError0).PropagateFailure<Cursors_Compile.Cursor__>();
        } else {
          Cursors_Compile.Cursor__ _101_ps = (_100_valueOrError0).Extract();
          var n8 = _101_ps;
          Dafny.ISequence<byte> n9 = bs;
          uint n10 = (offset) + (1U);
          _this = n8;
          bs = n9;
          offset = n10;
          goto TAIL_CALL_START;
        }
      }
    }
    public Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>> AssertChar<__R>(char c0) {
      return (this).AssertByte<__R>((byte)(c0));
    }
    public Cursors_Compile.Cursor__ SkipByte() {
      if ((this).EOF_q) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public Cursors_Compile.Cursor__ SkipIf(Func<byte, bool> p) {
      if (((this).EOF_q) || (!(Dafny.Helpers.Id<Func<byte, bool>>(p)((this).SuffixAt(0U))))) {
        return this;
      } else {
        return (this).Skip(1U);
      }
    }
    public Cursors_Compile.Cursor__ SkipWhile(Func<byte, bool> p)
    {
      Cursors_Compile.Cursor__ ps = Cursors_Compile.Cursor.Default();
      uint _102_point_k;
      _102_point_k = (this).dtor_point;
      uint _103_end;
      _103_end = (this).dtor_end;
      while (((_102_point_k) < (_103_end)) && (Dafny.Helpers.Id<Func<byte, bool>>(p)(((this).dtor_s).Select(_102_point_k)))) {
        _102_point_k = (_102_point_k) + (1U);
      }
      ps = Cursors_Compile.Cursor__.create((this).dtor_s, (this).dtor_beg, _102_point_k, (this).dtor_end);
      return ps;
      return ps;
    }
    public Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>> SkipWhileLexer<__A, __R>(Func<__A, short, Lexers_mCore_Compile.LexerResult<__A, __R>> step, __A st)
    {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>> pr = Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>.Default(Cursors_Compile.Cursor.Default());
      uint _104_point_k;
      _104_point_k = (this).dtor_point;
      uint _105_end;
      _105_end = (this).dtor_end;
      __A _106_st_k;
      _106_st_k = st;
      while (true) {
        bool _107_eof;
        _107_eof = (_104_point_k) == (_105_end);
        short _108_minusone;
        _108_minusone = -1;
        short _109_c;
        _109_c = ((_107_eof) ? (_108_minusone) : ((short)(((this).dtor_s).Select(_104_point_k))));
        Lexers_mCore_Compile.LexerResult<__A, __R> _source9 = Dafny.Helpers.Id<Func<__A, short, Lexers_mCore_Compile.LexerResult<__A, __R>>>(step)(_106_st_k, _109_c);
        if (_source9.is_Accept) {
          pr = new Wrappers_Compile.Result_Success<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>(Cursors_Compile.Cursor__.create((this).dtor_s, (this).dtor_beg, _104_point_k, (this).dtor_end));
          return pr;
        } else if (_source9.is_Reject) {
          __R _110___mcc_h0 = _source9.dtor_err;
          __R _111_err = _110___mcc_h0;
          pr = new Wrappers_Compile.Result_Failure<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>(Cursors_Compile.CursorError<__R>.create_OtherError(_111_err));
          return pr;
        } else {
          __A _112___mcc_h1 = _source9.dtor_st;
          __A _113_st_k_k = _112___mcc_h1;
          if (_107_eof) {
            pr = new Wrappers_Compile.Result_Failure<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<__R>>(Cursors_Compile.CursorError<__R>.create_EOF());
            return pr;
          } else {
            _106_st_k = _113_st_k_k;
            _104_point_k = (_104_point_k) + (1U);
          }
        }
      }
      return pr;
    }
    public bool BOF_q { get {
      return ((this).dtor_point) == ((this).dtor_beg);
    } }
    public bool EOF_q { get {
      return ((this).dtor_point) == ((this).dtor_end);
    } }
  }

} // end of namespace Cursors_Compile
namespace Parsers_Compile {

  public partial class Parser<T, R> {
    public static Parsers_Compile.Parser__<T, R> Default() {
      return Parsers_Compile.__default.ParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Parsers_Compile.Parser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile.Parser__<T, R>>(Parsers_Compile.Parser<T, R>.Default());
    }
  }

  public struct Parser__<T, R> {
    public readonly Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> fn;
    public Parser__(Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> fn) {
      this.fn = fn;
    }
    public Parser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is Parser__<__T, __R> dt) { return dt; }
      return new Parser__<__T, __R>((fn).DowncastClone<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>, Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>>(Dafny.Helpers.Id<Cursors_Compile.Cursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>, Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>>));
    }
    public override bool Equals(object other) {
      return other is Parsers_Compile.Parser__<T, R> oth && object.Equals(this.fn, oth.fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Parsers_Compile.Parser_.Parser";
      s += "(";
      s += Dafny.Helpers.ToString(this.fn);
      s += ")";
      return s;
    }
    public static Parser__<T, R> Default(T _default_T) {
      return create(((Cursors_Compile.Cursor__ x0) => Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>.Default(Cursors_Compile.Split<T>.Default(_default_T))));
    }
    public static Dafny.TypeDescriptor<Parsers_Compile.Parser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Parsers_Compile.Parser__<T, R>>(Parsers_Compile.Parser__<T, R>.Default(_td_T.Default()));
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static Parser__<T, R> create(Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> fn) {
      return new Parser__<T, R>(fn);
    }
    public bool is_Parser { get { return true; } }
    public Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> dtor_fn {
      get {
        return this.fn;
      }
    }
  }

  public struct SubParser__<T, R> {
    public readonly Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> fn;
    public SubParser__(Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> fn) {
      this.fn = fn;
    }
    public SubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is SubParser__<__T, __R> dt) { return dt; }
      return new SubParser__<__T, __R>((fn).DowncastClone<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>, Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>>(Dafny.Helpers.Id<Cursors_Compile.Cursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>, Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>>));
    }
    public override bool Equals(object other) {
      return other is Parsers_Compile.SubParser__<T, R> oth && object.Equals(this.fn, oth.fn);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)Dafny.Helpers.GetHashCode(this.fn));
      return (int) hash;
    }
    public override string ToString() {
      string s = "Parsers_Compile.SubParser_.SubParser";
      s += "(";
      s += Dafny.Helpers.ToString(this.fn);
      s += ")";
      return s;
    }
    public static SubParser__<T, R> Default() {
      return create(((Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>>)null));
    }
    public static Dafny.TypeDescriptor<Parsers_Compile.SubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile.SubParser__<T, R>>(Parsers_Compile.SubParser__<T, R>.Default());
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static SubParser__<T, R> create(Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> fn) {
      return new SubParser__<T, R>(fn);
    }
    public bool is_SubParser { get { return true; } }
    public Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile.CursorError<R>>> dtor_fn {
      get {
        return this.fn;
      }
    }
  }

  public partial class SubParser<T, R> {
    public static Parsers_Compile.SubParser__<T, R> Default() {
      return Parsers_Compile.__default.SubParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Parsers_Compile.SubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile.SubParser__<T, R>>(Parsers_Compile.SubParser<T, R>.Default());
    }
  }

  public partial class __default {
    public static Parsers_Compile.Parser__<__T, __R> ParserWitness<__T, __R>() {
      return Parsers_Compile.Parser__<__T, __R>.create(((System.Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>>)((_114___v0) => {
  return new Wrappers_Compile.Result_Failure<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>(Cursors_Compile.CursorError<__R>.create_EOF());
})));
    }
    public static Parsers_Compile.SubParser__<__T, __R> SubParserWitness<__T, __R>() {
      return Parsers_Compile.SubParser__<__T, __R>.create(((System.Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>>)((_115_cs) => {
  return new Wrappers_Compile.Result_Failure<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<__R>>(Cursors_Compile.CursorError<__R>.create_EOF());
})));
    }
  }
} // end of namespace Parsers_Compile
namespace JSON_mZeroCopy_mDeserializer_mCore_Compile {

  public abstract class JSONError {
    public JSONError() { }
    private static readonly JSONError theDefault = create_UnterminatedSequence();
    public static JSONError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> _TYPE = new Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.Default());
    public static Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> _TypeDescriptor() {
      return _TYPE;
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static JSONError create_UnterminatedSequence() {
      return new JSONError_UnterminatedSequence();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static JSONError create_EmptyNumber() {
      return new JSONError_EmptyNumber();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static JSONError create_ExpectingEOF() {
      return new JSONError_ExpectingEOF();
    }
    [MethodImpl(MethodImplOptions.AggressiveInlining)]
    public static JSONError create_IntOverflow() {
      return new JSONError_IntOverflow();
    }
    public bool is_UnterminatedSequence { get { return this is JSONError_UnterminatedSequence; } }
    public bool is_EmptyNumber { get { return this is JSONError_EmptyNumber; } }
    public bool is_ExpectingEOF { get { return this is JSONError_ExpectingEOF; } }
    public bool is_IntOverflow { get { return this is JSONError_IntOverflow; } }
    public static System.Collections.Generic.IEnumerable<JSONError> AllSingletonConstructors {
      get {
        yield return JSONError.create_UnterminatedSequence();
        yield return JSONError.create_EmptyNumber();
        yield return JSONError.create_ExpectingEOF();
        yield return JSONError.create_IntOverflow();
      }
    }
    public abstract JSONError DowncastClone();
    public Dafny.ISequence<char> _ToString() {
      JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError _source10 = this;
      if (_source10.is_UnterminatedSequence) {
        return Dafny.Sequence<char>.FromString("Unterminated sequence");
      } else if (_source10.is_EmptyNumber) {
        return Dafny.Sequence<char>.FromString("Number must contain at least one digit");
      } else if (_source10.is_ExpectingEOF) {
        return Dafny.Sequence<char>.FromString("Expecting EOF");
      } else {
        return Dafny.Sequence<char>.FromString("Input length does not fit in a 32-bit counter");
      }
    }
  }
  public sealed class JSONError_UnterminatedSequence : JSONError {
    public JSONError_UnterminatedSequence() {
    }
    public override JSONError DowncastClone() {
      if (this is JSONError dt) { return dt; }
      return new JSONError_UnterminatedSequence();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_UnterminatedSequence;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.UnterminatedSequence";
      return s;
    }
  }
  public sealed class JSONError_EmptyNumber : JSONError {
    public JSONError_EmptyNumber() {
    }
    public override JSONError DowncastClone() {
      if (this is JSONError dt) { return dt; }
      return new JSONError_EmptyNumber();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_EmptyNumber;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 1;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.EmptyNumber";
      return s;
    }
  }
  public sealed class JSONError_ExpectingEOF : JSONError {
    public JSONError_ExpectingEOF() {
    }
    public override JSONError DowncastClone() {
      if (this is JSONError dt) { return dt; }
      return new JSONError_ExpectingEOF();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_ExpectingEOF;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 2;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.ExpectingEOF";
      return s;
    }
  }
  public sealed class JSONError_IntOverflow : JSONError {
    public JSONError_IntOverflow() {
    }
    public override JSONError DowncastClone() {
      if (this is JSONError dt) { return dt; }
      return new JSONError_IntOverflow();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError_IntOverflow;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 3;
      return (int) hash;
    }
    public override string ToString() {
      string s = "JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.IntOverflow";
      return s;
    }
  }

  public partial class jopt {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements());
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mZeroCopy_mDeserializer_mCore_Compile.jopt.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class ValueParser {
    private static readonly Dafny.TypeDescriptor<Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _TYPE = new Dafny.TypeDescriptor<Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Parsers_Compile.SubParser<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.Default());
    public static Dafny.TypeDescriptor<Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Get(Cursors_Compile.Cursor__ cs, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError err)
    {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _116_valueOrError0 = (cs).Get<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(err);
      if ((_116_valueOrError0).IsFailure()) {
        return (_116_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _117_cs = (_116_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_117_cs).Split());
      }
    }
    public static Cursors_Compile.Split<Views_mCore_Compile.View__> WS(Cursors_Compile.Cursor__ cs)
    {
      Cursors_Compile.Split<Views_mCore_Compile.View__> sp;
        //= Cursors_Compile.Split<Views_mCore_Compile.View__>.Default(JSON_mGrammar_Compile.jblanks.Default());
      uint _118_point_k;
      _118_point_k = (cs).dtor_point;
      uint _119_end;
      _119_end = (cs).dtor_end;
      while (((_118_point_k) < (_119_end)) && (JSON_mGrammar_Compile.__default.Blank_q(((cs).dtor_s).Select(_118_point_k)))) {
        _118_point_k = (_118_point_k) + (1U);
      }
      sp = (Cursors_Compile.Cursor__.create((cs).dtor_s, (cs).dtor_beg, _118_point_k, (cs).dtor_end)).Split();
      return sp;
      return sp;
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<__T>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Structural<__T>(Cursors_Compile.Cursor__ cs, Parsers_Compile.Parser__<__T, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> parser)
    {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      Views_mCore_Compile.View__ _120_before = _let_tmp_rhs0.dtor_t;
      Cursors_Compile.Cursor__ _121_cs = _let_tmp_rhs0.dtor_cs;
      Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _122_valueOrError0 = Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>>>((parser).dtor_fn)(_121_cs);
      if ((_122_valueOrError0).IsFailure()) {
        return (_122_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<__T>>>();
      } else {
        Cursors_Compile.Split<__T> _let_tmp_rhs1 = (_122_valueOrError0).Extract();
        __T _123_val = _let_tmp_rhs1.dtor_t;
        Cursors_Compile.Cursor__ _124_cs = _let_tmp_rhs1.dtor_cs;
        Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs2 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_124_cs);
        Views_mCore_Compile.View__ _125_after = _let_tmp_rhs2.dtor_t;
        Cursors_Compile.Cursor__ _126_cs = _let_tmp_rhs2.dtor_cs;
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<__T>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<__T>>.create(JSON_mGrammar_Compile.Structural<__T>.create(_120_before, _123_val, _125_after), _126_cs));
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> TryStructural(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs3 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      Views_mCore_Compile.View__ _127_before = _let_tmp_rhs3.dtor_t;
      Cursors_Compile.Cursor__ _128_cs = _let_tmp_rhs3.dtor_cs;
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs4 = ((_128_cs).SkipByte()).Split();
      Views_mCore_Compile.View__ _129_val = _let_tmp_rhs4.dtor_t;
      Cursors_Compile.Cursor__ _130_cs = _let_tmp_rhs4.dtor_cs;
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs5 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_130_cs);
      Views_mCore_Compile.View__ _131_after = _let_tmp_rhs5.dtor_t;
      Cursors_Compile.Cursor__ _132_cs = _let_tmp_rhs5.dtor_cs;
      return Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>.create(JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>.create(_127_before, _129_val, _131_after), _132_cs);
    }
    public static Func<Views_mCore_Compile.View__, Dafny.ISequence<byte>> SpecView { get {
      return ((System.Func<Views_mCore_Compile.View__, Dafny.ISequence<byte>>)((_133_v) => {
        return JSON_mSpec_Compile.__default.View(_133_v);
      }));
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mCore_Compile
namespace JSON_mZeroCopy_mDeserializer_mStrings_Compile {

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> StringBody(Cursors_Compile.Cursor__ cs)
    {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> pr;
        //= Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>.Default(Cursors_Compile.Cursor.Default());
      bool _134_escaped;
      _134_escaped = false;
      uint _hi3 = (cs).dtor_end;
      for (uint _135_point_k = (cs).dtor_point; _135_point_k < _hi3; _135_point_k++) {
        byte _136_byte;
        _136_byte = ((cs).dtor_s).Select(_135_point_k);
        if (((_136_byte) == ((byte)('\"'))) && (!(_134_escaped))) {
          pr = new Wrappers_Compile.Result_Success<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Cursor__.create((cs).dtor_s, (cs).dtor_beg, _135_point_k, (cs).dtor_end));
          return pr;
        } else if ((_136_byte) == ((byte)('\\'))) {
          _134_escaped = !(_134_escaped);
        } else {
          _134_escaped = false;
        }
      }
      pr = new Wrappers_Compile.Result_Failure<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create_EOF());
      return pr;
      return pr;
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> String(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _137_valueOrError0 = (cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>('\"');
      if ((_137_valueOrError0).IsFailure()) {
        return (_137_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _138_cs = (_137_valueOrError0).Extract();
        Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _139_valueOrError1 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.StringBody(_138_cs);
        if ((_139_valueOrError1).IsFailure()) {
          return (_139_valueOrError1).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
        } else {
          Cursors_Compile.Cursor__ _140_cs = (_139_valueOrError1).Extract();
          Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _141_valueOrError2 = (_140_cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>('\"');
          if ((_141_valueOrError2).IsFailure()) {
            return (_141_valueOrError2).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
          } else {
            Cursors_Compile.Cursor__ _142_cs = (_141_valueOrError2).Extract();
            return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_142_cs).Split());
          }
        }
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mStrings_Compile
namespace JSON_mZeroCopy_mDeserializer_mNumbers_Compile {

  public partial class __default {
    public static Cursors_Compile.Split<Views_mCore_Compile.View__> Digits(Cursors_Compile.Cursor__ cs) {
      return ((cs).SkipWhile(JSON_mGrammar_Compile.__default.Digit_q)).Split();
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> NonEmptyDigits(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _143_sp = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Digits(cs);
      Wrappers_Compile.Outcome<Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _144_valueOrError0 = Wrappers_Compile.__default.Need<Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(!(((_143_sp).dtor_t).Empty_q), Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_EmptyNumber()));
      if ((_144_valueOrError0).IsFailure()) {
        return (_144_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(_143_sp);
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> NonZeroInt(Cursors_Compile.Cursor__ cs) {
      return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(cs);
    }
    public static Cursors_Compile.Split<Views_mCore_Compile.View__> OptionalMinus(Cursors_Compile.Cursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_145_c) => {
        return (_145_c) == ((byte)('-'));
      })))).Split();
    }
    public static Cursors_Compile.Split<Views_mCore_Compile.View__> OptionalSign(Cursors_Compile.Cursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_146_c) => {
        return ((_146_c) == ((byte)('-'))) || ((_146_c) == ((byte)('+')));
      })))).Split();
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> TrimmedInt(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _147_sp = ((cs).SkipIf(((System.Func<byte, bool>)((_148_c) => {
        return (_148_c) == ((byte)('0'));
      })))).Split();
      if (((_147_sp).dtor_t).Empty_q) {
        return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonZeroInt((_147_sp).dtor_cs);
      } else {
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(_147_sp);
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Exp(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs6 = ((cs).SkipIf(((System.Func<byte, bool>)((_149_c) => {
        return ((_149_c) == ((byte)('e'))) || ((_149_c) == ((byte)('E')));
      })))).Split();
      Views_mCore_Compile.View__ _150_e = _let_tmp_rhs6.dtor_t;
      Cursors_Compile.Cursor__ _151_cs = _let_tmp_rhs6.dtor_cs;
      if ((_150_e).Empty_q) {
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>.create_Empty(), _151_cs));
      } else {
        Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs7 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalSign(_151_cs);
        Views_mCore_Compile.View__ _152_sign = _let_tmp_rhs7.dtor_t;
        Cursors_Compile.Cursor__ _153_cs = _let_tmp_rhs7.dtor_cs;
        Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _154_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_153_cs);
        if ((_154_valueOrError0).IsFailure()) {
          return (_154_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs8 = (_154_valueOrError0).Extract();
          Views_mCore_Compile.View__ _155_num = _let_tmp_rhs8.dtor_t;
          Cursors_Compile.Cursor__ _156_cs = _let_tmp_rhs8.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>.create_NonEmpty(JSON_mGrammar_Compile.jexp.create(_150_e, _152_sign, _155_num)), _156_cs));
        }
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Frac(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs9 = ((cs).SkipIf(((System.Func<byte, bool>)((_157_c) => {
        return (_157_c) == ((byte)('.'));
      })))).Split();
      Views_mCore_Compile.View__ _158_period = _let_tmp_rhs9.dtor_t;
      Cursors_Compile.Cursor__ _159_cs = _let_tmp_rhs9.dtor_cs;
      if ((_158_period).Empty_q) {
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>.create_Empty(), _159_cs));
      } else {
        Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _160_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_159_cs);
        if ((_160_valueOrError0).IsFailure()) {
          return (_160_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs10 = (_160_valueOrError0).Extract();
          Views_mCore_Compile.View__ _161_num = _let_tmp_rhs10.dtor_t;
          Cursors_Compile.Cursor__ _162_cs = _let_tmp_rhs10.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>.create_NonEmpty(JSON_mGrammar_Compile.jfrac.create(_158_period, _161_num)), _162_cs));
        }
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber> NumberFromParts(Cursors_Compile.Split<Views_mCore_Compile.View__> minus, Cursors_Compile.Split<Views_mCore_Compile.View__> num, Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>> frac, Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>> exp)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber> _163_sp = Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber>.create(JSON_mGrammar_Compile.jnumber.create((minus).dtor_t, (num).dtor_t, (frac).dtor_t, (exp).dtor_t), (exp).dtor_cs);
      return _163_sp;
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Number(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _164_minus = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalMinus(cs);
      Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _165_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.TrimmedInt((_164_minus).dtor_cs);
      if ((_165_valueOrError0).IsFailure()) {
        return (_165_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber>>();
      } else {
        Cursors_Compile.Split<Views_mCore_Compile.View__> _166_num = (_165_valueOrError0).Extract();
        Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _167_valueOrError1 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Frac((_166_num).dtor_cs);
        if ((_167_valueOrError1).IsFailure()) {
          return (_167_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jfrac>> _168_frac = (_167_valueOrError1).Extract();
          Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _169_valueOrError2 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Exp((_168_frac).dtor_cs);
          if ((_169_valueOrError2).IsFailure()) {
            return (_169_valueOrError2).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.jexp>> _170_exp = (_169_valueOrError2).Extract();
            return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NumberFromParts(_164_minus, _166_num, _168_frac, _170_exp));
          }
        }
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mNumbers_Compile
namespace JSON_mZeroCopy_mDeserializer_mObjectParams_Compile {

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Colon(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _171_valueOrError0 = (cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(':');
      if ((_171_valueOrError0).IsFailure()) {
        return (_171_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _172_cs = (_171_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_172_cs).Split());
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile.jkv> KVFromParts(Cursors_Compile.Split<Views_mCore_Compile.View__> k, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> colon, Cursors_Compile.Split<JSON_mGrammar_Compile.Value> v)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile.jkv> _173_sp = Cursors_Compile.Split<JSON_mGrammar_Compile.jkv>.create(JSON_mGrammar_Compile.jkv.create((k).dtor_t, (colon).dtor_t, (v).dtor_t), (v).dtor_cs);
      return _173_sp;
    }
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile.jkv t) {
      return JSON_mSpec_Compile.__default.KV(t);
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.jkv>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Element(Cursors_Compile.Cursor__ cs, Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json)
    {
      Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _174_valueOrError0 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
      if ((_174_valueOrError0).IsFailure()) {
        return (_174_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.jkv>>();
      } else {
        Cursors_Compile.Split<Views_mCore_Compile.View__> _175_k = (_174_valueOrError0).Extract();
        Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _176_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>((_175_k).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Colon));
        if ((_176_valueOrError1).IsFailure()) {
          return (_176_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.jkv>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> _177_colon = (_176_valueOrError1).Extract();
          Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _178_valueOrError2 = Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>>>((json).dtor_fn)((_177_colon).dtor_cs);
          if ((_178_valueOrError2).IsFailure()) {
            return (_178_valueOrError2).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.jkv>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile.Value> _179_v = (_178_valueOrError2).Extract();
            return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.jkv>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.KVFromParts(_175_k, _177_colon, _179_v));
          }
        }
      }
    }
    public static byte OPEN { get {
      return (byte)('{');
    } }
    public static byte CLOSE { get {
      return (byte)('}');
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mObjectParams_Compile
namespace JSON_mZeroCopy_mDeserializer_mObjects_Compile {

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Object(Cursors_Compile.Cursor__ cs, Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json)
    {
      Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _180_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Bracketed(cs, json);
      if ((_180_valueOrError0).IsFailure()) {
        return (_180_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _181_sp = (_180_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(_181_sp);
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Open(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _182_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.OPEN);
      if ((_182_valueOrError0).IsFailure()) {
        return (_182_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _183_cs = (_182_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_183_cs).Split());
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Close(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _184_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE);
      if ((_184_valueOrError0).IsFailure()) {
        return (_184_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _185_cs = (_184_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_185_cs).Split());
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> BracketedFromParts(Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> close)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _186_sp = Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>.create(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _186_sp;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> AppendWithSuffix(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile.jkv> elem, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__> _187_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>.create_NonEmpty((sep).dtor_t));
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> _188_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>.FromElements(_187_suffixed)), (sep).dtor_cs);
      return _188_elems_k;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> AppendLast(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile.jkv> elem, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__> _189_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>.create_Empty());
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> _190_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>.FromElements(_189_suffixed)), (elem).dtor_cs);
      return _190_elems_k;
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Elements(Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.jkv>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _191_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_191_valueOrError0).IsFailure()) {
        return (_191_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile.jkv> _192_elem = (_191_valueOrError0).Extract();
        Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> _193_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_192_elem).dtor_cs);
        short _194_s0 = (((_193_sep).dtor_t).dtor_t).Peek();
        if ((_194_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> _195_elems = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendWithSuffix(elems, _192_elem, _193_sep);
          Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> n11 = json;
          Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> n12 = open;
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> n13 = _195_elems;
          json = n11;
          open = n12;
          elems = n13;
          goto TAIL_CALL_START;
        } else if ((_194_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> _196_elems = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendLast(elems, _192_elem, _193_sep);
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(open, _196_elems, _193_sep));
        } else {
          return new Wrappers_Compile.Result_Failure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE, JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR), _194_s0));
        }
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Bracketed(Cursors_Compile.Cursor__ cs, Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json)
    {
      Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _197_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>(cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Open));
      if ((_197_valueOrError0).IsFailure()) {
        return (_197_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> _198_open = (_197_valueOrError0).Extract();
        Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>> _199_elems = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__>>.FromElements(), (_198_open).dtor_cs);
        if ((((_198_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _200_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>((_198_open).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Close));
          if ((_200_valueOrError1).IsFailure()) {
            return (_200_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> _201_close = (_200_valueOrError1).Extract();
            return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(_198_open, _199_elems, _201_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Elements(json, _198_open, _199_elems);
        }
      }
    }
    public static byte SEPARATOR { get {
      return (byte)(',');
    } }
  }

  public partial class jopen {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.OPEN));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.jopen.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mZeroCopy_mDeserializer_mObjects_Compile.jclose.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mObjects_Compile
namespace JSON_mZeroCopy_mDeserializer_mArrayParams_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile.Value t) {
      return JSON_mSpec_Compile.__default.Value(t);
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Element(Cursors_Compile.Cursor__ cs, Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json)
    {
      return Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>>>((json).dtor_fn)(cs);
    }
    public static byte OPEN { get {
      return (byte)('[');
    } }
    public static byte CLOSE { get {
      return (byte)(']');
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mArrayParams_Compile
namespace JSON_mZeroCopy_mDeserializer_mArrays_Compile {

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Array(Cursors_Compile.Cursor__ cs, Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json)
    {
      Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _202_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Bracketed(cs, json);
      if ((_202_valueOrError0).IsFailure()) {
        return (_202_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _203_sp = (_202_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(_203_sp);
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Open(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _204_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.OPEN);
      if ((_204_valueOrError0).IsFailure()) {
        return (_204_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _205_cs = (_204_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_205_cs).Split());
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Close(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _206_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE);
      if ((_206_valueOrError0).IsFailure()) {
        return (_206_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _207_cs = (_206_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_207_cs).Split());
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> BracketedFromParts(Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> close)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _208_sp = Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>.create(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _208_sp;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> AppendWithSuffix(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile.Value> elem, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__> _209_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>.create_NonEmpty((sep).dtor_t));
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> _210_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>.FromElements(_209_suffixed)), (sep).dtor_cs);
      return _210_elems_k;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> AppendLast(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile.Value> elem, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__> _211_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>.create_Empty());
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> _212_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>.FromElements(_211_suffixed)), (elem).dtor_cs);
      return _212_elems_k;
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Elements(Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json, Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _213_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_213_valueOrError0).IsFailure()) {
        return (_213_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile.Value> _214_elem = (_213_valueOrError0).Extract();
        Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> _215_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_214_elem).dtor_cs);
        short _216_s0 = (((_215_sep).dtor_t).dtor_t).Peek();
        if ((_216_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> _217_elems = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendWithSuffix(elems, _214_elem, _215_sep);
          Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> n14 = json;
          Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> n15 = open;
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> n16 = _217_elems;
          json = n14;
          open = n15;
          elems = n16;
          goto TAIL_CALL_START;
        } else if ((_216_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> _218_elems = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendLast(elems, _214_elem, _215_sep);
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(open, _218_elems, _215_sep));
        } else {
          return new Wrappers_Compile.Result_Failure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE, JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR), _216_s0));
        }
      }
    }
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Bracketed(Cursors_Compile.Cursor__ cs, Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> json)
    {
      Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _219_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>(cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Open));
      if ((_219_valueOrError0).IsFailure()) {
        return (_219_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> _220_open = (_219_valueOrError0).Extract();
        Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>> _221_elems = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__>>.FromElements(), (_220_open).dtor_cs);
        if ((((_220_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _222_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>((_220_open).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Close));
          if ((_222_valueOrError1).IsFailure()) {
            return (_222_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>> _223_close = (_222_valueOrError1).Extract();
            return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(_220_open, _221_elems, _223_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Elements(json, _220_open, _221_elems);
        }
      }
    }
    public static byte SEPARATOR { get {
      return (byte)(',');
    } }
  }

  public partial class jopen {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.OPEN));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.jopen.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class jclose {
    private static readonly Views_mCore_Compile.View__ Witness = Views_mCore_Compile.View__.OfBytes(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE));
    public static Views_mCore_Compile.View__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TYPE = new Dafny.TypeDescriptor<Views_mCore_Compile.View__>(JSON_mZeroCopy_mDeserializer_mArrays_Compile.jclose.Default());
    public static Dafny.TypeDescriptor<Views_mCore_Compile.View__> _TypeDescriptor() {
      return _TYPE;
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mArrays_Compile
namespace JSON_mZeroCopy_mDeserializer_mConstants_Compile {

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Constant(Cursors_Compile.Cursor__ cs, Dafny.ISequence<byte> expected)
    {
      Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _224_valueOrError0 = (cs).AssertBytes<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>(expected, 0U);
      if ((_224_valueOrError0).IsFailure()) {
        return (_224_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _225_cs = (_224_valueOrError0).Extract();
        return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_225_cs).Split());
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mConstants_Compile
namespace JSON_mZeroCopy_mDeserializer_mValues_Compile {

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Value(Cursors_Compile.Cursor__ cs) {
      short _226_c = (cs).Peek();
      if ((_226_c) == ((short)('{'))) {
        Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _227_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Object(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_227_valueOrError0).IsFailure()) {
          return (_227_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _let_tmp_rhs11 = (_227_valueOrError0).Extract();
          JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.jkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _228_obj = _let_tmp_rhs11.dtor_t;
          Cursors_Compile.Cursor__ _229_cs = _let_tmp_rhs11.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Value>.create(JSON_mGrammar_Compile.Value.create_Object(_228_obj), _229_cs));
        }
      } else if ((_226_c) == ((short)('['))) {
        Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _230_valueOrError1 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Array(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_230_valueOrError1).IsFailure()) {
          return (_230_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _let_tmp_rhs12 = (_230_valueOrError1).Extract();
          JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile.Value, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _231_arr = _let_tmp_rhs12.dtor_t;
          Cursors_Compile.Cursor__ _232_cs = _let_tmp_rhs12.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Value>.create(JSON_mGrammar_Compile.Value.create_Array(_231_arr), _232_cs));
        }
      } else if ((_226_c) == ((short)('\"'))) {
        Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _233_valueOrError2 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
        if ((_233_valueOrError2).IsFailure()) {
          return (_233_valueOrError2).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs13 = (_233_valueOrError2).Extract();
          Views_mCore_Compile.View__ _234_str = _let_tmp_rhs13.dtor_t;
          Cursors_Compile.Cursor__ _235_cs = _let_tmp_rhs13.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Value>.create(JSON_mGrammar_Compile.Value.create_String(_234_str), _235_cs));
        }
      } else if ((_226_c) == ((short)('t'))) {
        Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _236_valueOrError3 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.TRUE);
        if ((_236_valueOrError3).IsFailure()) {
          return (_236_valueOrError3).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs14 = (_236_valueOrError3).Extract();
          Views_mCore_Compile.View__ _237_cst = _let_tmp_rhs14.dtor_t;
          Cursors_Compile.Cursor__ _238_cs = _let_tmp_rhs14.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Value>.create(JSON_mGrammar_Compile.Value.create_Bool(_237_cst), _238_cs));
        }
      } else if ((_226_c) == ((short)('f'))) {
        Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _239_valueOrError4 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.FALSE);
        if ((_239_valueOrError4).IsFailure()) {
          return (_239_valueOrError4).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs15 = (_239_valueOrError4).Extract();
          Views_mCore_Compile.View__ _240_cst = _let_tmp_rhs15.dtor_t;
          Cursors_Compile.Cursor__ _241_cs = _let_tmp_rhs15.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Value>.create(JSON_mGrammar_Compile.Value.create_Bool(_240_cst), _241_cs));
        }
      } else if ((_226_c) == ((short)('n'))) {
        Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _242_valueOrError5 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.NULL);
        if ((_242_valueOrError5).IsFailure()) {
          return (_242_valueOrError5).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs16 = (_242_valueOrError5).Extract();
          Views_mCore_Compile.View__ _243_cst = _let_tmp_rhs16.dtor_t;
          Cursors_Compile.Cursor__ _244_cs = _let_tmp_rhs16.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Value>.create(JSON_mGrammar_Compile.Value.create_Null(_243_cst), _244_cs));
        }
      } else {
        Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _245_valueOrError6 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Number(cs);
        if ((_245_valueOrError6).IsFailure()) {
          return (_245_valueOrError6).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile.jnumber> _let_tmp_rhs17 = (_245_valueOrError6).Extract();
          JSON_mGrammar_Compile.jnumber _246_num = _let_tmp_rhs17.dtor_t;
          Cursors_Compile.Cursor__ _247_cs = _let_tmp_rhs17.dtor_cs;
          return new Wrappers_Compile.Result_Success<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(Cursors_Compile.Split<JSON_mGrammar_Compile.Value>.create(JSON_mGrammar_Compile.Value.create_Number(_246_num), _247_cs));
        }
      }
    }
    public static Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError> ValueParser(Cursors_Compile.Cursor__ cs) {
      Func<Cursors_Compile.Cursor__, bool> _248_pre = Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Func<Cursors_Compile.Cursor__, bool>>>((_249_cs) => ((System.Func<Cursors_Compile.Cursor__, bool>)((_250_ps_k) => {
        return ((_250_ps_k).Length()) < ((_249_cs).Length());
      })))(cs);
      Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>> _251_fn = Dafny.Helpers.Id<Func<Func<Cursors_Compile.Cursor__, bool>, Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>>>>((_252_pre) => ((System.Func<Cursors_Compile.Cursor__, Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>>)((_253_ps_k) => {
        return JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value(_253_ps_k);
      })))(_248_pre);
      return Parsers_Compile.SubParser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create(_251_fn);
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mValues_Compile
namespace JSON_mZeroCopy_mDeserializer_mAPI_Compile {

  public partial class __default {
    public static Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> JSON(Cursors_Compile.Cursor__ cs) {
      return JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mGrammar_Compile.Value>(cs, Parsers_Compile.Parser__<JSON_mGrammar_Compile.Value, JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create(JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value));
    }
    public static Wrappers_Compile.Result<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Text(Views_mCore_Compile.View__ v) {
      Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _254_valueOrError0 = JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.JSON(Cursors_Compile.Cursor__.OfView(v));
      if ((_254_valueOrError0).IsFailure()) {
        return (_254_valueOrError0).PropagateFailure<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>> _let_tmp_rhs18 = (_254_valueOrError0).Extract();
        JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> _255_text = _let_tmp_rhs18.dtor_t;
        Cursors_Compile.Cursor__ _256_cs = _let_tmp_rhs18.dtor_cs;
        Wrappers_Compile.Outcome<Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _257_valueOrError1 = Wrappers_Compile.__default.Need<Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((_256_cs).EOF_q, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_ExpectingEOF()));
        if ((_257_valueOrError1).IsFailure()) {
          return (_257_valueOrError1).PropagateFailure<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>>();
        } else {
          return new Wrappers_Compile.Result_Success<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>(_255_text);
        }
      }
    }
    public static Wrappers_Compile.Result<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> OfBytes(Dafny.ISequence<byte> bs) {
      Wrappers_Compile.Outcome<Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _258_valueOrError0 = Wrappers_Compile.__default.Need<Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>>((new BigInteger((bs).Count)) < (BoundedInts_Compile.__default.TWO__TO__THE__32), Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_IntOverflow()));
      if ((_258_valueOrError0).IsFailure()) {
        return (_258_valueOrError0).PropagateFailure<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>>();
      } else {
        return JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.Text(Views_mCore_Compile.View__.OfBytes(bs));
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mAPI_Compile
namespace JSON_mZeroCopy_mDeserializer_Compile {

} // end of namespace JSON_mZeroCopy_mDeserializer_Compile
namespace JSON_mZeroCopy_mAPI_Compile {

  public partial class __default {
    public static Dafny.ISequence<byte> Serialize(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js) {
      return (JSON_mZeroCopy_mSerializer_Compile.__default.Text(js)).Bytes();
    }
    public static Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error> SerializeAlloc(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js)
    {
      Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error> bs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error>.Default(new byte[0]);
      Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error> _out3;
      _out3 = JSON_mZeroCopy_mSerializer_Compile.__default.Serialize(js);
      bs = _out3;
      return bs;
    }
    public static Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> SerializeBlit(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js, byte[] bs)
    {
      Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error>.Default(0);
      Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> _out4;
      _out4 = JSON_mZeroCopy_mSerializer_Compile.__default.SerializeTo(js, bs);
      len = _out4;
      return len;
    }
    public static Wrappers_Compile.Result<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> Deserialize(Dafny.ISequence<byte> bs) {
      return JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.OfBytes(bs);
    }
  }
} // end of namespace JSON_mZeroCopy_mAPI_Compile
namespace JSON_mZeroCopy_Compile {

} // end of namespace JSON_mZeroCopy_Compile
namespace JSON_Compile {

} // end of namespace JSON_Compile
namespace Benchmarks {

  public partial class __default {
    public static void Deserialize(Dafny.ISequence<byte> bytes)
    {
      uint _hi4 = Benchmarks.__default.WARMUP;
      for (uint _259_i = 0U; _259_i < _hi4; _259_i++) {
        Wrappers_Compile.Result<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _260___v0;
        _260___v0 = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(bytes);
      }
      Benchmarks.Interop.StartTimer();
      uint _hi5 = Benchmarks.__default.REPEATS;
      for (uint _261_i = 0U; _261_i < _hi5; _261_i++) {
        Wrappers_Compile.Result<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _262___v1;
        _262___v1 = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(bytes);
      }
      Benchmarks.Interop.ReportTimer(Dafny.Sequence<char>.FromString("Deserialize"), new BigInteger((bytes).Count), Benchmarks.__default.REPEATS);
    }
    public static void Serialize(JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> js, byte[] target)
    {
      uint _hi6 = Benchmarks.__default.WARMUP;
      for (uint _263_i = 0U; _263_i < _hi6; _263_i++) {
        Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> _264___v2;
        Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> _out5;
        _out5 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeBlit(js, target);
        _264___v2 = _out5;
      }
      Benchmarks.Interop.StartTimer();
      uint _hi7 = Benchmarks.__default.REPEATS;
      for (uint _265_i = 0U; _265_i < _hi7; _265_i++) {
        Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> _266___v3;
        Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile.Error> _out6;
        _out6 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeBlit(js, target);
        _266___v3 = _out6;
      }
      Benchmarks.Interop.ReportTimer(Dafny.Sequence<char>.FromString("Serialize"), new BigInteger((target).Length), Benchmarks.__default.REPEATS);
    }
    public static void _Main()
    {
      byte[] _267_input__array;
      byte[] _out7;
      _out7 = Benchmarks.Interop.ReadInput();
      _267_input__array = _out7;
      Dafny.ISequence<byte> _268_bytes;
      _268_bytes = Dafny.Helpers.SeqFromArray(_267_input__array);
      byte[] _269_output__array;
      byte[] _nw1 = new byte[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((_267_input__array).Length), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      _269_output__array = _nw1;
      Wrappers_Compile.Result<JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value>, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError>> _270_jsr;
      _270_jsr = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(_268_bytes);
      if (!((_270_jsr).is_Success)) {
        throw new Dafny.HaltException("c:\\Users\\cpitcla\\git\\dafny\\libraries\\src\\JSON\\Benchmarks\\Benchmark.dfy(50,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Benchmarks.__default.Deserialize(_268_bytes);
      JSON_mGrammar_Compile.Structural<JSON_mGrammar_Compile.Value> _271_js;
      _271_js = (_270_jsr).dtor_value;
      Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error> _272_output;
      Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile.Error> _out8;
      _out8 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeAlloc(_271_js);
      _272_output = _out8;
      if (!((_272_output).is_Success)) {
        throw new Dafny.HaltException("c:\\Users\\cpitcla\\git\\dafny\\libraries\\src\\JSON\\Benchmarks\\Benchmark.dfy(55,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Benchmarks.__default.Serialize(_271_js, _269_output__array);
    }
    public static uint WARMUP { get {
      return 20U;
    } }
    public static uint REPEATS { get {
      return 80U;
    } }
  }
} // end of namespace Benchmarks
namespace _module {

} // end of namespace _module
class __CallToMain {
  public static void Main(string[] args) {
    Dafny.Helpers.WithHaltHandling(Benchmarks.__default._Main);
  }
}
