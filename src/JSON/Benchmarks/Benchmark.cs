// Dafny program Benchmark.dfy compiled into C#
// To recompile, you will need the libraries
//     System.Runtime.Numerics.dll System.Collections.Immutable.dll
// but the 'dotnet' tool in net6.0 should pick those up automatically.
// Optionally, you may want to include compiler switches like
//     /debug /nowarn:162,164,168,183,219,436,1717,1718

using System;
using System.Numerics;
using Lexers_mCore_Compile;

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

  public interface _ITuple3GOO<out T1, out T2> {
    T1 dtor__0 { get; }
    T2 dtor__1 { get; }
    _ITuple3GOO<__T1, __T2> DowncastClone<__T1, __T2>(Func<T1, __T1> converter0, Func<T2, __T2> converter1);
  }
  public class Tuple3GOO<T1, T2> : _ITuple3GOO<T1, T2> {
    public readonly T1 _0;
    public readonly T2 _1;
    public Tuple3GOO(T1 _0, T2 _1) {
      this._0 = _0;
      this._1 = _1;
    }
    public _ITuple3GOO<__T1, __T2> DowncastClone<__T1, __T2>(Func<T1, __T1> converter0, Func<T2, __T2> converter1) {
      if (this is _ITuple3GOO<__T1, __T2> dt) { return dt; }
      return new Tuple3GOO<__T1, __T2>(converter0(_0), converter1(_1));
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple3GOO<T1, T2>;
      return oth != null && object.Equals(this._0, oth._0) && object.Equals(this._1, oth._1);
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
    public static _ITuple3GOO<T1, T2> Default(T1 _default_T1, T2 _default_T2) {
      return create(_default_T1, _default_T2);
    }
    public static Dafny.TypeDescriptor<_System._ITuple3GOO<T1, T2>> _TypeDescriptor(Dafny.TypeDescriptor<T1> _td_T1, Dafny.TypeDescriptor<T2> _td_T2) {
      return new Dafny.TypeDescriptor<_System._ITuple3GOO<T1, T2>>(_System.Tuple3GOO<T1, T2>.Default(_td_T1.Default(), _td_T2.Default()));
    }
    public static _ITuple3GOO<T1, T2> create(T1 _0, T2 _1) {
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

  public interface _ITuple0 {
    _ITuple0 DowncastClone();
  }
  public class Tuple0 : _ITuple0 {
    public Tuple0() {
    }
    public _ITuple0 DowncastClone() {
      if (this is _ITuple0 dt) { return dt; }
      return new Tuple0();
    }
    public override bool Equals(object other) {
      var oth = other as _System.Tuple0;
      return oth != null;
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      return (int) hash;
    }
    public override string ToString() {
      return "()";
    }
    private static readonly _ITuple0 theDefault = create();
    public static _ITuple0 Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<_System._ITuple0> _TYPE = new Dafny.TypeDescriptor<_System._ITuple0>(_System.Tuple0.Default());
    public static Dafny.TypeDescriptor<_System._ITuple0> _TypeDescriptor() {
      return _TYPE;
    }
    public static _ITuple0 create() {
      return new Tuple0();
    }
    public static System.Collections.Generic.IEnumerable<_ITuple0> AllSingletonConstructors {
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
      return this;
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
    public bool ValidIndex_q(uint idx) {
      return ((new BigInteger((this).dtor_beg)) + (new BigInteger(idx))) < (new BigInteger((this).dtor_end));
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
        var _index0 = (start) + (_0_idx);
        (bs)[(int)(_index0)] = ((this).dtor_s).Select(((this).dtor_beg) + (_0_idx));
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

  public interface _IOption<out T> {
    bool is_None { get; }
    bool is_Some { get; }
    T dtor_value { get; }
    _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult();
    bool IsFailure();
    Wrappers_Compile._IOption<__U> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Option<T> : _IOption<T> {
    public Option() { }
    public static _IOption<T> Default() {
      return create_None();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOption<T>>(Wrappers_Compile.Option<T>.Default());
    }
    public static _IOption<T> create_None() {
      return new Option_None<T>();
    }
    public static _IOption<T> create_Some(T @value) {
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
    public abstract _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0);
    public Wrappers_Compile._IResult<T, Dafny.ISequence<char>> ToResult() {
      Wrappers_Compile._IOption<T> _source0 = this;
      if (_source0.is_None) {
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Failure(Dafny.Sequence<char>.FromString("Option is None"));
      } else {
        T _3___mcc_h0 = _source0.dtor_value;
        T _4_v = _3___mcc_h0;
        return Wrappers_Compile.Result<T, Dafny.ISequence<char>>.create_Success(_4_v);
      }
    }
    public static T UnwrapOr(Wrappers_Compile._IOption<T> _this, T @default) {
      Wrappers_Compile._IOption<T> _source1 = _this;
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
    public Wrappers_Compile._IOption<__U> PropagateFailure<__U>() {
      return Wrappers_Compile.Option<__U>.create_None();
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Option_None<T> : Option<T> {
    public Option_None() {
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
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
  public class Option_Some<T> : Option<T> {
    public readonly T @value;
    public Option_Some(T @value) {
      this.@value = @value;
    }
    public override _IOption<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IOption<__T> dt) { return dt; }
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

  public interface _IResult<out T, out R> {
    bool is_Success { get; }
    bool is_Failure { get; }
    T dtor_value { get; }
    R dtor_error { get; }
    _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    Wrappers_Compile._IOption<T> ToOption();
    bool IsFailure();
    Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>();
    T Extract();
  }
  public abstract class Result<T, R> : _IResult<T, R> {
    public Result() { }
    public static _IResult<T, R> Default(T _default_T) {
      return create_Success(_default_T);
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IResult<T, R>>(Wrappers_Compile.Result<T, R>.Default(_td_T.Default()));
    }
    public static _IResult<T, R> create_Success(T @value) {
      return new Result_Success<T, R>(@value);
    }
    public static _IResult<T, R> create_Failure(R error) {
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
    public abstract _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
    public Wrappers_Compile._IOption<T> ToOption() {
      Wrappers_Compile._IResult<T, R> _source2 = this;
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
    public static T UnwrapOr(Wrappers_Compile._IResult<T, R> _this, T @default) {
      Wrappers_Compile._IResult<T, R> _source3 = _this;
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
    public Wrappers_Compile._IResult<__U, R> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, R>.create_Failure((this).dtor_error);
    }
    public static Wrappers_Compile._IResult<T, __NewR> MapFailure<__NewR>(Wrappers_Compile._IResult<T, R> _this, Func<R, __NewR> reWrap) {
      Wrappers_Compile._IResult<T, R> _source4 = _this;
      if (_source4.is_Success) {
        T _15___mcc_h0 = _source4.dtor_value;
        T _16_s = _15___mcc_h0;
        return Wrappers_Compile.Result<T, __NewR>.create_Success(_16_s);
      } else {
        R _17___mcc_h1 = _source4.dtor_error;
        R _18_e = _17___mcc_h1;
        return Wrappers_Compile.Result<T, __NewR>.create_Failure(Dafny.Helpers.Id<Func<R, __NewR>>(reWrap)(_18_e));
      }
    }
    public T Extract() {
      return (this).dtor_value;
    }
  }
  public class Result_Success<T, R> : Result<T, R> {
    public readonly T @value;
    public Result_Success(T @value) {
      this.@value = @value;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Success<__T, __R>(converter0(@value));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Success<T, R>;
      return oth != null && object.Equals(this.@value, oth.@value);
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
  public class Result_Failure<T, R> : Result<T, R> {
    public readonly R error;
    public Result_Failure(R error) {
      this.error = error;
    }
    public override _IResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IResult<__T, __R> dt) { return dt; }
      return new Result_Failure<__T, __R>(converter1(error));
    }
    public override bool Equals(object other) {
      var oth = other as Wrappers_Compile.Result_Failure<T, R>;
      return oth != null && object.Equals(this.error, oth.error);
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

  public interface _IOutcome<E> {
    bool is_Pass { get; }
    bool is_Fail { get; }
    E dtor_error { get; }
    _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    bool IsFailure();
    Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>();
  }
  public abstract class Outcome<E> : _IOutcome<E> {
    public Outcome() { }
    public static _IOutcome<E> Default() {
      return create_Pass();
    }
    public static Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Wrappers_Compile._IOutcome<E>>(Wrappers_Compile.Outcome<E>.Default());
    }
    public static _IOutcome<E> create_Pass() {
      return new Outcome_Pass<E>();
    }
    public static _IOutcome<E> create_Fail(E error) {
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
    public abstract _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0);
    public bool IsFailure() {
      return (this).is_Fail;
    }
    public Wrappers_Compile._IResult<__U, E> PropagateFailure<__U>() {
      return Wrappers_Compile.Result<__U, E>.create_Failure((this).dtor_error);
    }
  }
  public class Outcome_Pass<E> : Outcome<E> {
    public Outcome_Pass() {
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
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
  public class Outcome_Fail<E> : Outcome<E> {
    public readonly E error;
    public Outcome_Fail(E error) {
      this.error = error;
    }
    public override _IOutcome<__E> DowncastClone<__E>(Func<E, __E> converter0) {
      if (this is _IOutcome<__E> dt) { return dt; }
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
    public static Wrappers_Compile._IOutcome<__E> Need<__E>(bool condition, __E error)
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

  public interface _IChain {
    bool is_Empty { get; }
    bool is_Chain { get; }
    Views_mWriters_Compile._IChain dtor_previous { get; }
    Views_mCore_Compile.View__ dtor_v { get; }
    _IChain DowncastClone();
    BigInteger Length();
    BigInteger Count();
    Dafny.ISequence<byte> Bytes();
    Views_mWriters_Compile._IChain Append(Views_mCore_Compile.View__ v_k);
    void Blit(byte[] bs, uint end);
  }
  public abstract class Chain : _IChain {
    public Chain() { }
    private static readonly _IChain theDefault = create_Empty();
    public static _IChain Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile._IChain> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile._IChain>(Views_mWriters_Compile.Chain.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile._IChain> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IChain create_Empty() {
      return new Chain_Empty();
    }
    public static _IChain create_Chain(Views_mWriters_Compile._IChain previous, Views_mCore_Compile.View__ v) {
      return new Chain_Chain(previous, v);
    }
    public bool is_Empty { get { return this is Chain_Empty; } }
    public bool is_Chain { get { return this is Chain_Chain; } }
    public Views_mWriters_Compile._IChain dtor_previous {
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
    public abstract _IChain DowncastClone();
    public BigInteger Length() {
      BigInteger _19___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_19___accumulator);
      } else {
        _19___accumulator = (new BigInteger(((_this).dtor_v).Length())) + (_19___accumulator);
        var _in0 = (_this).dtor_previous;
        _this = _in0;
        goto TAIL_CALL_START;
      }
    }
    public BigInteger Count() {
      BigInteger _20___accumulator = BigInteger.Zero;
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return (BigInteger.Zero) + (_20___accumulator);
      } else {
        _20___accumulator = (BigInteger.One) + (_20___accumulator);
        var _in1 = (_this).dtor_previous;
        _this = _in1;
        goto TAIL_CALL_START;
      }
    }
    public Dafny.ISequence<byte> Bytes() {
      Dafny.ISequence<byte> _21___accumulator = Dafny.Sequence<byte>.FromElements();
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Empty) {
        return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.FromElements(), _21___accumulator);
      } else {
        _21___accumulator = Dafny.Sequence<byte>.Concat(((_this).dtor_v).Bytes(), _21___accumulator);
        var _in2 = (_this).dtor_previous;
        _this = _in2;
        goto TAIL_CALL_START;
      }
    }
    public Views_mWriters_Compile._IChain Append(Views_mCore_Compile.View__ v_k) {
      if (((this).is_Chain) && (Views_mCore_Compile.__default.Adjacent((this).dtor_v, v_k))) {
        return Views_mWriters_Compile.Chain.create_Chain((this).dtor_previous, Views_mCore_Compile.__default.Merge((this).dtor_v, v_k));
      } else {
        return Views_mWriters_Compile.Chain.create_Chain(this, v_k);
      }
    }
    public void Blit(byte[] bs, uint end)
    {
      _IChain _this = this;
    TAIL_CALL_START: ;
      if ((_this).is_Chain) {
        uint _22_end;
        _22_end = (end) - (((_this).dtor_v).Length());
        ((_this).dtor_v).Blit(bs, _22_end);
        var _in3 = (_this).dtor_previous;
        byte[] _in4 = bs;
        uint _in5 = _22_end;
        _this = _in3;
        bs = _in4;
        end = _in5;
        goto TAIL_CALL_START;
      }
    }
  }
  public class Chain_Empty : Chain {
    public Chain_Empty() {
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
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
  public class Chain_Chain : Chain {
    public readonly Views_mWriters_Compile._IChain previous;
    public readonly Views_mCore_Compile.View__ v;
    public Chain_Chain(Views_mWriters_Compile._IChain previous, Views_mCore_Compile.View__ v) {
      this.previous = previous;
      this.v = v;
    }
    public override _IChain DowncastClone() {
      if (this is _IChain dt) { return dt; }
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
    private static readonly Views_mWriters_Compile._IWriter__ Witness = Views_mWriters_Compile.Writer__.create(0U, Views_mWriters_Compile.Chain.create_Empty());
    public static Views_mWriters_Compile._IWriter__ Default() {
      return Witness;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__>(Views_mWriters_Compile.Writer.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public interface _IWriter__ {
    bool is_Writer { get; }
    uint dtor_length { get; }
    Views_mWriters_Compile._IChain dtor_chain { get; }
    _IWriter__ DowncastClone();
    bool Empty_q { get; }
    bool Unsaturated_q { get; }
    Dafny.ISequence<byte> Bytes();
    Views_mWriters_Compile._IWriter__ Append(Views_mCore_Compile.View__ v_k);
    Views_mWriters_Compile._IWriter__ Then(Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__> fn);
    void Blit(byte[] bs);
    byte[] ToArray();
  }
  public class Writer__ : _IWriter__ {
    public readonly uint length;
    public readonly Views_mWriters_Compile._IChain chain;
    public Writer__(uint length, Views_mWriters_Compile._IChain chain) {
      this.length = length;
      this.chain = chain;
    }
    public _IWriter__ DowncastClone() {
      if (this is _IWriter__ dt) { return dt; }
      return new Writer__(length, chain);
    }
    public override bool Equals(object other) {
      var oth = other as Views_mWriters_Compile.Writer__;
      return oth != null && this.length == oth.length && object.Equals(this.chain, oth.chain);
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
    private static readonly _IWriter__ theDefault = create(0, Views_mWriters_Compile.Chain.Default());
    public static _IWriter__ Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TYPE = new Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__>(Views_mWriters_Compile.Writer__.Default());
    public static Dafny.TypeDescriptor<Views_mWriters_Compile._IWriter__> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IWriter__ create(uint length, Views_mWriters_Compile._IChain chain) {
      return new Writer__(length, chain);
    }
    public bool is_Writer { get { return true; } }
    public uint dtor_length {
      get {
        return this.length;
      }
    }
    public Views_mWriters_Compile._IChain dtor_chain {
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
    public Views_mWriters_Compile._IWriter__ Append(Views_mCore_Compile.View__ v_k) {
      return Views_mWriters_Compile.Writer__.create(Views_mWriters_Compile.Writer__.SaturatedAddU32((this).dtor_length, (v_k).Length()), ((this).dtor_chain).Append(v_k));
    }
    public Views_mWriters_Compile._IWriter__ Then(Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__> fn) {
      return Dafny.Helpers.Id<Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__>>(fn)(this);
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
    public static Views_mWriters_Compile._IWriter__ Empty { get {
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

  public interface _IStructural<out T> {
    bool is_Structural { get; }
    Views_mCore_Compile.View__ dtor_before { get; }
    T dtor_t { get; }
    Views_mCore_Compile.View__ dtor_after { get; }
    _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Structural<T> : _IStructural<T> {
    public readonly Views_mCore_Compile.View__ before;
    public readonly T t;
    public readonly Views_mCore_Compile.View__ after;
    public Structural(Views_mCore_Compile.View__ before, T t, Views_mCore_Compile.View__ after) {
      this.before = before;
      this.t = t;
      this.after = after;
    }
    public _IStructural<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IStructural<__T> dt) { return dt; }
      return new Structural<__T>(before, converter0(t), after);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Structural<T>;
      return oth != null && object.Equals(this.before, oth.before) && object.Equals(this.t, oth.t) && object.Equals(this.after, oth.after);
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
    public static _IStructural<T> Default(T _default_T) {
      return create(JSON_mGrammar_Compile.jblanks.Default(), _default_T, JSON_mGrammar_Compile.jblanks.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IStructural<T>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IStructural<T>>(JSON_mGrammar_Compile.Structural<T>.Default(_td_T.Default()));
    }
    public static _IStructural<T> create(Views_mCore_Compile.View__ before, T t, Views_mCore_Compile.View__ after) {
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

  public interface _IMaybe<out T> {
    bool is_Empty { get; }
    bool is_NonEmpty { get; }
    T dtor_t { get; }
    _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public abstract class Maybe<T> : _IMaybe<T> {
    public Maybe() { }
    public static _IMaybe<T> Default() {
      return create_Empty();
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IMaybe<T>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IMaybe<T>>(JSON_mGrammar_Compile.Maybe<T>.Default());
    }
    public static _IMaybe<T> create_Empty() {
      return new Maybe_Empty<T>();
    }
    public static _IMaybe<T> create_NonEmpty(T t) {
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
    public abstract _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0);
  }
  public class Maybe_Empty<T> : Maybe<T> {
    public Maybe_Empty() {
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
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
  public class Maybe_NonEmpty<T> : Maybe<T> {
    public readonly T t;
    public Maybe_NonEmpty(T t) {
      this.t = t;
    }
    public override _IMaybe<__T> DowncastClone<__T>(Func<T, __T> converter0) {
      if (this is _IMaybe<__T> dt) { return dt; }
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

  public interface _ISuffixed<out T, out S> {
    bool is_Suffixed { get; }
    T dtor_t { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> dtor_suffix { get; }
    _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1);
  }
  public class Suffixed<T, S> : _ISuffixed<T, S> {
    public readonly T t;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix;
    public Suffixed(T t, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix) {
      this.t = t;
      this.suffix = suffix;
    }
    public _ISuffixed<__T, __S> DowncastClone<__T, __S>(Func<T, __T> converter0, Func<S, __S> converter1) {
      if (this is _ISuffixed<__T, __S> dt) { return dt; }
      return new Suffixed<__T, __S>(converter0(t), (suffix).DowncastClone<JSON_mGrammar_Compile._IStructural<__S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile._IStructural<S>, JSON_mGrammar_Compile._IStructural<__S>>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Suffixed<T, S>;
      return oth != null && object.Equals(this.t, oth.t) && object.Equals(this.suffix, oth.suffix);
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
    public static _ISuffixed<T, S> Default(T _default_T) {
      return create(_default_T, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<S>>.Default());
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._ISuffixed<T, S>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._ISuffixed<T, S>>(JSON_mGrammar_Compile.Suffixed<T, S>.Default(_td_T.Default()));
    }
    public static _ISuffixed<T, S> create(T t, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> suffix) {
      return new Suffixed<T, S>(t, suffix);
    }
    public bool is_Suffixed { get { return true; } }
    public T dtor_t {
      get {
        return this.t;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<S>> dtor_suffix {
      get {
        return this.suffix;
      }
    }
  }

  public partial class SuffixedSequence<D, S> {
    public static Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>>>(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<D, S>>.Empty);
    }
  }

  public interface _IBracketed<out L, out D, out S, out R> {
    bool is_Bracketed { get; }
    JSON_mGrammar_Compile._IStructural<L> dtor_l { get; }
    Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> dtor_data { get; }
    JSON_mGrammar_Compile._IStructural<R> dtor_r { get; }
    _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3);
  }
  public class Bracketed<L, D, S, R> : _IBracketed<L, D, S, R> {
    public readonly JSON_mGrammar_Compile._IStructural<L> l;
    public readonly Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data;
    public readonly JSON_mGrammar_Compile._IStructural<R> r;
    public Bracketed(JSON_mGrammar_Compile._IStructural<L> l, Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data, JSON_mGrammar_Compile._IStructural<R> r) {
      this.l = l;
      this.data = data;
      this.r = r;
    }
    public _IBracketed<__L, __D, __S, __R> DowncastClone<__L, __D, __S, __R>(Func<L, __L> converter0, Func<D, __D> converter1, Func<S, __S> converter2, Func<R, __R> converter3) {
      if (this is _IBracketed<__L, __D, __S, __R> dt) { return dt; }
      return new Bracketed<__L, __D, __S, __R>((l).DowncastClone<__L>(Dafny.Helpers.CastConverter<L, __L>), (data).DowncastClone<JSON_mGrammar_Compile._ISuffixed<__D, __S>>(Dafny.Helpers.CastConverter<JSON_mGrammar_Compile._ISuffixed<D, S>, JSON_mGrammar_Compile._ISuffixed<__D, __S>>), (r).DowncastClone<__R>(Dafny.Helpers.CastConverter<R, __R>));
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.Bracketed<L, D, S, R>;
      return oth != null && object.Equals(this.l, oth.l) && object.Equals(this.data, oth.data) && object.Equals(this.r, oth.r);
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
    public static _IBracketed<L, D, S, R> Default(L _default_L, R _default_R) {
      return create(JSON_mGrammar_Compile.Structural<L>.Default(_default_L), Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<D, S>>.Empty, JSON_mGrammar_Compile.Structural<R>.Default(_default_R));
    }
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IBracketed<L, D, S, R>> _TypeDescriptor(Dafny.TypeDescriptor<L> _td_L, Dafny.TypeDescriptor<R> _td_R) {
      return new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IBracketed<L, D, S, R>>(JSON_mGrammar_Compile.Bracketed<L, D, S, R>.Default(_td_L.Default(), _td_R.Default()));
    }
    public static _IBracketed<L, D, S, R> create(JSON_mGrammar_Compile._IStructural<L> l, Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> data, JSON_mGrammar_Compile._IStructural<R> r) {
      return new Bracketed<L, D, S, R>(l, data, r);
    }
    public bool is_Bracketed { get { return true; } }
    public JSON_mGrammar_Compile._IStructural<L> dtor_l {
      get {
        return this.l;
      }
    }
    public Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<D, S>> dtor_data {
      get {
        return this.data;
      }
    }
    public JSON_mGrammar_Compile._IStructural<R> dtor_r {
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

  public interface _Ijkv {
    bool is_KV { get; }
    Views_mCore_Compile.View__ dtor_k { get; }
    JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__> dtor_colon { get; }
    JSON_mGrammar_Compile._IValue dtor_v { get; }
    _Ijkv DowncastClone();
  }
  public class jkv : _Ijkv {
    public readonly Views_mCore_Compile.View__ k;
    public readonly JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__> colon;
    public readonly JSON_mGrammar_Compile._IValue v;
    public jkv(Views_mCore_Compile.View__ k, JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__> colon, JSON_mGrammar_Compile._IValue v) {
      this.k = k;
      this.colon = colon;
      this.v = v;
    }
    public _Ijkv DowncastClone() {
      if (this is _Ijkv dt) { return dt; }
      return new jkv(k, colon, v);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jkv;
      return oth != null && object.Equals(this.k, oth.k) && object.Equals(this.colon, oth.colon) && object.Equals(this.v, oth.v);
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
    private static readonly _Ijkv theDefault = create(JSON_mGrammar_Compile.jstring.Default(), JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>.Default(JSON_mGrammar_Compile.jcolon.Default()), JSON_mGrammar_Compile.Value.Default());
    public static _Ijkv Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijkv> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijkv>(JSON_mGrammar_Compile.jkv.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijkv> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijkv create(Views_mCore_Compile.View__ k, JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__> colon, JSON_mGrammar_Compile._IValue v) {
      return new jkv(k, colon, v);
    }
    public bool is_KV { get { return true; } }
    public Views_mCore_Compile.View__ dtor_k {
      get {
        return this.k;
      }
    }
    public JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__> dtor_colon {
      get {
        return this.colon;
      }
    }
    public JSON_mGrammar_Compile._IValue dtor_v {
      get {
        return this.v;
      }
    }
  }

  public interface _Ijfrac {
    bool is_JFrac { get; }
    Views_mCore_Compile.View__ dtor_period { get; }
    Views_mCore_Compile.View__ dtor_num { get; }
    _Ijfrac DowncastClone();
  }
  public class jfrac : _Ijfrac {
    public readonly Views_mCore_Compile.View__ period;
    public readonly Views_mCore_Compile.View__ num;
    public jfrac(Views_mCore_Compile.View__ period, Views_mCore_Compile.View__ num) {
      this.period = period;
      this.num = num;
    }
    public _Ijfrac DowncastClone() {
      if (this is _Ijfrac dt) { return dt; }
      return new jfrac(period, num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jfrac;
      return oth != null && object.Equals(this.period, oth.period) && object.Equals(this.num, oth.num);
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
    private static readonly _Ijfrac theDefault = create(JSON_mGrammar_Compile.jperiod.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static _Ijfrac Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac>(JSON_mGrammar_Compile.jfrac.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijfrac> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijfrac create(Views_mCore_Compile.View__ period, Views_mCore_Compile.View__ num) {
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

  public interface _Ijexp {
    bool is_JExp { get; }
    Views_mCore_Compile.View__ dtor_e { get; }
    Views_mCore_Compile.View__ dtor_sign { get; }
    Views_mCore_Compile.View__ dtor_num { get; }
    _Ijexp DowncastClone();
  }
  public class jexp : _Ijexp {
    public readonly Views_mCore_Compile.View__ e;
    public readonly Views_mCore_Compile.View__ sign;
    public readonly Views_mCore_Compile.View__ num;
    public jexp(Views_mCore_Compile.View__ e, Views_mCore_Compile.View__ sign, Views_mCore_Compile.View__ num) {
      this.e = e;
      this.sign = sign;
      this.num = num;
    }
    public _Ijexp DowncastClone() {
      if (this is _Ijexp dt) { return dt; }
      return new jexp(e, sign, num);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jexp;
      return oth != null && object.Equals(this.e, oth.e) && object.Equals(this.sign, oth.sign) && object.Equals(this.num, oth.num);
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
    private static readonly _Ijexp theDefault = create(JSON_mGrammar_Compile.je.Default(), JSON_mGrammar_Compile.jsign.Default(), JSON_mGrammar_Compile.jnum.Default());
    public static _Ijexp Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp>(JSON_mGrammar_Compile.jexp.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijexp> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijexp create(Views_mCore_Compile.View__ e, Views_mCore_Compile.View__ sign, Views_mCore_Compile.View__ num) {
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

  public interface _Ijnumber {
    bool is_JNumber { get; }
    Views_mCore_Compile.View__ dtor_minus { get; }
    Views_mCore_Compile.View__ dtor_num { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> dtor_frac { get; }
    JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> dtor_exp { get; }
    _Ijnumber DowncastClone();
  }
  public class jnumber : _Ijnumber {
    public readonly Views_mCore_Compile.View__ minus;
    public readonly Views_mCore_Compile.View__ num;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac;
    public readonly JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp;
    public jnumber(Views_mCore_Compile.View__ minus, Views_mCore_Compile.View__ num, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp) {
      this.minus = minus;
      this.num = num;
      this.frac = frac;
      this.exp = exp;
    }
    public _Ijnumber DowncastClone() {
      if (this is _Ijnumber dt) { return dt; }
      return new jnumber(minus, num, frac, exp);
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mGrammar_Compile.jnumber;
      return oth != null && object.Equals(this.minus, oth.minus) && object.Equals(this.num, oth.num) && object.Equals(this.frac, oth.frac) && object.Equals(this.exp, oth.exp);
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
    private static readonly _Ijnumber theDefault = create(JSON_mGrammar_Compile.jminus.Default(), JSON_mGrammar_Compile.jnum.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.Default(), JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.Default());
    public static _Ijnumber Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber>(JSON_mGrammar_Compile.jnumber.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._Ijnumber> _TypeDescriptor() {
      return _TYPE;
    }
    public static _Ijnumber create(Views_mCore_Compile.View__ minus, Views_mCore_Compile.View__ num, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> frac, JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> exp) {
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
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac> dtor_frac {
      get {
        return this.frac;
      }
    }
    public JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp> dtor_exp {
      get {
        return this.exp;
      }
    }
  }

  public interface _IValue {
    bool is_Null { get; }
    bool is_Bool { get; }
    bool is_String { get; }
    bool is_Number { get; }
    bool is_Object { get; }
    bool is_Array { get; }
    Views_mCore_Compile.View__ dtor_n { get; }
    Views_mCore_Compile.View__ dtor_b { get; }
    Views_mCore_Compile.View__ dtor_str { get; }
    JSON_mGrammar_Compile._Ijnumber dtor_num { get; }
    JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> dtor_obj { get; }
    JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> dtor_arr { get; }
    _IValue DowncastClone();
  }
  public abstract class Value : _IValue {
    public Value() { }
    private static readonly _IValue theDefault = create_Null(JSON_mGrammar_Compile.jnull.Default());
    public static _IValue Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue> _TYPE = new Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue>(JSON_mGrammar_Compile.Value.Default());
    public static Dafny.TypeDescriptor<JSON_mGrammar_Compile._IValue> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IValue create_Null(Views_mCore_Compile.View__ n) {
      return new Value_Null(n);
    }
    public static _IValue create_Bool(Views_mCore_Compile.View__ b) {
      return new Value_Bool(b);
    }
    public static _IValue create_String(Views_mCore_Compile.View__ str) {
      return new Value_String(str);
    }
    public static _IValue create_Number(JSON_mGrammar_Compile._Ijnumber num) {
      return new Value_Number(num);
    }
    public static _IValue create_Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj) {
      return new Value_Object(obj);
    }
    public static _IValue create_Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr) {
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
    public JSON_mGrammar_Compile._Ijnumber dtor_num {
      get {
        var d = this;
        return ((Value_Number)d).num;
      }
    }
    public JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> dtor_obj {
      get {
        var d = this;
        return ((Value_Object)d).obj;
      }
    }
    public JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> dtor_arr {
      get {
        var d = this;
        return ((Value_Array)d).arr;
      }
    }
    public abstract _IValue DowncastClone();
  }
  public class Value_Null : Value {
    public readonly Views_mCore_Compile.View__ n;
    public Value_Null(Views_mCore_Compile.View__ n) {
      this.n = n;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
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
  public class Value_Bool : Value {
    public readonly Views_mCore_Compile.View__ b;
    public Value_Bool(Views_mCore_Compile.View__ b) {
      this.b = b;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
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
  public class Value_String : Value {
    public readonly Views_mCore_Compile.View__ str;
    public Value_String(Views_mCore_Compile.View__ str) {
      this.str = str;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
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
  public class Value_Number : Value {
    public readonly JSON_mGrammar_Compile._Ijnumber num;
    public Value_Number(JSON_mGrammar_Compile._Ijnumber num) {
      this.num = num;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
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
  public class Value_Object : Value {
    public readonly JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj;
    public Value_Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj) {
      this.obj = obj;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
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
  public class Value_Array : Value {
    public readonly JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr;
    public Value_Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr) {
      this.arr = arr;
    }
    public override _IValue DowncastClone() {
      if (this is _IValue dt) { return dt; }
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
    public static Dafny.ISequence<byte> Structural<__T>(JSON_mGrammar_Compile._IStructural<__T> self, Func<__T, Dafny.ISequence<byte>> pt)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_before), Dafny.Helpers.Id<Func<__T, Dafny.ISequence<byte>>>(pt)((self).dtor_t)), JSON_mSpec_Compile.__default.View((self).dtor_after));
    }
    public static Dafny.ISequence<byte> StructuralView(JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__> self) {
      return JSON_mSpec_Compile.__default.Structural<Views_mCore_Compile.View__>(self, JSON_mSpec_Compile.__default.View);
    }
    public static Dafny.ISequence<byte> Maybe<__T>(JSON_mGrammar_Compile._IMaybe<__T> self, Func<__T, Dafny.ISequence<byte>> pt)
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
        Dafny.ISequence<__T> _in6 = (ts).Drop(BigInteger.One);
        Func<__T, Dafny.ISequence<byte>> _in7 = pt;
        ts = _in6;
        pt = _in7;
        goto TAIL_CALL_START;
      }
    }
    public static Dafny.ISequence<byte> Bracketed<__D, __S>(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, __D, __S, Views_mCore_Compile.View__> self, Func<JSON_mGrammar_Compile._ISuffixed<__D, __S>, Dafny.ISequence<byte>> pdatum)
    {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.StructuralView((self).dtor_l), JSON_mSpec_Compile.__default.ConcatBytes<JSON_mGrammar_Compile._ISuffixed<__D, __S>>((self).dtor_data, pdatum)), JSON_mSpec_Compile.__default.StructuralView((self).dtor_r));
    }
    public static Dafny.ISequence<byte> KV(JSON_mGrammar_Compile._Ijkv self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_k), JSON_mSpec_Compile.__default.StructuralView((self).dtor_colon)), JSON_mSpec_Compile.__default.Value((self).dtor_v));
    }
    public static Dafny.ISequence<byte> Frac(JSON_mGrammar_Compile._Ijfrac self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_period), JSON_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Exp(JSON_mGrammar_Compile._Ijexp self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_e), JSON_mSpec_Compile.__default.View((self).dtor_sign)), JSON_mSpec_Compile.__default.View((self).dtor_num));
    }
    public static Dafny.ISequence<byte> Number(JSON_mGrammar_Compile._Ijnumber self) {
      return Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.View((self).dtor_minus), JSON_mSpec_Compile.__default.View((self).dtor_num)), JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._Ijfrac>((self).dtor_frac, JSON_mSpec_Compile.__default.Frac)), JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._Ijexp>((self).dtor_exp, JSON_mSpec_Compile.__default.Exp));
    }
    public static Dafny.ISequence<byte> String(Views_mCore_Compile.View__ self) {
      return JSON_mSpec_Compile.__default.View(self);
    }
    public static Dafny.ISequence<byte> CommaSuffix(JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> c) {
      return JSON_mSpec_Compile.__default.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>(c, JSON_mSpec_Compile.__default.StructuralView);
    }
    public static Dafny.ISequence<byte> Member(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.KV((self).dtor_t), JSON_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Item(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__> self) {
      return Dafny.Sequence<byte>.Concat(JSON_mSpec_Compile.__default.Value((self).dtor_t), JSON_mSpec_Compile.__default.CommaSuffix((self).dtor_suffix));
    }
    public static Dafny.ISequence<byte> Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj) {
      return JSON_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>(obj, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>>>((_24_obj) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>)((_25_d) => {
        return JSON_mSpec_Compile.__default.Member(_25_d);
      })))(obj));
    }
    public static Dafny.ISequence<byte> Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr) {
      return JSON_mSpec_Compile.__default.Bracketed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>(arr, Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>, Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>>>((_26_arr) => ((System.Func<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>, Dafny.ISequence<byte>>)((_27_d) => {
        return JSON_mSpec_Compile.__default.Item(_27_d);
      })))(arr));
    }
    public static Dafny.ISequence<byte> Value(JSON_mGrammar_Compile._IValue self) {
      JSON_mGrammar_Compile._IValue _source5 = self;
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
        JSON_mGrammar_Compile._Ijnumber _34___mcc_h3 = _source5.dtor_num;
        JSON_mGrammar_Compile._Ijnumber _35_num = _34___mcc_h3;
        return JSON_mSpec_Compile.__default.Number(_35_num);
      } else if (_source5.is_Object) {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _36___mcc_h4 = _source5.dtor_obj;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _37_obj = _36___mcc_h4;
        return JSON_mSpec_Compile.__default.Object(_37_obj);
      } else {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _38___mcc_h5 = _source5.dtor_arr;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _39_arr = _38___mcc_h5;
        return JSON_mSpec_Compile.__default.Array(_39_arr);
      }
    }
    public static Dafny.ISequence<byte> JSON(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return JSON_mSpec_Compile.__default.Structural<JSON_mGrammar_Compile._IValue>(js, JSON_mSpec_Compile.__default.Value);
    }
  }
} // end of namespace JSON_mSpec_Compile
namespace JSON_mSpecProperties_Compile {

} // end of namespace JSON_mSpecProperties_Compile
namespace JSON_mZeroCopy_mSerializer_Compile {

  public interface _IError {
    bool is_OutOfMemory { get; }
    _IError DowncastClone();
  }
  public class Error : _IError {
    public Error() {
    }
    public _IError DowncastClone() {
      if (this is _IError dt) { return dt; }
      return new Error();
    }
    public override bool Equals(object other) {
      var oth = other as JSON_mZeroCopy_mSerializer_Compile.Error;
      return oth != null;
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
    private static readonly _IError theDefault = create();
    public static _IError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile._IError> _TYPE = new Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile._IError>(JSON_mZeroCopy_mSerializer_Compile.Error.Default());
    public static Dafny.TypeDescriptor<JSON_mZeroCopy_mSerializer_Compile._IError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IError create() {
      return new Error();
    }
    public bool is_OutOfMemory { get { return true; } }
    public static System.Collections.Generic.IEnumerable<_IError> AllSingletonConstructors {
      get {
        yield return Error.create();
      }
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> Serialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js)
    {
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> rbs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile._IError>.Default(new byte[0]);
      Views_mWriters_Compile._IWriter__ _40_writer;
      _40_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile._IOutcome<JSON_mZeroCopy_mSerializer_Compile._IError> _41_valueOrError0 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile._IError>.Default();
      _41_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile._IError>((_40_writer).Unsaturated_q, JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_41_valueOrError0).IsFailure()) {
        rbs = (_41_valueOrError0).PropagateFailure<byte[]>();
        return rbs;
      }
      byte[] _42_bs;
      byte[] _out0;
      _out0 = (_40_writer).ToArray();
      _42_bs = _out0;
      rbs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile._IError>.create_Success(_42_bs);
      return rbs;
      return rbs;
    }
    public static Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> SerializeTo(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] bs)
    {
      Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile._IError>.Default(0);
      Views_mWriters_Compile._IWriter__ _43_writer;
      _43_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Text(js);
      Wrappers_Compile._IOutcome<JSON_mZeroCopy_mSerializer_Compile._IError> _44_valueOrError0 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile._IError>.Default();
      _44_valueOrError0 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile._IError>((_43_writer).Unsaturated_q, JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_44_valueOrError0).IsFailure()) {
        len = (_44_valueOrError0).PropagateFailure<uint>();
        return len;
      }
      Wrappers_Compile._IOutcome<JSON_mZeroCopy_mSerializer_Compile._IError> _45_valueOrError1 = Wrappers_Compile.Outcome<JSON_mZeroCopy_mSerializer_Compile._IError>.Default();
      _45_valueOrError1 = Wrappers_Compile.__default.Need<JSON_mZeroCopy_mSerializer_Compile._IError>((new BigInteger((_43_writer).dtor_length)) <= (new BigInteger((bs).Length)), JSON_mZeroCopy_mSerializer_Compile.Error.create());
      if ((_45_valueOrError1).IsFailure()) {
        len = (_45_valueOrError1).PropagateFailure<uint>();
        return len;
      }
      (_43_writer).Blit(bs);
      len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile._IError>.create_Success((_43_writer).dtor_length);
      return len;
      return len;
    }
    public static Views_mWriters_Compile._IWriter__ Text(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return JSON_mZeroCopy_mSerializer_Compile.__default.JSON(js, Views_mWriters_Compile.Writer__.Empty);
    }
    public static Views_mWriters_Compile._IWriter__ JSON(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, Views_mWriters_Compile._IWriter__ writer)
    {
      return (((writer).Append((js).dtor_before)).Then(Dafny.Helpers.Id<Func<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__>>>((_46_js) => ((System.Func<Views_mWriters_Compile._IWriter__, Views_mWriters_Compile._IWriter__>)((_47_wr) => {
        return JSON_mZeroCopy_mSerializer_Compile.__default.Value((_46_js).dtor_t, _47_wr);
      })))(js))).Append((js).dtor_after);
    }
    public static Views_mWriters_Compile._IWriter__ Value(JSON_mGrammar_Compile._IValue v, Views_mWriters_Compile._IWriter__ writer)
    {
      JSON_mGrammar_Compile._IValue _source6 = v;
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
        JSON_mGrammar_Compile._Ijnumber _54___mcc_h3 = _source6.dtor_num;
        JSON_mGrammar_Compile._Ijnumber _55_num = _54___mcc_h3;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Number(_55_num, writer);
      } else if (_source6.is_Object) {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _56___mcc_h4 = _source6.dtor_obj;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _57_obj = _56___mcc_h4;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Object(_57_obj, writer);
      } else {
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _58___mcc_h5 = _source6.dtor_arr;
        JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _59_arr = _58___mcc_h5;
        return JSON_mZeroCopy_mSerializer_Compile.__default.Array(_59_arr, writer);
      }
    }
    public static Views_mWriters_Compile._IWriter__ String(Views_mCore_Compile.View__ str, Views_mWriters_Compile._IWriter__ writer)
    {
      return (writer).Append(str);
    }
    public static Views_mWriters_Compile._IWriter__ Number(JSON_mGrammar_Compile._Ijnumber num, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _60_writer = ((writer).Append((num).dtor_minus)).Append((num).dtor_num);
      Views_mWriters_Compile._IWriter__ _61_writer = ((((num).dtor_frac).is_NonEmpty) ? (((_60_writer).Append((((num).dtor_frac).dtor_t).dtor_period)).Append((((num).dtor_frac).dtor_t).dtor_num)) : (_60_writer));
      Views_mWriters_Compile._IWriter__ _62_writer = ((((num).dtor_exp).is_NonEmpty) ? ((((_61_writer).Append((((num).dtor_exp).dtor_t).dtor_e)).Append((((num).dtor_exp).dtor_t).dtor_sign)).Append((((num).dtor_exp).dtor_t).dtor_num)) : (_61_writer));
      return _62_writer;
    }
    public static Views_mWriters_Compile._IWriter__ StructuralView(JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__> st, Views_mWriters_Compile._IWriter__ writer)
    {
      return (((writer).Append((st).dtor_before)).Append((st).dtor_t)).Append((st).dtor_after);
    }
    public static Views_mWriters_Compile._IWriter__ Object(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _63_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_l, writer);
      Views_mWriters_Compile._IWriter__ _64_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Members(obj, _63_writer);
      Views_mWriters_Compile._IWriter__ _65_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((obj).dtor_r, _64_writer);
      return _65_writer;
    }
    public static Views_mWriters_Compile._IWriter__ Array(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _66_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_l, writer);
      Views_mWriters_Compile._IWriter__ _67_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Items(arr, _66_writer);
      Views_mWriters_Compile._IWriter__ _68_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView((arr).dtor_r, _67_writer);
      return _68_writer;
    }
    public static Views_mWriters_Compile._IWriter__ Members(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      Views_mWriters_Compile._IWriter__ _out1;
      _out1 = JSON_mZeroCopy_mSerializer_Compile.__default.MembersImpl(obj, writer);
      wr = _out1;
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ Items(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      Views_mWriters_Compile._IWriter__ _out2;
      _out2 = JSON_mZeroCopy_mSerializer_Compile.__default.ItemsImpl(arr, writer);
      wr = _out2;
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ MembersImpl(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> obj, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>> _69_members;
      _69_members = (obj).dtor_data;
      BigInteger _hi1 = new BigInteger((_69_members).Count);
      for (BigInteger _70_i = BigInteger.Zero; _70_i < _hi1; _70_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Member((_69_members).Select(_70_i), wr);
      }
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ ItemsImpl(JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> arr, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ wr = Views_mWriters_Compile.Writer.Default();
      wr = writer;
      Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>> _71_items;
      _71_items = (arr).dtor_data;
      BigInteger _hi2 = new BigInteger((_71_items).Count);
      for (BigInteger _72_i = BigInteger.Zero; _72_i < _hi2; _72_i++) {
        wr = JSON_mZeroCopy_mSerializer_Compile.__default.Item((_71_items).Select(_72_i), wr);
      }
      return wr;
    }
    public static Views_mWriters_Compile._IWriter__ Member(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__> m, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _73_writer = (writer).Append(((m).dtor_t).dtor_k);
      Views_mWriters_Compile._IWriter__ _74_writer = JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_t).dtor_colon, _73_writer);
      Views_mWriters_Compile._IWriter__ _75_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Value(((m).dtor_t).dtor_v, _74_writer);
      if (((m).dtor_suffix).is_Empty) {
        return _75_writer;
      } else {
        return JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _75_writer);
      }
    }
    public static Views_mWriters_Compile._IWriter__ Item(JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__> m, Views_mWriters_Compile._IWriter__ writer)
    {
      Views_mWriters_Compile._IWriter__ _76_writer = JSON_mZeroCopy_mSerializer_Compile.__default.Value((m).dtor_t, writer);
      if (((m).dtor_suffix).is_Empty) {
        return _76_writer;
      } else {
        return JSON_mZeroCopy_mSerializer_Compile.__default.StructuralView(((m).dtor_suffix).dtor_t, _76_writer);
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mSerializer_Compile
namespace Lexers_mCore_Compile {

  public interface _ILexerResult<out T, out R> {
    bool is_Accept { get; }
    bool is_Reject { get; }
    bool is_Partial { get; }
    R dtor_err { get; }
    T dtor_st { get; }
    _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public abstract class LexerResult<T, R> : _ILexerResult<T, R> {
    public LexerResult() { }
    public static _ILexerResult<T, R> Default() {
      return create_Accept();
    }
    public static Dafny.TypeDescriptor<Lexers_mCore_Compile._ILexerResult<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Lexers_mCore_Compile._ILexerResult<T, R>>(Lexers_mCore_Compile.LexerResult<T, R>.Default());
    }
    public static _ILexerResult<T, R> create_Accept() {
      return new LexerResult_Accept<T, R>();
    }
    public static _ILexerResult<T, R> create_Reject(R err) {
      return new LexerResult_Reject<T, R>(err);
    }
    public static _ILexerResult<T, R> create_Partial(T st) {
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
    public abstract _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class LexerResult_Accept<T, R> : LexerResult<T, R> {
    public LexerResult_Accept() {
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
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
  public class LexerResult_Reject<T, R> : LexerResult<T, R> {
    public readonly R err;
    public LexerResult_Reject(R err) {
      this.err = err;
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
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
  public class LexerResult_Partial<T, R> : LexerResult<T, R> {
    public readonly T st;
    public LexerResult_Partial(T st) {
      this.st = st;
    }
    public override _ILexerResult<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ILexerResult<__T, __R> dt) { return dt; }
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

  public interface _IStringLexerState {
    bool is_Start { get; }
    bool is_Body { get; }
    bool is_End { get; }
    bool dtor_escaped { get; }
    _IStringLexerState DowncastClone();
  }
  public abstract class StringLexerState : _IStringLexerState {
    public StringLexerState() { }
    private static readonly _IStringLexerState theDefault = create_Start();
    public static _IStringLexerState Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<Lexers_mStrings_Compile._IStringLexerState> _TYPE = new Dafny.TypeDescriptor<Lexers_mStrings_Compile._IStringLexerState>(Lexers_mStrings_Compile.StringLexerState.Default());
    public static Dafny.TypeDescriptor<Lexers_mStrings_Compile._IStringLexerState> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IStringLexerState create_Start() {
      return new StringLexerState_Start();
    }
    public static _IStringLexerState create_Body(bool escaped) {
      return new StringLexerState_Body(escaped);
    }
    public static _IStringLexerState create_End() {
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
    public abstract _IStringLexerState DowncastClone();
  }
  public class StringLexerState_Start : StringLexerState {
    public StringLexerState_Start() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
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
  public class StringLexerState_Body : StringLexerState {
    public readonly bool escaped;
    public StringLexerState_Body(bool escaped) {
      this.escaped = escaped;
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
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
  public class StringLexerState_End : StringLexerState {
    public StringLexerState_End() {
    }
    public override _IStringLexerState DowncastClone() {
      if (this is _IStringLexerState dt) { return dt; }
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
    public static Lexers_mCore_Compile._ILexerResult<bool, __R> StringBody<__R>(bool escaped, short @byte)
    {
      if ((@byte) == ((short)('\\'))) {
        return Lexers_mCore_Compile.LexerResult<bool, __R>.create_Partial(!(escaped));
      } else if (((@byte) == ((short)('\"'))) && (!(escaped))) {
        return Lexers_mCore_Compile.LexerResult<bool, __R>.create_Accept();
      } else {
        return Lexers_mCore_Compile.LexerResult<bool, __R>.create_Partial(false);
      }
    }
    public static Lexers_mCore_Compile._ILexerResult<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>> String(Lexers_mStrings_Compile._IStringLexerState st, short @byte)
    {
      Lexers_mStrings_Compile._IStringLexerState _source7 = st;
      if (_source7.is_Start) {
        if ((@byte) == ((short)('\"'))) {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(false));
        } else {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Reject(Dafny.Sequence<char>.FromString("String must start with double quote"));
        }
      } else if (_source7.is_Body) {
        bool _77___mcc_h0 = _source7.dtor_escaped;
        bool _78_escaped = _77___mcc_h0;
        if ((@byte) == ((short)('\\'))) {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(!(_78_escaped)));
        } else if (((@byte) == ((short)('\"'))) && (!(_78_escaped))) {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_End());
        } else {
          return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Partial(Lexers_mStrings_Compile.StringLexerState.create_Body(false));
        }
      } else {
        return Lexers_mCore_Compile.LexerResult<Lexers_mStrings_Compile._IStringLexerState, Dafny.ISequence<char>>.create_Accept();
      }
    }
    public static bool StringBodyLexerStart { get {
      return false;
    } }
    public static Lexers_mStrings_Compile._IStringLexerState StringLexerStart { get {
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

  public interface _ICursorError<out R> {
    bool is_EOF { get; }
    bool is_ExpectingByte { get; }
    bool is_ExpectingAnyByte { get; }
    bool is_OtherError { get; }
    byte dtor_expected { get; }
    short dtor_b { get; }
    Dafny.ISequence<byte> dtor_expected__sq { get; }
    R dtor_err { get; }
    _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
  }
  public abstract class CursorError<R> : _ICursorError<R> {
    public CursorError() { }
    public static _ICursorError<R> Default() {
      return create_EOF();
    }
    public static Dafny.TypeDescriptor<Cursors_Compile._ICursorError<R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Cursors_Compile._ICursorError<R>>(Cursors_Compile.CursorError<R>.Default());
    }
    public static _ICursorError<R> create_EOF() {
      return new CursorError_EOF<R>();
    }
    public static _ICursorError<R> create_ExpectingByte(byte expected, short b) {
      return new CursorError_ExpectingByte<R>(expected, b);
    }
    public static _ICursorError<R> create_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      return new CursorError_ExpectingAnyByte<R>(expected__sq, b);
    }
    public static _ICursorError<R> create_OtherError(R err) {
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
    public abstract _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0);
    public static Dafny.ISequence<char> _ToString(Cursors_Compile._ICursorError<R> _this, Func<R, Dafny.ISequence<char>> pr) {
      Cursors_Compile._ICursorError<R> _source8 = _this;
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
  public class CursorError_EOF<R> : CursorError<R> {
    public CursorError_EOF() {
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
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
  public class CursorError_ExpectingByte<R> : CursorError<R> {
    public readonly byte expected;
    public readonly short b;
    public CursorError_ExpectingByte(byte expected, short b) {
      this.expected = expected;
      this.b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
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
  public class CursorError_ExpectingAnyByte<R> : CursorError<R> {
    public readonly Dafny.ISequence<byte> expected__sq;
    public readonly short b;
    public CursorError_ExpectingAnyByte(Dafny.ISequence<byte> expected__sq, short b) {
      this.expected__sq = expected__sq;
      this.b = b;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
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
  public class CursorError_OtherError<R> : CursorError<R> {
    public readonly R err;
    public CursorError_OtherError(R err) {
      this.err = err;
    }
    public override _ICursorError<__R> DowncastClone<__R>(Func<R, __R> converter0) {
      if (this is _ICursorError<__R> dt) { return dt; }
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
      return this;
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
    public Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>> Get<__R>(__R err) {
      if ((this).EOF_q) {
        return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_OtherError(err));
      } else {
        return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Success((this).Skip(1U));
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>> AssertByte<__R>(byte b) {
      short _99_nxt = (this).Peek();
      if ((_99_nxt) == ((short)(b))) {
        return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Success((this).Skip(1U));
      } else {
        return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_ExpectingByte(b, _99_nxt));
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>> AssertBytes<__R>(Dafny.ISequence<byte> bs, uint offset)
    {
      Cursor__ _this = this;
    TAIL_CALL_START: ;
      if ((offset) == ((uint)(bs).LongCount)) {
        return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Success(_this);
      } else {
        Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>> _100_valueOrError0 = (_this).AssertByte<__R>((byte)((bs).Select(offset)));
        if ((_100_valueOrError0).IsFailure()) {
          return (_100_valueOrError0).PropagateFailure<Cursors_Compile.Cursor__>();
        } else {
          Cursors_Compile.Cursor__ _101_ps = (_100_valueOrError0).Extract();
          var _in8 = _101_ps;
          Dafny.ISequence<byte> _in9 = bs;
          uint _in10 = (offset) + (1U);
          _this = _in8;
          bs = _in9;
          offset = _in10;
          goto TAIL_CALL_START;
        }
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>> AssertChar<__R>(char c0) {
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
    public Cursors_Compile.Cursor__ SkipWhile(Func<byte, bool> p) {
      Cursor__ _this = this;
    TAIL_CALL_START: ;
      if (((_this).EOF_q) || (!(Dafny.Helpers.Id<Func<byte, bool>>(p)((_this).SuffixAt(0U))))) {
        return _this;
      } else {
        var _in11 = (_this).Skip(1U);
        Func<byte, bool> _in12 = p;
        _this = _in11;
        p = _in12;
        goto TAIL_CALL_START;
      }
    }
    public Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>> SkipWhileLexer<__A, __R>(Func<__A, short, Lexers_mCore_Compile._ILexerResult<__A, __R>> step, __A st)
    {
      Cursor__ _this = this;
    TAIL_CALL_START: ;
      Lexers_mCore_Compile._ILexerResult<__A, __R> _source9 = Dafny.Helpers.Id<Func<__A, short, Lexers_mCore_Compile._ILexerResult<__A, __R>>>(step)(st, (_this).Peek());
      switch (_source9)
      {
        case LexerResult_Accept<__A, __R> accept:
          return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Success(_this);
        case LexerResult_Reject<__A, __R> { err: var _102___mcc_h0 }:
          __R _103_err = _102___mcc_h0;
          return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_OtherError(_103_err));
        case LexerResult_Partial<__A, __R> { st: var _104___mcc_h1 }:
          __A _105_st = _104___mcc_h1;
          if ((_this).EOF_q) {
            return Wrappers_Compile.Result<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_EOF());
          } else {
            var _in13 = (_this).Skip(1U);
            Func<__A, short, Lexers_mCore_Compile._ILexerResult<__A, __R>> _in14 = step;
            __A _in15 = _105_st;
            _this = _in13;
            step = _in14;
            st = _in15;
            goto TAIL_CALL_START;
          }
      }
      // Unreachable
      return null;
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
    public static Parsers_Compile._IParser__<T, R> Default() {
      return Parsers_Compile.__default.ParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>>(Parsers_Compile.Parser<T, R>.Default());
    }
  }

  public interface _IParser__<T, out R> {
    bool is_Parser { get; }
    Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> dtor_fn { get; }
    _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class Parser__<T, R> : _IParser__<T, R> {
    public readonly Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> fn;
    public Parser__(Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> fn) {
      this.fn = fn;
    }
    public _IParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _IParser__<__T, __R> dt) { return dt; }
      return new Parser__<__T, __R>((fn).DowncastClone<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>, Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>>(Dafny.Helpers.Id<Cursors_Compile.Cursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>, Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as Parsers_Compile.Parser__<T, R>;
      return oth != null && object.Equals(this.fn, oth.fn);
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
    public static _IParser__<T, R> Default(T _default_T) {
      return create(((Cursors_Compile.Cursor__ x0) => Wrappers_Compile.Result<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>.Default(Cursors_Compile.Split<T>.Default(_default_T))));
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>> _TypeDescriptor(Dafny.TypeDescriptor<T> _td_T) {
      return new Dafny.TypeDescriptor<Parsers_Compile._IParser__<T, R>>(Parsers_Compile.Parser__<T, R>.Default(_td_T.Default()));
    }
    public static _IParser__<T, R> create(Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> fn) {
      return new Parser__<T, R>(fn);
    }
    public bool is_Parser { get { return true; } }
    public Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> dtor_fn {
      get {
        return this.fn;
      }
    }
  }

  public interface _ISubParser__<T, out R> {
    bool is_SubParser { get; }
    Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> dtor_fn { get; }
    _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1);
  }
  public class SubParser__<T, R> : _ISubParser__<T, R> {
    public readonly Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> fn;
    public SubParser__(Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> fn) {
      this.fn = fn;
    }
    public _ISubParser__<__T, __R> DowncastClone<__T, __R>(Func<T, __T> converter0, Func<R, __R> converter1) {
      if (this is _ISubParser__<__T, __R> dt) { return dt; }
      return new SubParser__<__T, __R>((fn).DowncastClone<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>, Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>>(Dafny.Helpers.Id<Cursors_Compile.Cursor__>, Dafny.Helpers.CastConverter<Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>, Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>>));
    }
    public override bool Equals(object other) {
      var oth = other as Parsers_Compile.SubParser__<T, R>;
      return oth != null && object.Equals(this.fn, oth.fn);
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
    public static _ISubParser__<T, R> Default() {
      return create(((Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>>)null));
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>>(Parsers_Compile.SubParser__<T, R>.Default());
    }
    public static _ISubParser__<T, R> create(Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> fn) {
      return new SubParser__<T, R>(fn);
    }
    public bool is_SubParser { get { return true; } }
    public Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<T>, Cursors_Compile._ICursorError<R>>> dtor_fn {
      get {
        return this.fn;
      }
    }
  }

  public partial class SubParser<T, R> {
    public static Parsers_Compile._ISubParser__<T, R> Default() {
      return Parsers_Compile.__default.SubParserWitness<T, R>();
    }
    public static Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>> _TypeDescriptor() {
      return new Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<T, R>>(Parsers_Compile.SubParser<T, R>.Default());
    }
  }

  public partial class __default {
    public static Parsers_Compile._IParser__<__T, __R> ParserWitness<__T, __R>() {
      return Parsers_Compile.Parser__<__T, __R>.create(((System.Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>>)((_106___v0) => {
  return Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_EOF());
})));
    }
    public static Parsers_Compile._ISubParser__<__T, __R> SubParserWitness<__T, __R>() {
      return Parsers_Compile.SubParser__<__T, __R>.create(((System.Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>>)((_107_cs) => {
  return Wrappers_Compile.Result<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<__R>>.create_Failure(Cursors_Compile.CursorError<__R>.create_EOF());
})));
    }
  }
} // end of namespace Parsers_Compile
namespace JSON_mZeroCopy_mDeserializer_mCore_Compile {

  public interface _IJSONError {
    bool is_UnterminatedSequence { get; }
    bool is_EmptyNumber { get; }
    bool is_ExpectingEOF { get; }
    bool is_IntOverflow { get; }
    _IJSONError DowncastClone();
    Dafny.ISequence<char> _ToString();
  }
  public abstract class JSONError : _IJSONError {
    public JSONError() { }
    private static readonly _IJSONError theDefault = create_UnterminatedSequence();
    public static _IJSONError Default() {
      return theDefault;
    }
    private static readonly Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _TYPE = new Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.Default());
    public static Dafny.TypeDescriptor<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _TypeDescriptor() {
      return _TYPE;
    }
    public static _IJSONError create_UnterminatedSequence() {
      return new JSONError_UnterminatedSequence();
    }
    public static _IJSONError create_EmptyNumber() {
      return new JSONError_EmptyNumber();
    }
    public static _IJSONError create_ExpectingEOF() {
      return new JSONError_ExpectingEOF();
    }
    public static _IJSONError create_IntOverflow() {
      return new JSONError_IntOverflow();
    }
    public bool is_UnterminatedSequence { get { return this is JSONError_UnterminatedSequence; } }
    public bool is_EmptyNumber { get { return this is JSONError_EmptyNumber; } }
    public bool is_ExpectingEOF { get { return this is JSONError_ExpectingEOF; } }
    public bool is_IntOverflow { get { return this is JSONError_IntOverflow; } }
    public static System.Collections.Generic.IEnumerable<_IJSONError> AllSingletonConstructors {
      get {
        yield return JSONError.create_UnterminatedSequence();
        yield return JSONError.create_EmptyNumber();
        yield return JSONError.create_ExpectingEOF();
        yield return JSONError.create_IntOverflow();
      }
    }
    public abstract _IJSONError DowncastClone();
    public Dafny.ISequence<char> _ToString() {
      JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError _source10 = this;
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
  public class JSONError_UnterminatedSequence : JSONError {
    public JSONError_UnterminatedSequence() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
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
  public class JSONError_EmptyNumber : JSONError {
    public JSONError_EmptyNumber() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
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
  public class JSONError_ExpectingEOF : JSONError {
    public JSONError_ExpectingEOF() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
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
  public class JSONError_IntOverflow : JSONError {
    public JSONError_IntOverflow() {
    }
    public override _IJSONError DowncastClone() {
      if (this is _IJSONError dt) { return dt; }
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
    private static readonly Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _TYPE = new Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>(Parsers_Compile.SubParser<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.Default());
    public static Dafny.TypeDescriptor<Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _TypeDescriptor() {
      return _TYPE;
    }
  }

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Get(Cursors_Compile.Cursor__ cs, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError err)
    {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _108_valueOrError0 = (cs).Get<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(err);
      if ((_108_valueOrError0).IsFailure()) {
        return (_108_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _109_cs = (_108_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_109_cs).Split());
      }
    }
    public static Cursors_Compile.Split<Views_mCore_Compile.View__> WS(Cursors_Compile.Cursor__ cs) {
      return ((cs).SkipWhile(JSON_mGrammar_Compile.__default.Blank_q)).Split();
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<__T>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Structural<__T>(Cursors_Compile.Cursor__ cs, Parsers_Compile._IParser__<__T, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> parser)
    {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      Views_mCore_Compile.View__ _110_before = _let_tmp_rhs0.dtor_t;
      Cursors_Compile.Cursor__ _111_cs = _let_tmp_rhs0.dtor_cs;
      Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _112_valueOrError0 = Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<__T>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>((parser).dtor_fn)(_111_cs);
      if ((_112_valueOrError0).IsFailure()) {
        return (_112_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<__T>>>();
      } else {
        Cursors_Compile.Split<__T> _let_tmp_rhs1 = (_112_valueOrError0).Extract();
        __T _113_val = _let_tmp_rhs1.dtor_t;
        Cursors_Compile.Cursor__ _114_cs = _let_tmp_rhs1.dtor_cs;
        Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs2 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_114_cs);
        Views_mCore_Compile.View__ _115_after = _let_tmp_rhs2.dtor_t;
        Cursors_Compile.Cursor__ _116_cs = _let_tmp_rhs2.dtor_cs;
        return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<__T>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<__T>>.create(JSON_mGrammar_Compile.Structural<__T>.create(_110_before, _113_val, _115_after), _116_cs));
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> TryStructural(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs3 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(cs);
      Views_mCore_Compile.View__ _117_before = _let_tmp_rhs3.dtor_t;
      Cursors_Compile.Cursor__ _118_cs = _let_tmp_rhs3.dtor_cs;
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs4 = ((_118_cs).SkipByte()).Split();
      Views_mCore_Compile.View__ _119_val = _let_tmp_rhs4.dtor_t;
      Cursors_Compile.Cursor__ _120_cs = _let_tmp_rhs4.dtor_cs;
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs5 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.WS(_120_cs);
      Views_mCore_Compile.View__ _121_after = _let_tmp_rhs5.dtor_t;
      Cursors_Compile.Cursor__ _122_cs = _let_tmp_rhs5.dtor_cs;
      return Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>.create(JSON_mGrammar_Compile.Structural<Views_mCore_Compile.View__>.create(_117_before, _119_val, _121_after), _122_cs);
    }
    public static Func<Views_mCore_Compile.View__, Dafny.ISequence<byte>> SpecView { get {
      return ((System.Func<Views_mCore_Compile.View__, Dafny.ISequence<byte>>)((_123_v) => {
        return JSON_mSpec_Compile.__default.View(_123_v);
      }));
    } }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mCore_Compile
namespace JSON_mZeroCopy_mDeserializer_mStrings_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> String(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _124_valueOrError0 = (cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>('\"');
      if ((_124_valueOrError0).IsFailure()) {
        return (_124_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _125_cs = (_124_valueOrError0).Extract();
        Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _126_valueOrError1 = (_125_cs).SkipWhileLexer<bool, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>((bool _eta0, short _eta1) => Lexers_mStrings_Compile.__default.StringBody<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(_eta0, _eta1), Lexers_mStrings_Compile.__default.StringBodyLexerStart);
        if ((_126_valueOrError1).IsFailure()) {
          return (_126_valueOrError1).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
        } else {
          Cursors_Compile.Cursor__ _127_cs = (_126_valueOrError1).Extract();
          Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _128_valueOrError2 = (_127_cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>('\"');
          if ((_128_valueOrError2).IsFailure()) {
            return (_128_valueOrError2).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
          } else {
            Cursors_Compile.Cursor__ _129_cs = (_128_valueOrError2).Extract();
            return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_129_cs).Split());
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
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> NonEmptyDigits(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _130_sp = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Digits(cs);
      Wrappers_Compile._IOutcome<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _131_valueOrError0 = Wrappers_Compile.__default.Need<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>(!(((_130_sp).dtor_t).Empty_q), Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_EmptyNumber()));
      if ((_131_valueOrError0).IsFailure()) {
        return (_131_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_130_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> NonZeroInt(Cursors_Compile.Cursor__ cs) {
      return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(cs);
    }
    public static Cursors_Compile.Split<Views_mCore_Compile.View__> OptionalMinus(Cursors_Compile.Cursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_132_c) => {
        return (_132_c) == ((byte)('-'));
      })))).Split();
    }
    public static Cursors_Compile.Split<Views_mCore_Compile.View__> OptionalSign(Cursors_Compile.Cursor__ cs) {
      return ((cs).SkipIf(((System.Func<byte, bool>)((_133_c) => {
        return ((_133_c) == ((byte)('-'))) || ((_133_c) == ((byte)('+')));
      })))).Split();
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> TrimmedInt(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _134_sp = ((cs).SkipIf(((System.Func<byte, bool>)((_135_c) => {
        return (_135_c) == ((byte)('0'));
      })))).Split();
      if (((_134_sp).dtor_t).Empty_q) {
        return JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonZeroInt((_134_sp).dtor_cs);
      } else {
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_134_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Exp(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs6 = ((cs).SkipIf(((System.Func<byte, bool>)((_136_c) => {
        return ((_136_c) == ((byte)('e'))) || ((_136_c) == ((byte)('E')));
      })))).Split();
      Views_mCore_Compile.View__ _137_e = _let_tmp_rhs6.dtor_t;
      Cursors_Compile.Cursor__ _138_cs = _let_tmp_rhs6.dtor_cs;
      if ((_137_e).Empty_q) {
        return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_Empty(), _138_cs));
      } else {
        Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs7 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalSign(_138_cs);
        Views_mCore_Compile.View__ _139_sign = _let_tmp_rhs7.dtor_t;
        Cursors_Compile.Cursor__ _140_cs = _let_tmp_rhs7.dtor_cs;
        Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _141_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_140_cs);
        if ((_141_valueOrError0).IsFailure()) {
          return (_141_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs8 = (_141_valueOrError0).Extract();
          Views_mCore_Compile.View__ _142_num = _let_tmp_rhs8.dtor_t;
          Cursors_Compile.Cursor__ _143_cs = _let_tmp_rhs8.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijexp>.create_NonEmpty(JSON_mGrammar_Compile.jexp.create(_137_e, _139_sign, _142_num)), _143_cs));
        }
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Frac(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs9 = ((cs).SkipIf(((System.Func<byte, bool>)((_144_c) => {
        return (_144_c) == ((byte)('.'));
      })))).Split();
      Views_mCore_Compile.View__ _145_period = _let_tmp_rhs9.dtor_t;
      Cursors_Compile.Cursor__ _146_cs = _let_tmp_rhs9.dtor_cs;
      if ((_145_period).Empty_q) {
        return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_Empty(), _146_cs));
      } else {
        Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _147_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NonEmptyDigits(_146_cs);
        if ((_147_valueOrError0).IsFailure()) {
          return (_147_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs10 = (_147_valueOrError0).Extract();
          Views_mCore_Compile.View__ _148_num = _let_tmp_rhs10.dtor_t;
          Cursors_Compile.Cursor__ _149_cs = _let_tmp_rhs10.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>.create(JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._Ijfrac>.create_NonEmpty(JSON_mGrammar_Compile.jfrac.create(_145_period, _148_num)), _149_cs));
        }
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber> NumberFromParts(Cursors_Compile.Split<Views_mCore_Compile.View__> minus, Cursors_Compile.Split<Views_mCore_Compile.View__> num, Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>> frac, Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>> exp)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber> _150_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>.create(JSON_mGrammar_Compile.jnumber.create((minus).dtor_t, (num).dtor_t, (frac).dtor_t, (exp).dtor_t), (exp).dtor_cs);
      return _150_sp;
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Number(Cursors_Compile.Cursor__ cs) {
      Cursors_Compile.Split<Views_mCore_Compile.View__> _151_minus = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.OptionalMinus(cs);
      Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _152_valueOrError0 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.TrimmedInt((_151_minus).dtor_cs);
      if ((_152_valueOrError0).IsFailure()) {
        return (_152_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>>();
      } else {
        Cursors_Compile.Split<Views_mCore_Compile.View__> _153_num = (_152_valueOrError0).Extract();
        Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _154_valueOrError1 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Frac((_153_num).dtor_cs);
        if ((_154_valueOrError1).IsFailure()) {
          return (_154_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijfrac>> _155_frac = (_154_valueOrError1).Extract();
          Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _156_valueOrError2 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Exp((_155_frac).dtor_cs);
          if ((_156_valueOrError2).IsFailure()) {
            return (_156_valueOrError2).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile._IMaybe<JSON_mGrammar_Compile._Ijexp>> _157_exp = (_156_valueOrError2).Extract();
            return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.NumberFromParts(_151_minus, _153_num, _155_frac, _157_exp));
          }
        }
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mNumbers_Compile
namespace JSON_mZeroCopy_mDeserializer_mObjectParams_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Colon(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _158_valueOrError0 = (cs).AssertChar<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(':');
      if ((_158_valueOrError0).IsFailure()) {
        return (_158_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _159_cs = (_158_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_159_cs).Split());
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv> KVFromParts(Cursors_Compile.Split<Views_mCore_Compile.View__> k, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> colon, Cursors_Compile.Split<JSON_mGrammar_Compile._IValue> v)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv> _160_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>.create(JSON_mGrammar_Compile.jkv.create((k).dtor_t, (colon).dtor_t, (v).dtor_t), (v).dtor_cs);
      return _160_sp;
    }
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile._Ijkv t) {
      return JSON_mSpec_Compile.__default.KV(t);
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Element(Cursors_Compile.Cursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _161_valueOrError0 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
      if ((_161_valueOrError0).IsFailure()) {
        return (_161_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>>();
      } else {
        Cursors_Compile.Split<Views_mCore_Compile.View__> _162_k = (_161_valueOrError0).Extract();
        Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _163_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>((_162_k).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Colon));
        if ((_163_valueOrError1).IsFailure()) {
          return (_163_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _164_colon = (_163_valueOrError1).Extract();
          Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _165_valueOrError2 = Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>((json).dtor_fn)((_164_colon).dtor_cs);
          if ((_165_valueOrError2).IsFailure()) {
            return (_165_valueOrError2).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile._IValue> _166_v = (_165_valueOrError2).Extract();
            return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.KVFromParts(_162_k, _164_colon, _166_v));
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
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Object(Cursors_Compile.Cursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _167_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Bracketed(cs, json);
      if ((_167_valueOrError0).IsFailure()) {
        return (_167_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _168_sp = (_167_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_168_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Open(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _169_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.OPEN);
      if ((_169_valueOrError0).IsFailure()) {
        return (_169_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _170_cs = (_169_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_170_cs).Split());
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Close(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _171_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE);
      if ((_171_valueOrError0).IsFailure()) {
        return (_171_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _172_cs = (_171_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_172_cs).Split());
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> BracketedFromParts(Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> close)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _173_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>.create(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _173_sp;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> AppendWithSuffix(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv> elem, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__> _174_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>.create_NonEmpty((sep).dtor_t));
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> _175_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>.FromElements(_174_suffixed)), (sep).dtor_cs);
      return _175_elems_k;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> AppendLast(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv> elem, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__> _176_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>.create_Empty());
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> _177_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>.FromElements(_176_suffixed)), (elem).dtor_cs);
      return _177_elems_k;
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Elements(Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _178_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_178_valueOrError0).IsFailure()) {
        return (_178_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile._Ijkv> _179_elem = (_178_valueOrError0).Extract();
        Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _180_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_179_elem).dtor_cs);
        short _181_s0 = (((_180_sep).dtor_t).dtor_t).Peek();
        if ((_181_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> _182_elems = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendWithSuffix(elems, _179_elem, _180_sep);
          Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _in16 = json;
          Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _in17 = open;
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> _in18 = _182_elems;
          json = _in16;
          open = _in17;
          elems = _in18;
          goto TAIL_CALL_START;
        } else if ((_181_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> _183_elems = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.AppendLast(elems, _179_elem, _180_sep);
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(open, _183_elems, _180_sep));
        } else {
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Failure(Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE, JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.SEPARATOR), _181_s0));
        }
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Bracketed(Cursors_Compile.Cursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _184_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>(cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Open));
      if ((_184_valueOrError0).IsFailure()) {
        return (_184_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _185_open = (_184_valueOrError0).Extract();
        Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>> _186_elems = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__>>.FromElements(), (_185_open).dtor_cs);
        if ((((_185_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mObjectParams_Compile.__default.CLOSE))) {
          Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _187_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>((_185_open).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Close));
          if ((_187_valueOrError1).IsFailure()) {
            return (_187_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _188_close = (_187_valueOrError1).Extract();
            return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.BracketedFromParts(_185_open, _186_elems, _188_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Elements(json, _185_open, _186_elems);
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
    public static Dafny.ISequence<byte> ElementSpec(JSON_mGrammar_Compile._IValue t) {
      return JSON_mSpec_Compile.__default.Value(t);
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Element(Cursors_Compile.Cursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      return Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>((json).dtor_fn)(cs);
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
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Array(Cursors_Compile.Cursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _189_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Bracketed(cs, json);
      if ((_189_valueOrError0).IsFailure()) {
        return (_189_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _190_sp = (_189_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_190_sp);
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Open(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _191_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.OPEN);
      if ((_191_valueOrError0).IsFailure()) {
        return (_191_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _192_cs = (_191_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_192_cs).Split());
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Close(Cursors_Compile.Cursor__ cs) {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _193_valueOrError0 = (cs).AssertByte<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE);
      if ((_193_valueOrError0).IsFailure()) {
        return (_193_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _194_cs = (_193_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_194_cs).Split());
      }
    }
    public static Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> BracketedFromParts(Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> close)
    {
      Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _195_sp = Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>.create(JSON_mGrammar_Compile.Bracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>.create((open).dtor_t, (elems).dtor_t, (close).dtor_t), (close).dtor_cs);
      return _195_sp;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> AppendWithSuffix(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile._IValue> elem, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__> _196_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>.create_NonEmpty((sep).dtor_t));
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> _197_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>.FromElements(_196_suffixed)), (sep).dtor_cs);
      return _197_elems_k;
    }
    public static Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> AppendLast(Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> elems, Cursors_Compile.Split<JSON_mGrammar_Compile._IValue> elem, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> sep)
    {
      JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__> _198_suffixed = JSON_mGrammar_Compile.Suffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>.create((elem).dtor_t, JSON_mGrammar_Compile.Maybe<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>.create_Empty());
      Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> _199_elems_k = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>.Concat((elems).dtor_t, Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>.FromElements(_198_suffixed)), (elem).dtor_cs);
      return _199_elems_k;
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Elements(Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json, Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> open, Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> elems)
    {
    TAIL_CALL_START: ;
      Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _200_valueOrError0 = JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.Element((elems).dtor_cs, json);
      if ((_200_valueOrError0).IsFailure()) {
        return (_200_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile._IValue> _201_elem = (_200_valueOrError0).Extract();
        Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _202_sep = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.TryStructural((_201_elem).dtor_cs);
        short _203_s0 = (((_202_sep).dtor_t).dtor_t).Peek();
        if ((_203_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> _204_elems = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendWithSuffix(elems, _201_elem, _202_sep);
          Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> _in19 = json;
          Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _in20 = open;
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> _in21 = _204_elems;
          json = _in19;
          open = _in20;
          elems = _in21;
          goto TAIL_CALL_START;
        } else if ((_203_s0) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> _205_elems = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.AppendLast(elems, _201_elem, _202_sep);
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(open, _205_elems, _202_sep));
        } else {
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Failure(Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_ExpectingAnyByte(Dafny.Sequence<byte>.FromElements(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE, JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.SEPARATOR), _203_s0));
        }
      }
    }
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Bracketed(Cursors_Compile.Cursor__ cs, Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> json)
    {
      Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _206_valueOrError0 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>(cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Open));
      if ((_206_valueOrError0).IsFailure()) {
        return (_206_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _207_open = (_206_valueOrError0).Extract();
        Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>> _208_elems = Cursors_Compile.Split<Dafny.ISequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>>.create(Dafny.Sequence<JSON_mGrammar_Compile._ISuffixed<JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__>>.FromElements(), (_207_open).dtor_cs);
        if ((((_207_open).dtor_cs).Peek()) == ((short)(JSON_mZeroCopy_mDeserializer_mArrayParams_Compile.__default.CLOSE))) {
          Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _209_valueOrError1 = JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<Views_mCore_Compile.View__>((_207_open).dtor_cs, Parsers_Compile.Parser__<Views_mCore_Compile.View__, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Close));
          if ((_209_valueOrError1).IsFailure()) {
            return (_209_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>>();
          } else {
            Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<Views_mCore_Compile.View__>> _210_close = (_209_valueOrError1).Extract();
            return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.BracketedFromParts(_207_open, _208_elems, _210_close));
          }
        } else {
          return JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Elements(json, _207_open, _208_elems);
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
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Constant(Cursors_Compile.Cursor__ cs, Dafny.ISequence<byte> expected)
    {
      Wrappers_Compile._IResult<Cursors_Compile.Cursor__, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _211_valueOrError0 = (cs).AssertBytes<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>(expected, 0U);
      if ((_211_valueOrError0).IsFailure()) {
        return (_211_valueOrError0).PropagateFailure<Cursors_Compile.Split<Views_mCore_Compile.View__>>();
      } else {
        Cursors_Compile.Cursor__ _212_cs = (_211_valueOrError0).Extract();
        return Wrappers_Compile.Result<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success((_212_cs).Split());
      }
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mConstants_Compile
namespace JSON_mZeroCopy_mDeserializer_mValues_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Value(Cursors_Compile.Cursor__ cs) {
      short _213_c = (cs).Peek();
      if ((_213_c) == ((short)('{'))) {
        Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _214_valueOrError0 = JSON_mZeroCopy_mDeserializer_mObjects_Compile.__default.Object(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_214_valueOrError0).IsFailure()) {
          return (_214_valueOrError0).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _let_tmp_rhs11 = (_214_valueOrError0).Extract();
          JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._Ijkv, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _215_obj = _let_tmp_rhs11.dtor_t;
          Cursors_Compile.Cursor__ _216_cs = _let_tmp_rhs11.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Object(_215_obj), _216_cs));
        }
      } else if ((_213_c) == ((short)('['))) {
        Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _217_valueOrError1 = JSON_mZeroCopy_mDeserializer_mArrays_Compile.__default.Array(cs, JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.ValueParser(cs));
        if ((_217_valueOrError1).IsFailure()) {
          return (_217_valueOrError1).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__>> _let_tmp_rhs12 = (_217_valueOrError1).Extract();
          JSON_mGrammar_Compile._IBracketed<Views_mCore_Compile.View__, JSON_mGrammar_Compile._IValue, Views_mCore_Compile.View__, Views_mCore_Compile.View__> _218_arr = _let_tmp_rhs12.dtor_t;
          Cursors_Compile.Cursor__ _219_cs = _let_tmp_rhs12.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Array(_218_arr), _219_cs));
        }
      } else if ((_213_c) == ((short)('\"'))) {
        Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _220_valueOrError2 = JSON_mZeroCopy_mDeserializer_mStrings_Compile.__default.String(cs);
        if ((_220_valueOrError2).IsFailure()) {
          return (_220_valueOrError2).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs13 = (_220_valueOrError2).Extract();
          Views_mCore_Compile.View__ _221_str = _let_tmp_rhs13.dtor_t;
          Cursors_Compile.Cursor__ _222_cs = _let_tmp_rhs13.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_String(_221_str), _222_cs));
        }
      } else if ((_213_c) == ((short)('t'))) {
        Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _223_valueOrError3 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.TRUE);
        if ((_223_valueOrError3).IsFailure()) {
          return (_223_valueOrError3).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs14 = (_223_valueOrError3).Extract();
          Views_mCore_Compile.View__ _224_cst = _let_tmp_rhs14.dtor_t;
          Cursors_Compile.Cursor__ _225_cs = _let_tmp_rhs14.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Bool(_224_cst), _225_cs));
        }
      } else if ((_213_c) == ((short)('f'))) {
        Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _226_valueOrError4 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.FALSE);
        if ((_226_valueOrError4).IsFailure()) {
          return (_226_valueOrError4).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs15 = (_226_valueOrError4).Extract();
          Views_mCore_Compile.View__ _227_cst = _let_tmp_rhs15.dtor_t;
          Cursors_Compile.Cursor__ _228_cs = _let_tmp_rhs15.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Bool(_227_cst), _228_cs));
        }
      } else if ((_213_c) == ((short)('n'))) {
        Wrappers_Compile._IResult<Cursors_Compile.Split<Views_mCore_Compile.View__>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _229_valueOrError5 = JSON_mZeroCopy_mDeserializer_mConstants_Compile.__default.Constant(cs, JSON_mGrammar_Compile.__default.NULL);
        if ((_229_valueOrError5).IsFailure()) {
          return (_229_valueOrError5).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile.Split<Views_mCore_Compile.View__> _let_tmp_rhs16 = (_229_valueOrError5).Extract();
          Views_mCore_Compile.View__ _230_cst = _let_tmp_rhs16.dtor_t;
          Cursors_Compile.Cursor__ _231_cs = _let_tmp_rhs16.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Null(_230_cst), _231_cs));
        }
      } else {
        Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _232_valueOrError6 = JSON_mZeroCopy_mDeserializer_mNumbers_Compile.__default.Number(cs);
        if ((_232_valueOrError6).IsFailure()) {
          return (_232_valueOrError6).PropagateFailure<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>>();
        } else {
          Cursors_Compile.Split<JSON_mGrammar_Compile._Ijnumber> _let_tmp_rhs17 = (_232_valueOrError6).Extract();
          JSON_mGrammar_Compile._Ijnumber _233_num = _let_tmp_rhs17.dtor_t;
          Cursors_Compile.Cursor__ _234_cs = _let_tmp_rhs17.dtor_cs;
          return Wrappers_Compile.Result<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>.create(JSON_mGrammar_Compile.Value.create_Number(_233_num), _234_cs));
        }
      }
    }
    public static Parsers_Compile._ISubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError> ValueParser(Cursors_Compile.Cursor__ cs) {
      Func<Cursors_Compile.Cursor__, bool> _235_pre = Dafny.Helpers.Id<Func<Cursors_Compile.Cursor__, Func<Cursors_Compile.Cursor__, bool>>>((_236_cs) => ((System.Func<Cursors_Compile.Cursor__, bool>)((_237_ps_k) => {
        return ((_237_ps_k).Length()) < ((_236_cs).Length());
      })))(cs);
      Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>> _238_fn = Dafny.Helpers.Id<Func<Func<Cursors_Compile.Cursor__, bool>, Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>>>((_239_pre) => ((System.Func<Cursors_Compile.Cursor__, Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>>)((_240_ps_k) => {
        return JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value(_240_ps_k);
      })))(_235_pre);
      return Parsers_Compile.SubParser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(_238_fn);
    }
  }
} // end of namespace JSON_mZeroCopy_mDeserializer_mValues_Compile
namespace JSON_mZeroCopy_mDeserializer_mAPI_Compile {

  public partial class __default {
    public static Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> JSON(Cursors_Compile.Cursor__ cs) {
      return JSON_mZeroCopy_mDeserializer_mCore_Compile.__default.Structural<JSON_mGrammar_Compile._IValue>(cs, Parsers_Compile.Parser__<JSON_mGrammar_Compile._IValue, JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create(JSON_mZeroCopy_mDeserializer_mValues_Compile.__default.Value));
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Text(Views_mCore_Compile.View__ v) {
      Wrappers_Compile._IResult<Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _241_valueOrError0 = JSON_mZeroCopy_mDeserializer_mAPI_Compile.__default.JSON(Cursors_Compile.Cursor__.OfView(v));
      if ((_241_valueOrError0).IsFailure()) {
        return (_241_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
      } else {
        Cursors_Compile.Split<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>> _let_tmp_rhs18 = (_241_valueOrError0).Extract();
        JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _242_text = _let_tmp_rhs18.dtor_t;
        Cursors_Compile.Cursor__ _243_cs = _let_tmp_rhs18.dtor_cs;
        Wrappers_Compile._IOutcome<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _244_valueOrError1 = Wrappers_Compile.__default.Need<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>((_243_cs).EOF_q, Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_ExpectingEOF()));
        if ((_244_valueOrError1).IsFailure()) {
          return (_244_valueOrError1).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
        } else {
          return Wrappers_Compile.Result<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>.create_Success(_242_text);
        }
      }
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> OfBytes(Dafny.ISequence<byte> bs) {
      Wrappers_Compile._IOutcome<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _245_valueOrError0 = Wrappers_Compile.__default.Need<Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>>((new BigInteger((bs).Count)) < (BoundedInts_Compile.__default.TWO__TO__THE__32), Cursors_Compile.CursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>.create_OtherError(JSON_mZeroCopy_mDeserializer_mCore_Compile.JSONError.create_IntOverflow()));
      if ((_245_valueOrError0).IsFailure()) {
        return (_245_valueOrError0).PropagateFailure<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>>();
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
    public static Dafny.ISequence<byte> Serialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js) {
      return (JSON_mZeroCopy_mSerializer_Compile.__default.Text(js)).Bytes();
    }
    public static Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> SerializeAlloc(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js)
    {
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> bs = Wrappers_Compile.Result<byte[], JSON_mZeroCopy_mSerializer_Compile._IError>.Default(new byte[0]);
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> _out3;
      _out3 = JSON_mZeroCopy_mSerializer_Compile.__default.Serialize(js);
      bs = _out3;
      return bs;
    }
    public static Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> SerializeBlit(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] bs)
    {
      Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> len = Wrappers_Compile.Result<uint, JSON_mZeroCopy_mSerializer_Compile._IError>.Default(0);
      Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _out4;
      _out4 = JSON_mZeroCopy_mSerializer_Compile.__default.SerializeTo(js, bs);
      len = _out4;
      return len;
    }
    public static Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> Deserialize(Dafny.ISequence<byte> bs) {
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
    public static void Serialize(Dafny.ISequence<byte> bytes)
    {
      uint _hi3 = Benchmarks.__default.WARMUP;
      for (uint _246_i = 0U; _246_i < _hi3; _246_i++) {
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _247___v0;
        _247___v0 = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(bytes);
      }
      Benchmarks.Interop.StartTimer();
      uint _hi4 = Benchmarks.__default.REPEATS;
      for (uint _248_i = 0U; _248_i < _hi4; _248_i++) {
        Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _249___v1;
        _249___v1 = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(bytes);
      }
      Benchmarks.Interop.ReportTimer(Dafny.Sequence<char>.FromString("Serialize"), new BigInteger((bytes).Count), Benchmarks.__default.REPEATS);
    }
    public static void Deserialize(JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> js, byte[] target)
    {
      uint _hi5 = Benchmarks.__default.WARMUP;
      for (uint _250_i = 0U; _250_i < _hi5; _250_i++) {
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _251___v2;
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _out5;
        _out5 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeBlit(js, target);
        _251___v2 = _out5;
      }
      Benchmarks.Interop.StartTimer();
      uint _hi6 = Benchmarks.__default.REPEATS;
      for (uint _252_i = 0U; _252_i < _hi6; _252_i++) {
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _253___v3;
        Wrappers_Compile._IResult<uint, JSON_mZeroCopy_mSerializer_Compile._IError> _out6;
        _out6 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeBlit(js, target);
        _253___v3 = _out6;
      }
      Benchmarks.Interop.ReportTimer(Dafny.Sequence<char>.FromString("Deserialize"), new BigInteger((target).Length), Benchmarks.__default.REPEATS);
    }
    public static void _Main()
    {
      byte[] _254_input__array;
      byte[] _out7;
      _out7 = Benchmarks.Interop.ReadInput();
      _254_input__array = _out7;
      byte[] _255_output__array;
      byte[] _nw1 = new byte[Dafny.Helpers.ToIntChecked(Dafny.Helpers.ToIntChecked(new BigInteger((_254_input__array).Length), "C# arrays may not be larger than the max 32-bit integer"),"C# array size must not be larger than max 32-bit int")];
      _255_output__array = _nw1;
      Dafny.ISequence<byte> _256_bytes;
      _256_bytes = Dafny.Helpers.SeqFromArray(_254_input__array);
      Wrappers_Compile._IResult<JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue>, Cursors_Compile._ICursorError<JSON_mZeroCopy_mDeserializer_mCore_Compile._IJSONError>> _257_jsr;
      _257_jsr = JSON_mZeroCopy_mAPI_Compile.__default.Deserialize(_256_bytes);
      if (!((_257_jsr).is_Success)) {
        throw new Dafny.HaltException("c:\\Users\\cpitcla\\git\\dafny\\libraries\\src\\JSON\\Benchmarks\\Benchmark.dfy(50,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      JSON_mGrammar_Compile._IStructural<JSON_mGrammar_Compile._IValue> _258_js;
      _258_js = (_257_jsr).dtor_value;
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> _259_output;
      Wrappers_Compile._IResult<byte[], JSON_mZeroCopy_mSerializer_Compile._IError> _out8;
      _out8 = JSON_mZeroCopy_mAPI_Compile.__default.SerializeAlloc(_258_js);
      _259_output = _out8;
      if (!((_259_output).is_Success)) {
        throw new Dafny.HaltException("c:\\Users\\cpitcla\\git\\dafny\\libraries\\src\\JSON\\Benchmarks\\Benchmark.dfy(54,4): " + Dafny.Sequence<char>.FromString("expectation violation"));
      }
      Benchmarks.__default.Serialize(_256_bytes);
      Benchmarks.__default.Deserialize(_258_js, _255_output__array);
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
