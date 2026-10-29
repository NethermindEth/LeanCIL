using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Examples;

internal static class UnsafeReferences
{
    public static unsafe ref ulong Pointer(byte* source) => ref Unsafe.AsRef<ulong>(source);
    public static unsafe byte* AddPointer(byte* source, int offset) => (byte*)Unsafe.Add<ulong>(source, offset);
    public static unsafe byte* AddPointerAggregate(byte* source, int offset) =>
        (byte*)Unsafe.Add<FourLimbs>(source, offset);
    public static unsafe byte* SubtractPointer(byte* source, int offset) =>
        (byte*)Unsafe.Subtract<ulong>(source, offset);
    public static unsafe byte* SubtractPointerAggregate(byte* source, int offset) =>
        (byte*)Unsafe.Subtract<FourLimbs>(source, offset);
    public static ref ulong Word(ref FourLimbs value) => ref Unsafe.As<FourLimbs, ulong>(ref value);
    public static ref Vector128<ulong> Half(ref FourLimbs value) => ref Unsafe.As<FourLimbs, Vector128<ulong>>(ref value);
    public static Vector128<ulong> ReadHalf(ref FourLimbs value) => Unsafe.As<FourLimbs, Vector128<ulong>>(ref value);
    public static ref Vector256<uint> Vector(ref FourLimbs value) => ref Unsafe.As<FourLimbs, Vector256<uint>>(ref value);
    public static ref FourLimbs Mutable(in FourLimbs value) => ref Unsafe.AsRef(in value);

    public static ulong Store(ref FourLimbs value, ulong a, ulong b, ulong c, ulong d)
    {
        ref ulong first = ref Unsafe.As<FourLimbs, ulong>(ref value);
        first = a;
        Unsafe.Add(ref first, 1) = b;
        Unsafe.Add(ref first, 2) = c;
        Unsafe.Add(ref first, 3) = d;
        return Unsafe.Add(ref first, 3);
    }

    public static ulong PastEnd(ref FourLimbs value) => Unsafe.Add(ref Unsafe.As<FourLimbs, ulong>(ref value), 4);
    public static ulong Read(ref FourLimbs value) => Unsafe.As<FourLimbs, ulong>(ref value);
    public static bool AreSame(ref byte origin, ref byte target) => Unsafe.AreSame(ref origin, ref target);
    public static bool Less(ref byte origin, ref byte target) => Unsafe.IsAddressLessThan(ref origin, ref target);
    public static bool Greater(ref byte origin, ref byte target) => Unsafe.IsAddressGreaterThan(ref origin, ref target);
    public static nint ByteOffset(ref byte origin, ref byte target) => Unsafe.ByteOffset(ref origin, ref target);
    public static ref byte AddSigned(ref byte origin, nint offset) => ref Unsafe.AddByteOffset(ref origin, offset);
    public static ref byte AddUnsigned(ref byte origin, nuint offset) => ref Unsafe.AddByteOffset(ref origin, offset);
    public static ref byte Subtract(ref byte origin, nint offset) => ref Unsafe.SubtractByteOffset(ref origin, offset);
    public static ref byte SubtractUnsigned(ref byte origin, nuint offset) =>
        ref Unsafe.SubtractByteOffset(ref origin, offset);
    public static ref ulong SubtractElements32(ref ulong origin, int offset) => ref Unsafe.Subtract(ref origin, offset);
    public static ref ulong SubtractElementsNative(ref ulong origin, nint offset) =>
        ref Unsafe.Subtract(ref origin, offset);
    public static ref ulong SubtractElementsUnsigned(ref ulong origin, nuint offset) =>
        ref Unsafe.Subtract(ref origin, offset);
    public static ref FourLimbs SubtractAggregate(ref FourLimbs origin, nint offset) =>
        ref Unsafe.Subtract(ref origin, offset);
    public static ref Vector128<ulong> SubtractVector(ref Vector128<ulong> origin, nuint offset) =>
        ref Unsafe.Subtract(ref origin, offset);
}
