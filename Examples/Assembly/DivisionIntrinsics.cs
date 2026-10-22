using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;

namespace Examples;

public static class DivisionIntrinsics
{
    public static ulong And(ulong left, ulong right) => Avx2.And(Vector256.Create(left), Vector256.Create(right)).GetElement(0);
    public static ulong Or(ulong left, ulong right) => Avx2.Or(Vector256.Create(left), Vector256.Create(right)).GetElement(1);
    public static ulong Xor(ulong left, ulong right) => Avx2.Xor(Vector256.Create(left), Vector256.Create(right)).GetElement(2);
    public static ulong AndNot(ulong left, ulong right) => Avx2.AndNot(Vector256.Create(left), Vector256.Create(right)).GetElement(3);
    public static ulong ShiftLeft(ulong value, ulong count)
    {
        Vector128<ulong> local = Vector128.CreateScalarUnsafe(count);
        return Avx2.ShiftLeftLogical(Vector256.Create(value), local).GetElement(0);
    }
    public static ulong ShiftRight(ulong value, ulong count)
    {
        Vector128<ulong> local = Vector128.CreateScalarUnsafe(count);
        return Avx2.ShiftRightLogical(Vector256.Create(value), local).GetElement(3);
    }
    public static int Less(ulong left, ulong right)
    {
        Vector512<ulong> first = Vector512.Create(Vector256.Create(left), Vector256.Create(left));
        Vector512<ulong> second = Vector512.Create(Vector256.Create(right), Vector256.Create(right));
        return Avx512DQ.MoveMask(Avx512F.CompareLessThan(first, second));
    }
    public static int Greater(ulong left, ulong right)
    {
        Vector512<ulong> first = Vector512.Create(Vector256.Create(left), Vector256.Create(left));
        Vector512<ulong> second = Vector512.Create(Vector256.Create(right), Vector256.Create(right));
        return Avx512DQ.MoveMask(Avx512F.CompareGreaterThan(first, second));
    }
    public static ulong UnsafeLow(ulong value) => Vector128.CreateScalarUnsafe(value).GetElement(0);
    public static ulong UnsafeHigh(ulong value) => Vector128.CreateScalarUnsafe(value).GetElement(1);
    public static bool UnsafeEquals(ulong value) => Vector128.CreateScalarUnsafe(value) == Vector128.CreateScalarUnsafe(value);
    public static void Init128(ref Vector128<ulong> value) => value = default;
    public static void Init256(ref Vector256<ulong> value) => value = default;
    public static void Init512(ref Vector512<ulong> value) => value = default;
}
