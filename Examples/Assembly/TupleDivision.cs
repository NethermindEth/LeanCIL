// DivRem is marked experimental in .NET 10; the fixture pins its current signature.
#pragma warning disable SYSLIB5004
using System;
using System.Runtime.Intrinsics.X86;

namespace Examples;

public static class TupleDivision
{
    public static ulong Quotient(ulong lower, ulong upper, ulong divisor) => X86Base.X64.DivRem(lower, upper, divisor).Quotient;

    public static ulong Remainder(ulong lower, ulong upper, ulong divisor) => X86Base.X64.DivRem(lower, upper, divisor).Remainder;

    public static ulong Deconstruct(ulong lower, ulong upper, ulong divisor)
    {
        var (quotient, remainder) = X86Base.X64.DivRem(lower, upper, divisor);
        return quotient ^ remainder;
    }

    public static ulong Local(ulong lower, ulong upper, ulong divisor)
    {
        var result = X86Base.X64.DivRem(lower, upper, divisor);
        return Item1(in result) - result.Remainder;
    }

    public static (ulong Quotient, ulong Remainder) Pair(ulong lower, ulong upper, ulong divisor) =>
        X86Base.X64.DivRem(lower, upper, divisor);

    public static ulong WrongQuotient(ulong lower, ulong upper, ulong divisor) => X86Base.X64.DivRem(lower, upper, divisor).Remainder;

    static ulong Item1(in (ulong, ulong) pair) => pair.Item1;

    // Portable Math.DivRem overloads, returned whole so both tuple fields are observed.
    public static (sbyte Quotient, sbyte Remainder) MathSByte(sbyte left, sbyte right) => Math.DivRem(left, right);

    public static (byte Quotient, byte Remainder) MathByte(byte left, byte right) => Math.DivRem(left, right);

    public static (short Quotient, short Remainder) MathInt16(short left, short right) => Math.DivRem(left, right);

    public static (ushort Quotient, ushort Remainder) MathUInt16(ushort left, ushort right) => Math.DivRem(left, right);

    public static (int Quotient, int Remainder) MathInt32(int left, int right) => Math.DivRem(left, right);

    public static (uint Quotient, uint Remainder) MathUInt32(uint left, uint right) => Math.DivRem(left, right);

    public static (long Quotient, long Remainder) MathInt64(long left, long right) => Math.DivRem(left, right);

    public static (ulong Quotient, ulong Remainder) MathUInt64(ulong left, ulong right) => Math.DivRem(left, right);

    public static (nint Quotient, nint Remainder) MathIntPtr(nint left, nint right) => Math.DivRem(left, right);

    public static (nuint Quotient, nuint Remainder) MathUIntPtr(nuint left, nuint right) => Math.DivRem(left, right);

    public static sbyte MathSByteRemainder(sbyte left, sbyte right) => Math.DivRem(left, right).Remainder;

    public static int MathQuotient(int left, int right) => Math.DivRem(left, right).Quotient;

    public static int MathWrongQuotient(int left, int right) => Math.DivRem(left, right).Remainder;

    public static int MathOutInt32(int left, int right, out int remainder) =>
        Math.DivRem(left, right, out remainder);

    public static long MathOutInt64(long left, long right, out long remainder) =>
        Math.DivRem(left, right, out remainder);
}
