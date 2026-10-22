// DivRem is marked experimental in .NET 10; the fixture pins its current signature.
#pragma warning disable SYSLIB5004
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
}
