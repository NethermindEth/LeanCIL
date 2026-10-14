using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

[StructLayout(LayoutKind.Explicit, Size = 16)]
public struct NativePair
{
    [FieldOffset(0)] public nint Signed;
    [FieldOffset(8)] public nuint Unsigned;
}

public static class NativeIntegers
{
    public static nint Add(nint x, nint y) => x + y;
    public static nuint AddUnsigned(nuint x, nuint y) => x + y;
    public static nint CheckedAdd(nint x, nint y) => checked(x + y);
    public static nuint CheckedAddUnsigned(nuint x, nuint y) => checked(x + y);
    public static nint Divide(nint x, nint y) => x / y;
    public static nuint DivideUnsigned(nuint x, nuint y) => x / y;
    public static nint Widen(int x) => x;
    public static nuint WidenUnsigned(uint x) => x;
    public static int Narrow(nint x) => checked((int)x);
    public static uint NarrowUnsigned(nuint x) => checked((uint)x);
    public static nint ReadWrite(ref nint target, nint value) => target = value;
    public static nuint ReadWriteUnsigned(ref nuint target, nuint value) => target = value;

    [MethodImpl(MethodImplOptions.NoInlining)]
    static nint Increment(ref nint value) => ++value;

    public static nint LocalCall(nint value)
    {
        var local = value;
        return Increment(ref local);
    }

    public static nint Fields(ref NativePair pair, nint signed, nuint unsigned)
    {
        pair.Signed = signed;
        pair.Unsigned = unsigned;
        return pair.Signed + (nint)pair.Unsigned;
    }

    public static nint Choose(nint value) => value < 0 ? -value : value;
    public static nuint Shift(nuint value, int count) => value >> count;
    public static unsafe int SignedSize() => sizeof(nint);
    public static unsafe int UnsignedSize() => sizeof(nuint);
}
