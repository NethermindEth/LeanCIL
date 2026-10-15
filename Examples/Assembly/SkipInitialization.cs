using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

[StructLayout(LayoutKind.Sequential)]
struct FourLimbs
{
    public ulong A, B, C, D;
}

static class SkipInitialization
{
    public static void Skip(out FourLimbs value) => Unsafe.SkipInit(out value);

    public static void Store(out FourLimbs value, ulong a, ulong b, ulong c, ulong d)
    {
        Unsafe.SkipInit(out value);
        value.A = a;
        value.B = b;
        value.C = c;
        value.D = d;
    }

    public static ulong Read(out ulong value)
    {
        Unsafe.SkipInit(out value);
        return value;
    }
}
