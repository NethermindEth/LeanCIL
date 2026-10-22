using System.Runtime.CompilerServices;

namespace Examples;

static class NullReferences
{
    public static bool IsNull() => Unsafe.IsNullRef(ref Unsafe.NullRef<ulong>());
    public static bool IsLive(ref ulong value) => Unsafe.IsNullRef(ref value);
    public static ulong Read() => Unsafe.NullRef<ulong>();
    public static void Write(ulong value) => Unsafe.NullRef<ulong>() = value;
    public static ulong ReadField() => Unsafe.NullRef<FourLimbs>().A;
    public static void WriteField(ulong value) => Unsafe.NullRef<FourLimbs>().A = value;

    // An optional reference that is either unset or bound to a live argument.
    public static ulong Optional(in FourLimbs value, bool present)
    {
        scoped ref readonly FourLimbs selected = ref Unsafe.NullRef<FourLimbs>();
        if (present) selected = ref value;
        return Unsafe.IsNullRef(in selected) ? 0 : selected.A;
    }

    // Reads through the reference even when it is unset.
    public static ulong Unchecked(in FourLimbs value, bool present)
    {
        scoped ref readonly FourLimbs selected = ref Unsafe.NullRef<FourLimbs>();
        if (present) selected = ref value;
        return selected.A;
    }
}
