using System.Runtime.CompilerServices;

namespace Examples;

internal static class Arguments
{
    public static uint Overwrite(uint value, uint replacement)
    {
        value = replacement;
        return value;
    }

    public static uint Alias(uint value)
    {
        ref var alias = ref value;
        value = unchecked(value + 1);
        return alias;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static uint Address(uint value)
    {
        Increment(ref value);
        return value;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    static void Increment(ref uint value) => value = unchecked(value + 1);

    public static uint CallerIsolation(uint value)
    {
        Address(value);
        return value;
    }

    public static nint Native(nint value)
    {
        ref var alias = ref value;
        value = unchecked(value + 1);
        return alias;
    }

    public static byte Narrow(byte value)
    {
        ref var alias = ref value;
        value = unchecked((byte)(value + 1));
        return alias;
    }

    public static uint ReassignReference(ref uint first, ref uint second)
    {
        first = ref second;
        first = 17;
        return second;
    }

    public static ulong Struct(Packet value)
    {
        ref var alias = ref value;
        value.Payload = 23;
        return alias.Payload;
    }
}
