using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

[StructLayout(LayoutKind.Explicit, Size = 12)]
internal struct Packet
{
    [FieldOffset(0)] public ulong Payload;
    [FieldOffset(8)] public uint Tag;
}

[StructLayout(LayoutKind.Explicit, Size = 40)]
internal struct LargePacket
{
    [FieldOffset(0)] public ulong Payload;
    [FieldOffset(32)] public uint Tag;
}

internal static class Arithmetic
{
    public static ulong Add(ulong x, ulong y) => unchecked(x + y);
    public static ulong WrongAdd(ulong x, ulong y) => unchecked(x - y);
    public static ulong Choose(bool flag, ulong x, ulong y) => flag ? x : y;
    [MethodImpl(MethodImplOptions.NoInlining)]
    private static ulong Increment(ulong x) => unchecked(x + 1);
    public static ulong Calls(ulong x)
    {
        ulong local = Increment(x);
        Mutate(ref local);
        return local;
    }
    private static void Mutate(ref ulong value) => value = unchecked(value + 2);
    public static ulong Alias(ref ulong x, ref ulong y)
    {
        x = 7;
        y = 9;
        return x;
    }
    public static ulong Struct(ulong x)
    {
        Packet packet = default;
        packet.Payload = x;
        packet.Tag = 3;
        return Read(ref packet);
    }
    private static ulong Read(ref Packet packet) => packet.Payload;
    private static ulong ReadValue(Packet packet) => packet.Payload;
    public static ulong StructCopy(ulong x)
    {
        Packet packet = default;
        packet.Payload = x;
        packet.Tag = 5;
        return ReadValue(packet);
    }
    public static ulong LargeStruct(ulong x)
    {
        LargePacket packet = default;
        packet.Payload = x;
        packet.Tag = 7;
        return ReadLarge(ref packet);
    }
    private static ulong ReadLarge(ref LargePacket packet) => packet.Payload;
    public static ulong PastEnd(ref ulong x) => Unsafe.Add(ref x, 1);
    public static ref ulong Escape()
    {
        ulong local = 1;
        return ref Unsafe.AsRef(in local);
    }
    public static int Unsupported(int x) => x / 2;
}
