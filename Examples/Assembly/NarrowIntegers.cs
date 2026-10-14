using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

[StructLayout(LayoutKind.Explicit, Size = 8)]
internal struct NarrowPacket
{
    [FieldOffset(0)] public sbyte SignedByte;
    [FieldOffset(2)] public short SignedShort;
    [FieldOffset(4)] public ushort UnsignedShort;
    [FieldOffset(6)] public char Character;
}

internal static class NarrowIntegers
{
    public static int SignedByte(int value) => unchecked((sbyte)value);
    public static int SignedShort(long value) => unchecked((short)value);
    public static int UnsignedShort(int value) => unchecked((ushort)value);
    public static char Character(int value) => unchecked((char)value);

    [MethodImpl(MethodImplOptions.NoInlining)]
    static short Identity(short value) => value;

    public static int Call(int value) => Identity(unchecked((short)value));

    public static int Fields(int value)
    {
        var packet = default(NarrowPacket);
        packet.SignedByte = unchecked((sbyte)value);
        packet.SignedShort = unchecked((short)value);
        packet.UnsignedShort = unchecked((ushort)value);
        packet.Character = unchecked((char)value);
        return packet.SignedByte + packet.SignedShort + packet.UnsignedShort + packet.Character;
    }
}
