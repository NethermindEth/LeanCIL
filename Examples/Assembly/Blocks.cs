using System.Runtime.CompilerServices;

namespace Examples;

public static class Blocks
{
    public static unsafe void FillPointer(byte* destination, byte value, uint count) =>
        Unsafe.InitBlockUnaligned(destination, value, count);

    public static unsafe void CopyPointer(byte* destination, byte* source, uint count) =>
        Unsafe.CopyBlockUnaligned(destination, source, count);

    public static unsafe void FillPointerAligned(byte* destination, byte value, uint count) =>
        Unsafe.InitBlock(destination, value, count);

    public static unsafe void CopyPointerAligned(byte* destination, byte* source, uint count) =>
        Unsafe.CopyBlock(destination, source, count);

    public static void Fill(ref byte destination, byte value, uint count) =>
        Unsafe.InitBlockUnaligned(ref destination, value, count);

    public static void Copy(ref byte destination, ref byte source, uint count) =>
        Unsafe.CopyBlockUnaligned(ref destination, ref source, count);

    public static void FillAligned(ref byte destination, byte value, uint count) =>
        Unsafe.InitBlock(ref destination, value, count);

    public static void CopyAligned(ref byte destination, ref byte source, uint count) =>
        Unsafe.CopyBlock(ref destination, ref source, count);
    public static ulong FillLocal(byte value, uint count)
    {
        ulong destination = 0;
        Unsafe.InitBlock(ref Unsafe.As<ulong, byte>(ref destination), value, count);
        return destination;
    }

    public static ulong FillParameter(ulong destination, byte value, uint count)
    {
        Unsafe.InitBlock(ref Unsafe.As<ulong, byte>(ref destination), value, count);
        return destination;
    }

    public static ulong CopyLocal(ulong source, uint count)
    {
        ulong destination = 0;
        Unsafe.CopyBlock(ref Unsafe.As<ulong, byte>(ref destination),
            ref Unsafe.As<ulong, byte>(ref source), count);
        return destination;
    }

    public static ulong CopyParameter(ulong destination, ulong source, uint count)
    {
        Unsafe.CopyBlock(ref Unsafe.As<ulong, byte>(ref destination),
            ref Unsafe.As<ulong, byte>(ref source), count);
        return destination;
    }
}
