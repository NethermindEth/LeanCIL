using System.Runtime.CompilerServices;

namespace Examples;

public static class Blocks
{
    public static void Fill(ref byte destination, byte value, uint count) =>
        Unsafe.InitBlockUnaligned(ref destination, value, count);

    public static void Copy(ref byte destination, ref byte source, uint count) =>
        Unsafe.CopyBlockUnaligned(ref destination, ref source, count);

    public static void FillAligned(ref byte destination, byte value, uint count) =>
        Unsafe.InitBlock(ref destination, value, count);

    public static void CopyAligned(ref byte destination, ref byte source, uint count) =>
        Unsafe.CopyBlock(ref destination, ref source, count);
}
