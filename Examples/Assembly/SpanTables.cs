using System;
using System.Runtime.InteropServices;

namespace Examples;

public static class SpanTables
{
    // Non-byte primitive tables compile to `ldtoken <field>; RuntimeHelpers.CreateSpan<T>`.
    private static ReadOnlySpan<uint> Words => [0x07FD, 0x07F5, 0x07ED, 0x07E5, 0x07DD, 0x07D5, 0x07CE, 0x07C6];
    private static ReadOnlySpan<ulong> Powers => [1, 10, 100, 1000];

    public static uint Word(int index) => Words[index];
    public static ulong Power(int index) => Powers[index];
    public static int Count() => Words.Length;
    public static ulong First() => MemoryMarshal.GetReference(Powers);
}
