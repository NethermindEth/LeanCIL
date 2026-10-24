using System;
using System.Runtime.InteropServices;

namespace Examples;

public static class MemorySpans
{
    public static int Read(ReadOnlySpan<int> values, int index) => values[index];

    public static int SliceRead(ReadOnlySpan<int> values, int start, int length, int index)
    {
        var slice = values.Slice(start, length);
        var result = Read(slice, index);
        return result + slice.Length;
    }

    public static void Write(Span<int> values, int index, int value) => values[index] = value;

    public static int SliceWrite(Span<int> values, int start, int length, int index, int value)
    {
        var slice = values.Slice(start, length);
        Write(slice, index, value);
        return Read(slice, index);
    }

    public static int Existing(ref int first, int length, int index)
    {
        var values = MemoryMarshal.CreateSpan(ref first, length);
        return Read(values, index);
    }
}
