using System;
using System.Runtime.CompilerServices;

namespace Examples;

public static class StackAllocation
{
    public static int Length(int length)
    {
        Span<int> buffer = stackalloc int[length];
        return buffer.Length;
    }

    public static int FillAndRead(int length, int value)
    {
        Span<int> buffer = stackalloc int[length];
        for (var index = 0; index < buffer.Length; index++) buffer[index] = value;
        return buffer[length - 1];
    }

    public static unsafe int ZeroInitialized()
    {
        var buffer = stackalloc int[2];
        return buffer[1];
    }

    [SkipLocalsInit]
    public static unsafe int WrittenBeforeRead(int value)
    {
        var buffer = stackalloc int[2];
        buffer[1] = value;
        return buffer[1];
    }

    [SkipLocalsInit]
    public static unsafe int UninitializedRead()
    {
        var buffer = stackalloc int[2];
        return buffer[1];
    }

    public static unsafe int* EscapingStorage()
    {
        var buffer = stackalloc int[2];
        return buffer;
    }
}
