using System;
using System.Runtime.InteropServices;

namespace Examples;

public static class MemorySpans
{
    public static Span<int> ArrayWritable(int[] values) => values;

    public static ReadOnlySpan<int> ArrayReadOnly(int[] values) => values;

    public static Span<char> ArrayConstructor(char[] values) => new(values);

    public static ReadOnlySpan<int> ArrayRange(int[] values, int start, int length) => new(values, start, length);

    public static Span<bool> ArrayAsSpan(bool[] values) => values.AsSpan();

    public static Span<nint> ArrayAsSpanStart(nint[] values, int start) => values.AsSpan(start);

    public static Span<nuint> ArrayAsSpanRange(nuint[] values, int start, int length) => values.AsSpan(start, length);

    public static int ArraySliceWrite(int[] values, int start, int length, int value)
    {
        var slice = values.AsSpan(start, length);
        Write(slice, 0, value);
        return values[start];
    }

    public static nint NativeRead(ReadOnlySpan<nint> values, int index) => values[index];

    public static nuint NativeWrite(Span<nuint> values, int index, nuint value)
    {
        values[index] = value;
        return values[index];
    }

    public static char CharacterWrite(Span<char> values, int index, char value)
    {
        var slice = values.Slice(index, 1);
        slice[0] = value;
        return slice[0];
    }

    public static bool BooleanWrite(Span<bool> values, int index, bool value)
    {
        values[index] = value;
        return values[index];
    }

    public static int ByRefSpan(ref Span<int> values) => values.Length;

    public static int FloatingSpan(ReadOnlySpan<double> values) => values.Length;

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
