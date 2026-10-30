using System;
using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

public static class ViewAccessors
{
    public static bool Empty(Span<int> values) => values.IsEmpty;
    public static bool ReadOnlyEmpty(ReadOnlySpan<int> values) => values.IsEmpty;
    public static bool PinnableNull(Span<int> values) => Unsafe.IsNullRef(ref values.GetPinnableReference());
    public static bool ReadOnlyPinnableNull(ReadOnlySpan<int> values) =>
        Unsafe.IsNullRef(in values.GetPinnableReference());
    public static bool ReferenceNull(Span<int> values) => Unsafe.IsNullRef(ref MemoryMarshal.GetReference(values));
    public static ref int ArrayData(int[] values) => ref MemoryMarshal.GetArrayDataReference(values);
}
