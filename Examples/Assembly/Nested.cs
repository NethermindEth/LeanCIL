using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

public struct Leaf
{
    public byte Tag;
    public ulong Value;
}

[StructLayout(LayoutKind.Sequential, Pack = 1)]
public struct PackedLeaf
{
    public byte Tag;
    public uint Value;
}

public struct NestedRecord
{
    public byte Header;
    public Leaf Inner;
    public ushort Tail;
}

[StructLayout(LayoutKind.Sequential, Pack = 1)]
public struct PackedNestedRecord
{
    public byte Header;
    public PackedLeaf Inner;
    public ulong Tail;
}

[StructLayout(LayoutKind.Sequential, Size = 17)]
public struct SizedLeaf
{
    public byte Tag;
    public ulong Value;
}

public struct SizedNestedRecord
{
    public byte Header;
    public SizedLeaf Inner;
    public byte Tail;
}

[StructLayout(LayoutKind.Explicit, Size = 40)]
public struct ExplicitNestedRecord
{
    [FieldOffset(0)] public PackedLeaf Packed;
    [FieldOffset(8)] public Leaf Inner;
}

public static class Nested
{
    public static Leaf Extract(NestedRecord value) => value.Inner;
    public static Leaf WrongExtract(NestedRecord value) => default;

    public static ulong Snapshot(ulong value)
    {
        NestedRecord record = default;
        record.Inner.Value = value;
        var snapshot = record.Inner;
        record.Inner.Value = 0;
        return Read(snapshot);
    }

    public static ulong Copy(ulong value)
    {
        NestedRecord source = default;
        source.Inner.Value = value;
        NestedRecord destination = default;
        destination.Inner = source.Inner;
        source.Inner.Value = 0;
        return destination.Inner.Value;
    }

    public static ulong WrongCopy(ulong value)
    {
        NestedRecord source = default;
        source.Inner.Value = value;
        NestedRecord destination = default;
        source.Inner = destination.Inner;
        return destination.Inner.Value;
    }

    public static ulong Alias(ulong value)
    {
        NestedRecord record = default;
        ref var inner = ref record.Inner;
        inner.Value = value;
        return record.Inner.Value;
    }

    public static ulong Pass(ulong value)
    {
        NestedRecord record = default;
        record.Inner.Value = value;
        return ReadOuter(record);
    }

    public static uint Packed(uint value)
    {
        PackedNestedRecord record = default;
        record.Inner.Value = value;
        var copy = record.Inner;
        return copy.Value;
    }

    public static ulong Explicit(ulong value)
    {
        ExplicitNestedRecord record = default;
        record.Inner.Value = value;
        return Read(record.Inner);
    }

    public static ulong Sized(ulong value)
    {
        SizedNestedRecord record = default;
        record.Inner.Value = value;
        return record.Inner.Value;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static ulong Read(Leaf value) => value.Value;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static ulong ReadOuter(NestedRecord value) => value.Inner.Value;
}
