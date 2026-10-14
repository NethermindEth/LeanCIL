using System.Runtime.CompilerServices;
using System.Runtime.InteropServices;

namespace Examples;

[StructLayout(LayoutKind.Sequential, Pack = 1)]
public struct PackedConstructor
{
    public byte Tag;
    public ushort Code;
    public ulong Value;

    public PackedConstructor(ulong value) : this(value, 3) { }

    public PackedConstructor(ulong value, byte tag)
    {
        Tag = tag;
        Code = 7;
        Value = value;
    }

    public readonly ulong Sum() => Value + Tag + Code;
}

public struct ConstructorLeaf
{
    public uint Value;
    public ConstructorLeaf(uint value) => Value = value;
}

public struct NestedConstructor
{
    public byte Tag;
    public ConstructorLeaf Inner;
    public ulong Value;

    public NestedConstructor(ulong value)
    {
        Tag = 5;
        Inner = new ConstructorLeaf((uint)value);
        Value = value;
    }

    public readonly ulong Sum() => Value + Inner.Value + Tag;
}

public struct DefaultConstructor
{
    public ulong Value;
    public DefaultConstructor() => Value = 23;
}

public struct CheckedConstructor
{
    public ulong Value;
    public CheckedConstructor(ulong value) => Value = checked(value + 1);
}

public static class Constructors
{
    [MethodImpl(MethodImplOptions.NoInlining)]
    public static Counter Return(ulong value) => new Counter(value);

    public static Counter WrongReturn(ulong value) => new Counter(value + 1);

    public static ulong Read(ulong value) => Return(value).Read();

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static PackedConstructor MakePacked(ulong value) => new PackedConstructor(value);

    public static ulong Packed(ulong value) => MakePacked(value).Sum();

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static NestedConstructor MakeNested(ulong value) => new NestedConstructor(value);

    public static ulong Nested(ulong value) => MakeNested(value).Sum();

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static DefaultConstructor MakeDefault() => new DefaultConstructor();

    public static ulong Default() => MakeDefault().Value;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static CheckedConstructor MakeChecked(ulong value) => new CheckedConstructor(value);

    public static ulong Checked(ulong value) => MakeChecked(value).Value;
}
