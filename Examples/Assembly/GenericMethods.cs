using System.Runtime.CompilerServices;
using System.Runtime.Intrinsics;

namespace Examples;

public static class GenericMethods
{
    [MethodImpl(MethodImplOptions.NoInlining)]
    public static T Identity<T>(T value) => value;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static T Read<T>(ref T value) where T : unmanaged => value;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static void Swap<T>(ref T left, ref T right) where T : unmanaged
    {
        var temporary = left;
        left = right;
        right = temporary;
    }

    public static int Identity32(int value) => Identity(value);
    public static ulong Identity64(ulong value) => Identity(value);
    public static int Read32(ref int value) => Read(ref value);
    public static void Swap32(ref int left, ref int right) => Swap(ref left, ref right);
    public static void SwapRecord(ref PackedLeaf left, ref PackedLeaf right) => Swap(ref left, ref right);

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static T Forward<T>(T value) => Identity(value);

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static T Choose<T>(bool first, T left, T right) => first ? left : right;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static int Size<T>() where T : unmanaged => Unsafe.SizeOf<T>();

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static void Clear<T>(ref T value) where T : unmanaged => value = default;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static ref T Next<T>(ref T value, int offset) where T : unmanaged => ref Unsafe.Add(ref value, offset);

    public static ulong Nested(ulong value) => Forward(value);
    public static ulong Repeated(ulong value) => Identity(Identity(value));
    public static int Mixed(int left, byte right) => Identity(left) + Identity(right);
    public static ulong Select(bool first, ulong left, ulong right) => Choose(first, left, right);
    public static int PackedSize() => Size<PackedLeaf>();
    public static int VectorSize() => Size<Vector128<ulong>>();
    public static Signed8 EnumIdentity(Signed8 value) => Identity(value);
    public static nint NativeIdentity(nint value) => Identity(value);

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static T First<T, U>(T first, U second) => first;

    public static ulong TwoTypes(ulong first, uint second) => First(first, second);

    public static uint SwapPacked(uint left, uint right)
    {
        var x = new PackedLeaf { Tag = 1, Value = left };
        var y = new PackedLeaf { Tag = 2, Value = right };
        Swap(ref x, ref y);
        return x.Value;
    }

    public static uint ClearPacked(uint value)
    {
        var x = new PackedLeaf { Tag = 1, Value = value };
        Clear(ref x);
        return x.Value;
    }

    public static ref PackedLeaf NextPacked(ref PackedLeaf value, int offset) => ref Next(ref value, offset);
    public static ulong Instance(ulong value)
    {
        var instance = new GenericPicker();
        return instance.Pick(value);
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static T Recursive<T>(T value) => Recursive(value);

    public static int RejectRecursion(int value) => Recursive(value);
    public static int WrongIdentity(int value) => Identity(value) + 1;
}

public struct GenericPicker
{
    [MethodImpl(MethodImplOptions.NoInlining)]
    public T Pick<T>(T value) => value;
}
