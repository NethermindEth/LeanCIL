namespace Examples;

public struct GenericPair<T> where T : unmanaged
{
    public T First;
    public T Second;
    public GenericPair(T first, T second) { First = first; Second = second; }
    public T GetSecond() => Second;
    public void SetSecond(T value) => Second = value;
}

public struct GenericEnvelope<T> where T : unmanaged
{
    public byte Tag;
    public GenericPair<T> Pair;
    public GenericEnvelope(T first, T second) { Tag = 7; Pair = new(first, second); }
    public T Read() => Pair.Second;
}

public static class GenericLayouts
{
    public static int VectorSize() => System.Runtime.CompilerServices.Unsafe.SizeOf<
        GenericPair<System.Runtime.Intrinsics.Vector128<int>>>();
    public static int TupleSize() => System.Runtime.CompilerServices.Unsafe.SizeOf<GenericPair<(ulong, ulong)>>();

    public static ulong Roundtrip(ulong first, ulong second)
    {
        var pair = new GenericPair<ulong>(first, second);
        pair.SetSecond(first);
        return pair.GetSecond();
    }

    public static ulong Composed(ulong first, ulong second) =>
        new GenericEnvelope<ulong>(first, second).Read();

    public static ulong Field(ref GenericPair<ulong> pair) => pair.Second;
    public static GenericPair<ulong> Create(ulong first, ulong second) => new(first, second);
    public static GenericPair<GenericPair<uint>> Nested(uint first, uint second) =>
        new(new(first, second), new(second, first));
}
