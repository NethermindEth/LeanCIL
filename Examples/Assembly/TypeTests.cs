using System.Runtime.CompilerServices;

namespace Examples;

public struct TypeMarker;

public struct OtherMarker;

public static class TypeTests
{
    // The last branch calls an unmodelled API; it is reachable only when T is ulong.
    [MethodImpl(MethodImplOptions.NoInlining)]
    public static int Classify<T>(int value) where T : struct
    {
        if (typeof(T) == typeof(TypeMarker)) return value + 1;
        if (typeof(T) != typeof(ulong)) return value + 2;
        return System.Environment.ProcessorCount;
    }

    public static int Marker(int value) => Classify<TypeMarker>(value);
    public static int Other(int value) => Classify<OtherMarker>(value);
    public static int Word(int value) => Classify<ulong>(value);

    [MethodImpl(MethodImplOptions.NoInlining)]
    public static int ReferenceClassify<T>(int value) where T : struct
    {
        bool same = ReferenceEquals(typeof(T), typeof(TypeMarker));
        if (ReferenceEquals(typeof(T), typeof(TypeMarker))) return value + (same ? 4 : 0) + 1;
        if (!ReferenceEquals(typeof(T), typeof(ulong))) return value + (same ? 4 : 0) + 2;
        return value + (same ? 4 : 0) + 3;
    }

    public static int ReferenceCases(int value) => ReferenceClassify<TypeMarker>(value) +
        ReferenceClassify<OtherMarker>(value) + ReferenceClassify<ulong>(value);
}
