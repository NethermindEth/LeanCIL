using System.Runtime.Intrinsics;

namespace Examples;

public static unsafe class IndirectValues
{
    public struct Pair { public ulong First; public ulong Second; }
    public struct Box<T> where T : unmanaged { public T Value; }

    public static Pair Record(Pair value) => ((delegate* managed<Pair, Pair>)&Identity<Pair>)(value);
    public static Box<Pair> Generic(Box<Pair> value) =>
        ((delegate* managed<Box<Pair>, Box<Pair>>)&Identity<Box<Pair>>)(value);
    public static Vector128<ulong> Vector(Vector128<ulong> value) =>
        ((delegate* managed<Vector128<ulong>, Vector128<ulong>>)&Identity<Vector128<ulong>>)(value);
    public static Pair Reference(ref Pair value) => ((delegate* managed<ref Pair, Pair>)&Read)(ref value);

    private static T Identity<T>(T value) where T : unmanaged => value;
    private static Pair Read(ref Pair value) => value;
}
