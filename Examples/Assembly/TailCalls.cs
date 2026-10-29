using System;

namespace Examples;

public static class TailCalls
{
    public static int Forward(int value) => Increment(value);
    public static int ForwardReference(ref int value) => Read(ref value);
    public static void ForwardVoid(ref int value) => Store(ref value);
    public static int ForwardThrow(int value) => Raise(value);
    public static int Excluded(int value)
    {
        if (System.Runtime.Intrinsics.X86.Avx2.IsSupported) return Increment(value);
        return value;
    }

    public static int LocalReference(int value)
    {
        var local = value;
        return Ignore(ref local);
    }

    static int Increment(int value) => value + 1;
    static int Read(ref int value) => value;
    static void Store(ref int value) => value = 7;
    static int Ignore(ref int value) => 42;
    static int Raise(int value) => throw new InvalidOperationException();
}
