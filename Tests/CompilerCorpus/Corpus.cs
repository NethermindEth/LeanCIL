using System;
using System.Reflection;
using System.Runtime.CompilerServices;
using System.Runtime.Versioning;

[assembly: AssemblyVersion("1.0.0.0")]
[assembly: AssemblyConfiguration("Release")]
[assembly: TargetFramework(".NETCoreApp,Version=v10.0")]

public static class Corpus
{
    public static int TypeTest(int value) => TypeIdentity<int>(value);
    private static int TypeIdentity<T>(int value) => typeof(T) == typeof(int) ? value : -1;
    public static int Throw(int value) => value == 0 ? throw new ArgumentException("zero") : value;
    public static int NullInner(int value) => value == 0
        ? throw new InvalidOperationException("zero", null) : value;
    public static int SpanLocal(ref int value)
    {
        Span<int> view = new(ref value);
        return view[0];
    }
    public static int SpanSlice(Span<int> values, int offset) => values.Slice(offset)[0];
    public static unsafe int PointerRead(int* source) => Unsafe.ReadUnaligned<int>(source);
    public static int[] Allocate(int length) => new int[length];
    public static int Unsupported(int length) => new double[length].Length;
}
