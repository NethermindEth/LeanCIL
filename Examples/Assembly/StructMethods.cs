using System.Runtime.CompilerServices;

namespace Examples;

public struct Counter
{
    public ulong Value;

    public Counter(ulong value) => Value = value;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public readonly ulong Read() => Value;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public void Set(ulong value) => Value = value;

    public ulong WriteRead(ulong value)
    {
        Value = value;
        return Value;
    }

    public ulong WrongWriteRead(ulong value)
    {
        Value = value + 1;
        return Value;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public ulong Add(ulong value)
    {
        Value += value;
        return Value;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    public readonly ulong Mix(ulong a, uint b, ushort c, byte d) => Value + a + b + c + d;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public void Replace(Counter other) => this = other;

    [MethodImpl(MethodImplOptions.NoInlining)]
    public byte Parameter(byte value)
    {
        value++;
        Increment(ref value);
        Value = value;
        return value;
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    static void Increment(ref byte value) => value++;
}

public static class StructMethods
{
    public static ulong Mutate(ulong value)
    {
        Counter counter = default;
        counter.Set(value);
        counter.Add(7);
        return counter.Read();
    }

    public static ulong ByValue(ulong value)
    {
        Counter counter = default;
        counter.Set(value);
        ChangeCopy(counter);
        return counter.Read();
    }

    [MethodImpl(MethodImplOptions.NoInlining)]
    static void ChangeCopy(Counter counter) => counter.Set(0);

    public static ulong Arguments(ulong value)
    {
        Counter counter = default;
        counter.Set(value);
        return counter.Mix(value, 3, 5, 7);
    }

    public static ulong Replace(ulong value)
    {
        Counter source = default;
        source.Set(value);
        Counter destination = default;
        destination.Replace(source);
        return destination.Read();
    }

    public static byte Narrow(byte value)
    {
        Counter counter = default;
        return counter.Parameter(value);
    }

    public static ulong ConstructLocal(ulong value)
    {
        var counter = new Counter(value);
        return counter.Read();
    }
}
