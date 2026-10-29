namespace Examples;

public interface ICounterValue
{
    int Read();
    void Increment();
}

public interface IClosedCounter<T>
{
    int Read();
}

public struct ClosedInterfaceCounter : IClosedCounter<int>, IClosedCounter<long>
{
    public int Value;
    int IClosedCounter<int>.Read() => Value;
    int IClosedCounter<long>.Read() => Value + 1;
}

public struct GenericInterfaceCounter<T> : IClosedCounter<T> where T : unmanaged
{
    public int Value;
    public T Payload;
    public int Read() => Value;
}

public struct CounterValue : ICounterValue
{
    public int Value;
    public int Read() => Value;
    public void Increment() => Value++;
}

public struct ExplicitCounterValue : ICounterValue
{
    public int Value;
    int ICounterValue.Read() => Value + 1;
    void ICounterValue.Increment() => Value++;
}

public struct GenericCounterValue<T> : ICounterValue where T : unmanaged
{
    public int Value;
    public T Payload;
    public int Read() => Value;
    public TMethod Read<TMethod>(TMethod value) => value;
    public T Echo(T value) => value;
    public void Increment() => Value++;
}

public struct ExplicitGenericCounterValue<T> : ICounterValue where T : unmanaged
{
    public int Value;
    public T Payload;
    int ICounterValue.Read() => Value + 1;
    void ICounterValue.Increment() => Value++;
}

public static class ConstrainedCalls
{
    public static int Read<T>(ref T value) where T : struct, ICounterValue => value.Read();

    public static int Implicit(ref CounterValue value) => Read(ref value);

    public static int Explicit(ref ExplicitCounterValue value) => Read(ref value);

    public static int IncrementAndRead<T>(ref T value) where T : struct, ICounterValue
    {
        value.Increment();
        return value.Read();
    }

    public static int Mutating(ref CounterValue value) => IncrementAndRead(ref value);

    public static int MutatingExplicit(ref ExplicitCounterValue value) => IncrementAndRead(ref value);

    public static int Generic(ref GenericCounterValue<int> value) => Read(ref value);

    public static int DirectGeneric(ref GenericCounterValue<int> value) => value.Echo(42);

    public static int ReadClosedInt<T>(ref T value) where T : struct, IClosedCounter<int> => value.Read();

    public static int ReadClosedLong<T>(ref T value) where T : struct, IClosedCounter<long> => value.Read();

    public static int ClosedBoth(ref ClosedInterfaceCounter value) =>
        ReadClosedInt(ref value) + ReadClosedLong(ref value);

    public static int ClosedGeneric(ref GenericInterfaceCounter<int> value) => ReadClosedInt(ref value);

    public static int GenericExplicit(ref ExplicitGenericCounterValue<int> value) => IncrementAndRead(ref value);

    public static int TwoGenericOwners(ref GenericCounterValue<int> first, ref GenericCounterValue<long> second) =>
        Read(ref first) + Read(ref second);

    public static int OrdinaryVirtual(ICounterValue value) => value.Read();
}
