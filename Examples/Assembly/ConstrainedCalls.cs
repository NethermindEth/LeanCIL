namespace Examples;

public interface ICounterValue
{
    int Read();
    void Increment();
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

    public static int OrdinaryVirtual(ICounterValue value) => value.Read();
}
