namespace Examples;

public interface ICounterValue
{
    int Read();
}

public struct CounterValue : ICounterValue
{
    public int Value;
    public int Read() => Value;
}

public struct ExplicitCounterValue : ICounterValue
{
    public int Value;
    int ICounterValue.Read() => Value + 1;
}

public static class ConstrainedCalls
{
    public static int Read<T>(ref T value) where T : struct, ICounterValue => value.Read();

    public static int Implicit(ref CounterValue value) => Read(ref value);

    public static int Explicit(ref ExplicitCounterValue value) => Read(ref value);

    public static int OrdinaryVirtual(ICounterValue value) => value.Read();
}
