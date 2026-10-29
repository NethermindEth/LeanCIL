namespace Examples;

public static unsafe class ManagedDispatch
{
    public static int Dispatch(delegate* managed<int, int>[] handlers, int index, int value) =>
        handlers[index](value);

    public static int Repeat(int value) => value == 0 ? 17 : Repeat(value - 1);

    public static int Raise(int value) => value == 0
        ? throw new System.ArgumentException()
        : Raise(value - 1);

    public static int Address(int value) => ((delegate* managed<int, int>)&Repeat)(value);

    public static int Read(ref int value) => value;

    public static int LocalEscape(int value)
    {
        var local = value;
        return ((delegate* managed<ref int, int>)&Read)(ref local);
    }
    public static delegate* managed<float, float> UnrelatedTarget() => &Identity<float>;

    private static T Identity<T>(T value) => value;

    // These addresses define the bounded handler universe independently of the supplied table.
    public static void Targets(delegate* managed<int, int>[] handlers)
    {
        handlers[0] = &Repeat;
        handlers[1] = &Raise;
    }
}
