namespace Examples;

public static unsafe class NativeManagedDispatch
{
    public static int Dispatch(nint* table, int index, int value, int count, long marker)
    {
        var target = table[index];
        return ((delegate* managed<int, int, long, int>)target)(value, count, marker);
    }

    public static int Repeat(int value, int count, long marker)
    {
        if (marker < 0) throw new System.InvalidOperationException();
        return count == 0 ? value :
            ((delegate* managed<int, int, long, int>)&Repeat)(value + 1, count - 1, marker);
    }
}
