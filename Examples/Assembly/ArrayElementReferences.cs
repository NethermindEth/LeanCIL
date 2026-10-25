namespace Examples;

public static class ArrayElementReferences
{
    public static ref int Element(int[] values, int index) => ref values[index];

    public static int Read(int[] values, int index)
    {
        ref var element = ref Element(values, index);
        return element;
    }

    public static int Write(int[] values, int index, int value)
    {
        ref var element = ref Element(values, index);
        element = value;
        return values[index];
    }
}
