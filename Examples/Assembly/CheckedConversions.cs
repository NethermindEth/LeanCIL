namespace Examples;

public static class CheckedConversions
{
    public static uint Narrow(ulong value) => checked((uint)value);
}
