namespace Examples;

internal static class PrimitiveOperations
{
    public static int ReadWrite(ref int target, int value)
    {
        target = value;
        return target;
    }

    public static int Alias(ref short target, ref short alias, int value)
    {
        target = unchecked((short)value);
        return alias;
    }

    public static int Choose(int index) => index switch
    {
        0 => 13,
        1 => 29,
        2 => 7,
        3 => 41,
        4 => 19,
        _ => -1
    };

    public static unsafe int PacketSize() => sizeof(Packet);
}
