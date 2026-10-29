namespace Examples;

public static unsafe class PointerOperations
{
    public static byte* Subtract(byte* value, int count) => value - count;
    public static byte* SubtractNative(byte* value, nint count) => value - count;
    public static long Difference(byte* left, byte* right) => left - right;
    public static bool Less(byte* left, byte* right) => left < right;
    public static bool Greater(byte* left, byte* right) => left > right;
    public static bool LessEqual(byte* left, byte* right) => left <= right;
    public static bool GreaterEqual(byte* left, byte* right) => left >= right;
    public static char ReadCharacter(char* values, int index) => values[index];
    public static Signed16 ReadEnum(Signed16* values, int index) => values[index];
    public static ulong WriteEnum(Unsigned64* values, ulong value)
    {
        values[1] = (Unsigned64)value;
        return (ulong)values[1];
    }
}
