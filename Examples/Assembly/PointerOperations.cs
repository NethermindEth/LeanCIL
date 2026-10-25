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
}
