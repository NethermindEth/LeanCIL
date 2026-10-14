namespace Examples;

internal static class IntegerOperations
{
    public static bool Greater32(int left, int right) => left > right;
    public static bool Greater64(long left, long right) => left > right;
    public static int Negate32(int value) => unchecked(-value);
    public static long Negate64(long value) => unchecked(-value);
}
