namespace Examples;

internal static class WideProduct
{
    public static ulong BigMul(ulong left, ulong right, out ulong low) => System.Math.BigMul(left, right, out low);

    public static long SignedBigMul(long left, long right, out long low) => System.Math.BigMul(left, right, out low);

    public static long BigMul32(int left, int right) => System.Math.BigMul(left, right);

    public static ulong UnsignedBigMul32(uint left, uint right) => System.Math.BigMul(left, right);
}
