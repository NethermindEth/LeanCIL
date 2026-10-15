namespace Examples;

internal static class WideProduct
{
    public static ulong BigMul(ulong left, ulong right, out ulong low) => System.Math.BigMul(left, right, out low);
}
