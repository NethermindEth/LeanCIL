namespace Examples;

public static class CheckedArithmetic
{
    public static uint Add(uint x, uint y) => checked(x + y);
    public static ulong Add64(ulong x, ulong y) => checked(x + y);
    public static int AddSigned(int x, int y) => checked(x + y);
}
