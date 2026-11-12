/// <summary>Small integer operations whose catalog bindings keep exact managed signatures.</summary>
public static class BindingMethods
{
    /// <summary>Unsigned equality at the 32-bit stack width.</summary>
    public static bool Equal(uint left, uint right) => left == right;

    /// <summary>Signed inequality at the 64-bit stack width.</summary>
    public static bool Different(long left, long right) => left != right;

    /// <summary>Signed bitwise conjunction at the 32-bit stack width.</summary>
    public static int And(int left, int right) => left & right;

    /// <summary>Unsigned bitwise exclusive-or at the 64-bit stack width.</summary>
    public static ulong Xor(ulong left, ulong right) => left ^ right;
}
