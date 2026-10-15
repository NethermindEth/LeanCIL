namespace Examples;

public static class InitializedTypes
{
    public static readonly ulong Constant = 42;
    public static ulong Add(ulong x, ulong y) => unchecked(x + y);
    public static ulong ReadConstant() => Constant;
    public static ulong CallHelper(ulong x) => InitializedHelper.Identity(x);
}

public static class InitializedHelper
{
    public static readonly ulong Constant = 7;
    public static ulong Identity(ulong x) => x;
}

public struct InitializedValue
{
    public static readonly ulong Constant = 1;
    public ulong Value;
    public static ulong Read(ref InitializedValue value) => value.Value;
}
