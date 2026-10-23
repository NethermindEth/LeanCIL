namespace ImportFixture;

public static class Application
{
    public static ulong Entry(ulong value) => Library.AddOne(value);
    public static ulong Generic(ulong value) => Library.Identity(value);
    public static ulong Unrelated(ulong value) => value + 2;
}
