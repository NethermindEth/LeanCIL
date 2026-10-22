namespace ImportFixture;

public class Library
{
    public static ulong AddOne(ulong value) => value + 1;
    public static T Identity<T>(T value) => value;
}
