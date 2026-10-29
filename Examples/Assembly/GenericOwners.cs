namespace Examples;

public static class GenericOwners
{
    public static uint Identity(uint value) => OwnerHelper<uint>.Identity(value);

    public static uint Combined(uint value) => OwnerHelper<ulong>.Select<uint>(value, 0);

    public static uint Nested(uint value) => OwnerOuter<ulong>.Inner<uint>.Identity(value);

    public static uint Repeated(uint value) =>
        OwnerHelper<uint>.Identity(value) + OwnerHelper<uint>.Identity(value);

    public static unsafe uint Address(uint value) =>
        ((delegate* managed<uint, uint>)&OwnerHelper<uint>.Identity)(value);
}

public static class OwnerHelper<T> where T : unmanaged
{
    public static T Identity(T value) => value;

    public static U Select<U>(U value, T unused) where U : unmanaged => value;
}

public static class OwnerOuter<T> where T : unmanaged
{
    public static class Inner<U> where U : unmanaged
    {
        public static U Identity(U value) => value;
    }
}
