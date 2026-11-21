namespace ImportFixture;

public static class Application
{
    public static ulong Entry(ulong value) => Library.AddOne(value);
    public static ulong Generic(ulong value) => Library.Identity(value);
    public static ulong Unrelated(ulong value) => value + 2;
}

internal class MetadataBase<T>;

internal sealed class MetadataRecursive : MetadataBase<MetadataRecursive>
{
    public static int Run() => 7;
}

internal class MetadataPair<TLeft, TRight>;
internal class Depth0;
internal class Depth1 : MetadataPair<Depth0, Depth0>;
internal class Depth2 : MetadataPair<Depth1, Depth1>;
internal class Depth3 : MetadataPair<Depth2, Depth2>;
internal class Depth4 : MetadataPair<Depth3, Depth3>;
internal class Depth5 : MetadataPair<Depth4, Depth4>;
internal class Depth6 : MetadataPair<Depth5, Depth5>;
internal class Depth7 : MetadataPair<Depth6, Depth6>;
internal class Depth8 : MetadataPair<Depth7, Depth7>
{
    public static int Run() => 7;
}
internal class Depth9 : MetadataPair<Depth8, Depth8>;
internal class Depth10 : MetadataPair<Depth9, Depth9>
{
    public static int Run() => 7;
}
internal class Depth11 : MetadataPair<Depth10, Depth10>;
internal class Depth12 : MetadataPair<Depth11, Depth11>
{
    public static int Run() => 7;
}
internal class Depth13 : MetadataPair<Depth12, Depth12>;
internal class Depth14 : MetadataPair<Depth13, Depth13>
{
    public static int Run() => 7;
}

internal sealed class MetadataDerived : MetadataBase<int>
{
    public static int Run() => 7;
    public static int First(ref (int, uint) value) => value.Item1;
}
