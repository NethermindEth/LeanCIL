namespace SelectorExamples.One
{
    internal static class Collision
    {
        public static ulong Add(ulong x, ulong y) => unchecked(x + y);
        public static uint Add(uint x, uint y) => unchecked(x + y);
        public static string Unsupported(string value) => value;
    }
}

namespace SelectorExamples.Two
{
    internal static class Collision
    {
        public static ulong Add(ulong x, ulong y) => unchecked(x + y);
    }
}
