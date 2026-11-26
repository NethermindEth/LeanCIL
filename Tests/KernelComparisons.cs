partial class Program
{
    // A balanced tree retains every claim without a linear-depth proof term.
    static string Balanced(IReadOnlyList<string> entries, Func<string, string, string> join)
    {
        string Build(int start, int count)
        {
            if (count == 1) return entries[start];
            var half = count / 2;
            return join(Build(start, half), Build(start + half, count - half));
        }
        return Build(0, entries.Count);
    }

    // The proof of entry `index` of `count` from `pairs`, an equation of the tuples `Balanced` builds.
    static string Projection(string pairs, int count, int index)
    {
        var (start, term) = (0, pairs);
        while (count > 1)
        {
            var half = count / 2;
            var first = index < start + half;
            term = $"(Prod.mk.inj {term}).{(first ? 1 : 2)}";
            (start, count) = first ? (start, half) : (start + half, count - half);
        }
        return term;
    }

    /// <summary>
    /// A private Lean theorem `results` equating the tuple of every claim's left side with the tuple of its
    /// right side. One kernel evaluation checks every comparison, so the program's definitions unfold once per
    /// fixture; `Projection("results", claims.Count, index)` proves claim `index`.
    /// </summary>
    static string ComparisonResults(IReadOnlyList<(string Left, string Right)> claims)
    {
        string Tuple(IEnumerable<string> sides) =>
            Balanced([.. sides.Select(side => $"({side})")], (left, right) => $"({left}, {right})");
        return $$"""
            /-- Each compiled call returns the result or raises the fault observed at runtime. -/
            private theorem results :
            {{Tuple(claims.Select(claim => claim.Left))}} =
            {{Tuple(claims.Select(claim => claim.Right))}} := by cil_kernel_rfl
            #print axioms results
            """;
    }
}
