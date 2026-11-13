partial class Program
{
    /// <summary>
    /// The body check costs time linear in the number of bodies and independent of the image size per body. 318 and
    /// 1272 bodies of Examples.dll (98 KB) take about four times as long as each other, and the same 1272 bodies of
    /// Examples.dll followed by 770 KB of other bytes, which no body reads, take at most about twice as long, the cost
    /// of decoding the larger image once per page of bodies, where a read that touched the whole image would take
    /// about nine times as long. The claims are identical in the last two cases, so the bodies cannot differ in size.
    /// Times are measured above the fixture's, which is the fixed cost.
    /// </summary>
    static void CheckBindingScaling(string root)
    {
        // Memory cannot be measured here, so the page layout that bounds it is pinned: 250 methods per page until the
        // 32-page cap, then pages that grow with the evidence.
        (int Methods, int Size, int Pages)[] layouts = [(318, 250, 2), (1272, 250, 6), (10767, 337, 32)];
        foreach (var (methods, size, pages) in layouts)
            if (BindingPageSize(methods) != size || BindingPageCount(methods) != pages)
                throw new InvalidOperationException($"{methods} methods are paged {BindingPageCount(methods)} x " +
                    $"{BindingPageSize(methods)}, not {pages} x {size}");
        Console.WriteLine("PASS the body proof pages at 250 methods up to 32 pages");
        var package = FixturePackage();
        Run(["lake", "build", "StrictBinding.Evidence"], package, progress: "Building the strict binding library");
        CheckGeneratedBodiesModuleElaborates(root, package);
        var examples = File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"));
        var larger = new byte[examples.Length + 770 * 1024];
        examples.CopyTo(larger, 0);
        new Random(5).NextBytes(larger.AsSpan(examples.Length));
        (string Name, byte[] Bytes, int Bodies)[] cases =
        [
            ("fixture", StrictBindingFacts.ReadImage(File.ReadAllText(Fixture)), int.MaxValue),
            ("Examples.dll, 318 bodies", examples, 318),
            ("Examples.dll, 1272 bodies", examples, 1272),
            ("Examples.dll and 770 KB more, 1272 bodies", larger, 1272)
        ];
        Directory.CreateDirectory(root);
        var seconds = new double[cases.Length];
        for (var index = 0; index < cases.Length; index++)
        {
            var path = Path.Combine(root, $"Bodies{index}.lean");
            File.WriteAllText(path, AllBodiesModule(cases[index].Bytes, cases[index].Bodies));
            var started = System.Diagnostics.Stopwatch.StartNew();
            var run = Execute(["lake", "env", "lean", path], cwd: package);
            seconds[index] = started.Elapsed.TotalSeconds;
            if (run.Code != 0)
                throw new InvalidOperationException($"The bodies of {cases[index].Name} were not found: {run.Output}");
        }
        var times = cases.Zip(seconds, (item, time) => $"{item.Name} {time:F1} s");
        Console.WriteLine("Body checks: " + string.Join(", ", times));
        double Above(int index) => seconds[index] - seconds[0];
        if (Above(1) < 2) throw new InvalidOperationException("The body check is too fast to measure its growth");
        var perBody = Above(2) / Above(1);
        var perImage = Above(3) / Above(2);
        if (perBody is < 2 or > 8 || perImage > 4)
            throw new InvalidOperationException(
                $"The body check grew {perBody:F1} times for 4 times the bodies and " +
                $"{perImage:F1} times for 8.8 times the image");
        Console.WriteLine($"PASS the body check is linear in the bodies ({perBody:F1} times for 4) and " +
            $"independent of the image size ({perImage:F1} times for 8.8)");
    }

    /// <summary>
    /// Elaborates the module the audit generates, over an extraction with no methods, so a malformed
    /// declaration in the generator fails here and not only in an end-to-end audit.
    /// </summary>
    static void CheckGeneratedBodiesModuleElaborates(string root, string package)
    {
        const string imports = "import BindingAudit.Images\nimport Extracted\nimport StrictBinding.Evidence\n";
        const string stubs = """
            import StrictBinding.Evidence
            namespace Extracted
            def methodEvidence : List CIL.Extraction.MethodEvidence := []
            end Extracted
            namespace BindingAudit
            def images : List StrictBinding.PinnedImage := []
            end BindingAudit

            """;
        var source = BodiesModuleSource(3, 1);
        if (!source.StartsWith(imports, StringComparison.Ordinal))
            throw new InvalidOperationException("The generated bodies module no longer starts with its imports");
        Directory.CreateDirectory(root);
        var path = Path.Combine(root, "GeneratedBodies.lean");
        File.WriteAllText(path, stubs.ReplaceLineEndings("\n") + source[imports.Length..]);
        var run = Execute(["lake", "env", "lean", path], cwd: package);
        if (run.Code != 0)
            throw new InvalidOperationException($"The generated bodies module does not elaborate: {run.Output}");
        Console.WriteLine("PASS the generated bodies module elaborates");
    }

    /// <summary>
    /// A module stating that every body System.Reflection.Metadata reads is found in the image, composed the way a
    /// generated module composes its pages: one theorem per page of claims, each its own kernel evaluation, and the
    /// whole from `claimedBodiesBound_of_pages`. The page lemmas are checked when the module is built.
    /// </summary>
    static string AllBodiesModule(byte[] file, int limit)
    {
        var identity = StrictBindingFacts.Read(file).Last().Text;
        var bodies = StrictBindingFacts.Bodies(file).Take(limit).ToArray();
        var size = BindingPageSize(bodies.Length);
        var parts = bodies.Select(body =>
            $"{{ identity := \"{identity}\", token := 0x{body.Token:x8}, " +
            $"bytes := [{string.Join(", ", body.Bytes)}] }}")
            .Chunk(size).ToArray();
        var defs = string.Concat(parts.Select((part, index) =>
            $"def claims{index} : List StrictBinding.BodyClaim :=\n  [{string.Join(",\n   ", part)}]\n\n"));
        var joined = Enumerable.Range(0, parts.Length - 1).Reverse().Aggregate($"claims{parts.Length - 1}",
            (rest, index) => $"(claims{index} ++ {rest})");
        var lemmas = string.Concat(parts.Select((_, index) => $"theorem bodiesOf{index} : " +
            $"StrictBinding.ClaimedBodiesBound pinned (StrictBinding.claimPage claims {size} {index}) := by\n" +
            "  decide +kernel\n\n"));
        var chain = string.Concat(Enumerable.Range(0, parts.Length).Reverse()
            .Select(index => $"(.succ bodiesOf{index} "));
        return $$"""
            import StrictBinding.Bind

            namespace Scaling

            {{BindingImage.Definitions(file)}}
            def pinned : List StrictBinding.PinnedImage := [{ identity := "{{identity}}", image := image }]

            {{defs}}def claims : List StrictBinding.BodyClaim := {{joined}}

            theorem prepared : StrictBinding.ok (StrictBinding.prepare pinned) = true := by decide +kernel

            {{lemmas}}theorem found : StrictBinding.ClaimedBodiesBound pinned claims :=
              StrictBinding.claimedBodiesBound_of_pages (size := {{size}}) (count := {{parts.Length}}) prepared
                (by decide +kernel) {{chain}}.zero{{new string(')', parts.Length)}}

            end Scaling
            """;
    }
}
