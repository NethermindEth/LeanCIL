partial class Program
{
    /// <summary>The most a claim may cost more, per claim, when the claims grow at a fixed image.</summary>
    const double MaximumPerClaimGrowth = 2;

    /// <summary>The most the check may take longer, as a multiple, for a larger image with the same claims.</summary>
    const double MaximumImageGrowth = 4;

    /// <summary>
    /// The body check costs time linear in the number of claims and independent of the image size per claim. The
    /// 1272 claims of Examples.dll (98 KB) are repeated to 5088, which the page cap lays out in eight pages of
    /// 636 where 1272 claims take six pages of 212, so the cost per claim cannot hide in the page count. The same
    /// 1272 claims followed by 770 KB of other bytes, which no body reads, take at most about twice as long, the cost
    /// of decoding the larger image once per page, where a read that touched the whole image would take about nine
    /// times as long. Times are measured above the fixture's, which is the fixed cost.
    /// </summary>
    static void CheckBindingScaling(string root)
    {
        // Memory cannot be measured here, so the page layout that bounds it is pinned: pages of about 250 methods
        // until the page cap, then pages that grow with the evidence, and one empty page for no methods.
        (int Methods, int Size, int Pages)[] layouts =
            [(0, 1, 1), (318, 159, 2), (1272, 212, 6), (2000, 250, 8), (5088, 636, 8), (10767, 1346, 8)];
        foreach (var (methods, size, pages) in layouts)
            if (BindingPageSize(methods) != size || BindingPageCount(methods) != pages ||
                pages * size < methods)
                throw new InvalidOperationException($"{methods} methods are paged {BindingPageCount(methods)} x " +
                    $"{BindingPageSize(methods)}, not {pages} x {size}");
        Console.WriteLine("PASS the body proof pages at about 250 methods up to 8 pages");
        var package = FixturePackage();
        Run(["lake", "build", "StrictBinding.Evidence"], package, progress: "Building the strict binding library");
        CheckGeneratedBodiesModuleElaborates(root, package);
        var examples = File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"));
        var larger = new byte[examples.Length + 770 * 1024];
        examples.CopyTo(larger, 0);
        new Random(5).NextBytes(larger.AsSpan(examples.Length));
        const int smaller = 1272;
        const int largerClaims = 5088;
        (string Name, byte[] Bytes, int? Claims)[] cases =
        [
            ("fixture", StrictBindingFacts.ReadImage(File.ReadAllText(Fixture)), null),
            ($"Examples.dll, {smaller} claims", examples, smaller),
            ($"Examples.dll and 770 KB more, {smaller} claims", larger, smaller),
            ($"Examples.dll, {largerClaims} claims", examples, largerClaims)
        ];
        Directory.CreateDirectory(root);
        var seconds = new double[cases.Length];
        for (var index = 0; index < cases.Length; index++)
        {
            var path = Path.Combine(root, $"Bodies{index}.lean");
            File.WriteAllText(path, AllBodiesModule(cases[index].Bytes, cases[index].Claims));
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
        var perClaim = Above(3) / largerClaims / (Above(1) / smaller);
        var perImage = Above(2) / Above(1);
        if (perClaim > MaximumPerClaimGrowth || perImage > MaximumImageGrowth)
            throw new InvalidOperationException(
                $"The body check took {perClaim:F1} times as long per claim for {largerClaims / smaller} times the " +
                $"claims and {perImage:F1} times as long for 8.8 times the image");
        Console.WriteLine($"PASS the body check is linear in the claims ({perClaim:F1} times per claim) and " +
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
        Directory.CreateDirectory(root);
        foreach (var (methods, size) in new[] { (3, 1), (0, BindingPageSize(0)) })
        {
            var source = BodiesModuleSource(methods, size);
            if (!source.StartsWith(imports, StringComparison.Ordinal))
                throw new InvalidOperationException("The generated bodies module no longer starts with its imports");
            var path = Path.Combine(root, $"GeneratedBodies{methods}.lean");
            File.WriteAllText(path, stubs.ReplaceLineEndings("\n") + source[imports.Length..]);
            var run = Execute(["lake", "env", "lean", path], cwd: package);
            if (run.Code != 0)
                throw new InvalidOperationException(
                    $"The generated bodies module for {methods} methods does not elaborate: {run.Output}");
        }
        Console.WriteLine("PASS the generated bodies module elaborates, also for no methods");
    }

    /// <summary>
    /// A module stating that every body System.Reflection.Metadata reads is found in the image, composed the way a
    /// generated module composes its pages: one theorem per page of claims, each its own kernel evaluation, and the
    /// whole from `claimsHold_of_pages`. The page lemmas are checked when the module is built.
    /// </summary>
    static string AllBodiesModule(byte[] file, int? claims)
    {
        var identity = StrictBindingFacts.Read(file).Last().Text;
        var read = StrictBindingFacts.Bodies(file);
        // A claim count beyond the bodies the image has repeats them, so the claims can outgrow a fixed image.
        var bodies = Enumerable.Range(0, claims ?? read.Count).Select(index => read[index % read.Count]).ToArray();
        var size = BindingPageSize(bodies.Length);
        // One definition per claim keeps each list literal small enough for the elaborator's recursion limit.
        var parts = bodies.Select(body =>
            $"{{ identity := \"{identity}\", token := 0x{body.Token:x8}, " +
            $"bytes := [{string.Join(", ", body.Bytes)}] }}")
            .Chunk(size).ToArray();
        var defs = string.Concat(parts.Select((part, index) =>
            string.Concat(part.Select((claim, at) =>
                $"def claim{index}_{at} : StrictBinding.BodyClaim := {claim}\n")) +
            $"def claims{index} : List StrictBinding.BodyClaim :=\n  " +
            $"[{string.Join(", ", part.Select((_, at) => $"claim{index}_{at}"))}]\n\n"));
        var joined = Enumerable.Range(0, parts.Length - 1).Reverse().Aggregate($"claims{parts.Length - 1}",
            (rest, index) => $"(claims{index} ++ {rest})");
        var lemmas = string.Concat(parts.Select((_, index) => $"theorem bodiesOf{index} : " +
            $"StrictBinding.ClaimsHold StrictBinding.bodyClaimBound pinned " +
            $"(StrictBinding.claimPage claims {size} {index}) := by\n" +
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

            {{lemmas}}theorem found : StrictBinding.ClaimsHold StrictBinding.bodyClaimBound pinned claims :=
              StrictBinding.claimsHold_of_pages (size := {{size}}) (count := {{parts.Length}}) prepared
                (by decide +kernel) {{chain}}.zero{{new string(')', parts.Length)}}

            end Scaling
            """;
    }
}
