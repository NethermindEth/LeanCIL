using System.Runtime.InteropServices;
using System.Text.RegularExpressions;

partial class Program
{
    /// <summary>The checked-in Lean module that holds the fixture image.</summary>
    static string Fixture => At("Tests/StrictBinding/Fixture.lean");

    /// <summary>
    /// The container, table positions, heaps, method body offsets and identity that Lean decodes from an
    /// image, compared line by line with System.Reflection.Metadata on the same bytes: Examples.dll, the
    /// checked-in fixture and the platform reference assembly System.Runtime.
    /// </summary>
    static void CheckBindingDecoding(string root)
    {
        // The checked-in module is what its own image generates, so its expected facts are the reader's.
        var fixtureText = File.ReadAllText(Fixture);
        var fixtureImage = StrictBindingFacts.ReadImage(fixtureText);
        if (StrictBindingFacts.Module(fixtureImage) != fixtureText.ReplaceLineEndings("\n"))
            throw new InvalidOperationException(Fixture + " is not what its image generates; run " +
                "`dotnet run --file Tests/StrictBindingFixture.cs -- --update`.");
        RequireBoundedDigestLemmas();
        (string Name, byte[] Bytes)[] images =
        [
            ("Examples.dll", File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"))),
            ("the strict binding fixture", fixtureImage),
            ("the System.Runtime reference assembly", File.ReadAllBytes(PlatformReference()))
        ];
        var package = FixturePackage();
        Run(["lake", "build", "StrictBinding"], package, progress: "Building the strict binding library");
        Directory.CreateDirectory(root);
        RequireLargeDigestToElaborate(root, package);
        for (var index = 0; index < images.Length; index++)
        {
            var (name, bytes) = images[index];
            var path = Path.Combine(root, $"Describe{index}.lean");
            File.WriteAllText(path, DescribeModule(bytes));
            var (code, output, stdout, _) = Execute(["lake", "env", "lean", "--run", path], cwd: package);
            if (code != 0) throw new InvalidOperationException($"Lean could not describe {name}: {output}");
            string[] lean = stdout.ReplaceLineEndings("\n").Split('\n', StringSplitOptions.RemoveEmptyEntries);
            string[] expected = [.. StrictBindingFacts.Read(bytes).Select(fact => fact.Line())];
            var mismatch = Enumerable.Range(0, Math.Min(lean.Length, expected.Length))
                .FirstOrDefault(line => lean[line] != expected[line], -1);
            if (mismatch >= 0 || lean.Length != expected.Length)
                throw new InvalidOperationException($"Lean and System.Reflection.Metadata disagree on {name}: " +
                    $"{lean.Length} and {expected.Length} lines" +
                    (mismatch < 0 ? "" : $"; line {mismatch + 1} is '{lean[mismatch]}' and '{expected[mismatch]}'"));
            Console.WriteLine($"PASS Lean decodes {name} as System.Reflection.Metadata does: {lean.Length} facts");
        }
    }

    /// <summary>
    /// Kernel memory for hashing is bounded by the block count of one lemma, so a generated digest proof states one
    /// lemma per page of 64 chunks, however large the file, and one evaluation of a whole file is refused.
    /// </summary>
    static void RequireBoundedDigestLemmas()
    {
        var file = new byte[3 * 4096 + 100];
        new Random(7).NextBytes(file);
        var proof = BindingImage.PagedDigestTheorem(file, skipCompileCheck: true);
        var definitions = BindingImage.Definitions(file);
        var lemmas = Regex.Matches(proof, @"(?m)^set_option debug\.skipKernelTC true in\ntheorem hash\d+ ").Count;
        var longest = Regex.Matches(definitions, @"(?s)def page\d+ : List Nat := \[(.*?)\]")
            .Max(page => page.Groups[1].Value.Split(",\n").Length);
        if (lemmas != 4 || longest > 64)
            throw new InvalidOperationException(
                $"Digest proof is not one lemma per page: {lemmas} lemmas, {longest} chunks");
        try { BindingImage.SingleDigestTheorem(file); }
        catch (ArgumentException)
        {
            Console.WriteLine("PASS digest proofs state one lemma per page of 64 chunks");
            return;
        }
        throw new InvalidOperationException("Whole-file kernel hashing was accepted");
    }

    /// <summary>
    /// A digest proof of a file of 210 pages, about the size of a platform reference assembly, elaborates: the
    /// chain of page lemmas has no term nested more deeply than one level. Only elaboration runs, since replay
    /// costs minutes.
    /// </summary>
    static void RequireLargeDigestToElaborate(string root, string package)
    {
        var file = new byte[210 * 4096 - 17];
        new Random(11).NextBytes(file);
        var path = Path.Combine(root, "LargeDigest.lean");
        File.WriteAllText(path, "import StrictBinding.Sha256\n\nnamespace Large\n\n" + BindingImage.Definitions(file) +
            "\n" + BindingImage.PagedDigestTheorem(file, skipCompileCheck: true) + "end Large\n");
        var run = Execute(["lake", "env", "lean", path], cwd: package);
        if (run.Code != 0)
            throw new InvalidOperationException("A digest of 210 pages did not elaborate: " + run.Output);
        Console.WriteLine("PASS a digest proof of 210 pages elaborates");
    }

    /// <summary>A program that prints the description of an image the audit decodes, one fact per line.</summary>
    static string DescribeModule(byte[] file) => $$"""
        import StrictBinding.Dump

        namespace StrictDescribe

        {{BindingImage.Definitions(file)}}
        end StrictDescribe

        def main : IO UInt32 := do
          match StrictBinding.describe StrictDescribe.image with
          | .ok lines =>
            lines.forM IO.println
            pure 0
          | .error error =>
            IO.eprintln (repr error)
            pure 1
        """;

    /// <summary>The newest platform reference assembly System.Runtime of the .NET 11 reference pack.</summary>
    static string PlatformReference()
    {
        var runtime = Path.GetFullPath(Path.Combine(RuntimeEnvironment.GetRuntimeDirectory(), "..", "..", ".."));
        var packs = Path.Combine(Environment.GetEnvironmentVariable("DOTNET_ROOT") ?? runtime, "packs",
            "Microsoft.NETCore.App.Ref");
        return Directory.EnumerateDirectories(packs, "11.*")
            .Select(directory => Path.Combine(directory, "ref", "net11.0", "System.Runtime.dll")).Where(File.Exists)
            .OrderByDescending(path => Version.Parse(Path.GetFileName(
                Path.GetDirectoryName(Path.GetDirectoryName(Path.GetDirectoryName(path)))!)))
            .FirstOrDefault() ?? throw new FileNotFoundException("No .NET 11 reference pack under " + packs);
    }
}
