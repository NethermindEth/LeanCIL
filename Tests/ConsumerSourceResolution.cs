
partial class Program
{
    static void CheckConsumerSourceResolution(string[] args)
    {
        var root = Path.Combine(Path.GetTempPath(), "leancil-source-resolution-" + Guid.NewGuid().ToString("N"));
        Directory.CreateDirectory(root);
        try
        {
            File.Copy(At("lean-toolchain"), Path.Combine(root, "lean-toolchain"));
            File.WriteAllText(Path.Combine(root, "lakefile.toml"), """
        name = "source-resolution"
        srcDir = "Sources"
        [[lean_lib]]
        name = "Published"
        srcDir = "Library"
        """);
            var library = Path.Combine(root, "Sources", "Library");
            Directory.CreateDirectory(library);
            var unrelated = Path.Combine(root, "Tests", "Fixtures");
            Directory.CreateDirectory(unrelated);
            File.WriteAllText(Path.Combine(unrelated, "Published.lean"), "-- unrelated source\n");
            var directories = ConsumerSourceDirectories(root, [root]);
            RejectContractSourceShadow("Published", directories);
            Console.WriteLine("PASS deeper same-named source does not shadow a module");

            void Reject(string module)
            {
                try { RejectContractSourceShadow(module, directories); }
                catch (InvalidDataException error) when (error.Message ==
                    "Contract interface module shadows a consumer source: " + module) { return; }
                throw new Exception("Missed module shadow: " + module);
            }

            var source = Path.Combine(library, "Published.lean");
            File.WriteAllText(source, "-- library source\n");
            Reject("Published");
            var caseVariant = Path.Combine(library, "published.lean");
            if (File.Exists(caseVariant)) Reject("published");
            else RejectContractSourceShadow("published", directories);
            File.Delete(source);
            File.WriteAllText(Path.Combine(root, "Published.lean"), "-- package source\n");
            Reject("Published");
            Console.WriteLine("PASS library/package roots and filesystem case rules");
            CheckGeneratedImportSources(root);
        }
        finally { Directory.Delete(root, true); }
    }

    static void CheckGeneratedImportSources(string root)
    {
        var snapshot = new SortedDictionary<string, string>(StringComparer.Ordinal);
        string Source(string relative, string text)
        {
            var path = Path.Combine(root, relative.Replace('/', Path.DirectorySeparatorChar));
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, text);
            snapshot.Add("consumer:" + path, Sha(path));
            return path;
        }
        var proof = Source("Proof.lean", "import Shared.Helper\nimport Alias\nimport Shared.Helper\n");
        var first = Source("A/Shared/Helper.lean", "import Extracted.First\nimport Alias\n");
        var second = Source("B/Shared/Helper.lean", "import ExtractedSymbols.Second\nimport Shared.Helper\n");
        var alias = Source("Alias.lean", "import ExtractedSymbols\n");
        Source("NotShared/Helper.lean", "import Extracted.Unrelated\n");
        var graph = new ConsumerImports(snapshot, root);
        if (!graph.Generated(proof).SequenceEqual([("Extracted.First", first),
            ("ExtractedSymbols.Second", second), ("ExtractedSymbols", alias)]))
            throw new InvalidOperationException("Ambiguous consumer imports lost a source or changed order.");
        File.AppendAllText(second, "import Extracted.Changed\n");
        try { _ = new ConsumerImports(snapshot, root).Generated(proof).ToArray(); }
        catch (InvalidOperationException error) when (error.Message == "Inputs changed during consumer verification")
        {
            Console.WriteLine("PASS generated imports bind both roots, cycles and source contents");
            return;
        }
        throw new InvalidOperationException("Import selection accepted source bytes outside the snapshot.");
    }
}
