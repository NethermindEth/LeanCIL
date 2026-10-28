
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
        }
        finally { Directory.Delete(root, true); }
    }
}
