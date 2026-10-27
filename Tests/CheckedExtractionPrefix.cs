partial class Program
{
    // The original declarations are checked once; every variant must retain their exact source bytes.
    sealed class CheckedExtractionPrefix
    {
        readonly string prefix;
        readonly string module;
        readonly string directory;

        public CheckedExtractionPrefix(string source, string boundary, string directory)
        {
            var start = source.IndexOf(boundary, StringComparison.Ordinal);
            if (start < 0 || !source[..start].Contains("namespace Extracted\n", StringComparison.Ordinal))
                throw new InvalidOperationException("Missing generated extraction prefix boundary.");
            prefix = source[..start];
            this.directory = directory;
            module = "CheckedPrefix" + ContentKey(prefix);
            Directory.CreateDirectory(directory);
            var path = Path.Combine(directory, module + ".lean");
            File.WriteAllText(path, prefix + "\nend Extracted\n");
            Run(["lean", "--root=" + directory, "-o", Path.ChangeExtension(path, ".olean"), path],
                leanPath: LeanPath, progress: "Checking unchanged extraction prefix");
        }

        public string LeanPath => directory + Path.PathSeparator + FixtureLeanPath();

        public string Module => module;

        public string RemainingSource(string source)
        {
            if (!source.StartsWith(prefix, StringComparison.Ordinal))
                throw new InvalidOperationException("Mutation changes the checked extraction prefix.");
            return "import " + module + "\nnamespace Extracted\nopen CIL\n" +
                "set_option maxRecDepth 4096\n" + source[prefix.Length..];
        }
    }
}
