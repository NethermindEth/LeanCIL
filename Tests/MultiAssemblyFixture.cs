partial class Program
{
    /// <summary>SDK-built assemblies under one artifact root, with extraction rejection helpers shared by
    /// the multi-assembly tests. Each rejection must fail with its marker and leave no certificate.</summary>
    sealed class MultiAssemblyFixture(string name)
    {
        internal string Root { get; } = At("artifacts/" + name + "-" + Guid.NewGuid().ToString("N"));

        internal string[] Cli { get; } = ["dotnet", ExtractorPath];

        /// <summary>Writes a Release net11.0 project and returns its directory.</summary>
        internal string Project(string name, string assembly, string properties = "", string references = "")
        {
            string directory = Path.Combine(Root, name);
            Directory.CreateDirectory(directory);
            File.WriteAllText(Path.Combine(directory, name + ".csproj"), $"""
                <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net11.0</TargetFramework>
                <AssemblyName>{assembly}</AssemblyName><Optimize>true</Optimize>{properties}</PropertyGroup>
                <ItemGroup>{references}</ItemGroup></Project>
                """);
            return directory;
        }

        /// <summary>Writes one source file into a project, builds it and returns the assembly path.</summary>
        internal string Build(string name, string assembly, string source, string properties = "",
            string references = "")
        {
            string directory = Project(name, assembly, properties, references);
            File.WriteAllText(Path.Combine(directory, name + ".cs"), source);
            Run(["dotnet", "build", Path.Combine(directory, name + ".csproj"), "-c", "Release"]);
            return Path.Combine(directory, "bin", assembly + ".dll");
        }

        internal string Artifact(string name) => Path.Combine(Root, "x-" + name);

        internal static string[] Reference(string path) => ["--reference", path];

        internal static void Rejected(string name, string marker, string[] command)
        {
            (int Code, string Output, string Stdout, string Stderr) result = Execute(command);
            if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
                throw new InvalidOperationException($"Expected rejection {name} ({marker}): {result.Output}");
            Console.WriteLine("PASS rejected " + name);
        }

        internal string RejectedExtract(string name, string marker, string assembly, string selector,
            params string[] extra)
        {
            string output = Path.Combine(Root, "r-" + name.Replace(' ', '-'));
            Rejected(name, marker, [.. Cli, "extract", assembly, selector, output, .. extra]);
            if (File.Exists(Path.Combine(output, "Extracted.lean")))
                throw new InvalidOperationException("Rejected extraction left a certificate: " + name);
            return output;
        }
    }
}
