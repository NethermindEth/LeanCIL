using System.Text.Json;
using Mono.Cecil;

partial class Program
{
    static readonly string[] CorpusLanguages = ["default", "14", "latest"];

    static string CompileCorpus(string compiler, CompilerToolchain toolchain, string directory,
        string name, IEnumerable<string> sources, string language, IEnumerable<string>? extraReferences = null,
        bool executable = false)
    {
        Directory.CreateDirectory(directory);
        var assembly = Path.Combine(directory, name + ".dll");
        var response = Path.Combine(directory, name + ".rsp");
        var options = new List<string> { "/nologo", executable ? "/target:exe" : "/target:library",
            "/optimize+", "/debug-", "/unsafe+", "/nullable:enable", "/nostdlib+", "/out:" + Quote(assembly) };
        // Omitting the switch exercises the compiler's default, independently of the SDK's TFM policy.
        if (language != "default") options.Add("/langversion:" + language);
        File.WriteAllLines(response, options.Concat(sources.Select(Quote))
            .Concat(Directory.EnumerateFiles(toolchain.References, "*.dll")
                .Concat(extraReferences ?? []).Order(StringComparer.Ordinal).Select(path => "/reference:" + Quote(path))));
        Run(["dotnet", "exec", "--roll-forward", "Major", compiler, "@" + response]);
        return assembly;
    }

    static string Quote(string value) => "\"" + value.Replace('\\', '/') + "\"";

    static string[] CorpusSources(string directory) => Directory.EnumerateFiles(At(directory), "*.cs",
        SearchOption.AllDirectories).Where(path => !Path.GetRelativePath(At(directory), path)
            .Split(Path.DirectorySeparatorChar).Any(part => part is "obj" or "bin"))
        .Order(StringComparer.Ordinal).ToArray();

    static SortedDictionary<string, char> WholeCorpus(string compiler, CompilerToolchain toolchain,
        string directory, string language)
    {
        var results = new SortedDictionary<string, char>(StringComparer.Ordinal);
        var uncheckedEntries = new List<(string Assembly, string Signature, string Reason)>();
        Directory.CreateDirectory(directory);
        var attributes = Path.Combine(directory, "AssemblyInfo.cs");
        File.WriteAllText(attributes, """
            [assembly: System.Reflection.AssemblyVersion("1.0.0.0")]
            [assembly: System.Reflection.AssemblyConfiguration("Release")]
            [assembly: System.Runtime.Versioning.TargetFramework(".NETCoreApp,Version=v10.0")]
            """);
        var implicitUsings = Path.Combine(directory, "GlobalUsings.cs");
        File.WriteAllText(implicitUsings, """
            global using System;
            global using System.Collections.Generic;
            global using System.IO;
            global using System.Linq;
            global using System.Net.Http;
            global using System.Threading;
            global using System.Threading.Tasks;
            """);
        var library = CompileCorpus(compiler, toolchain, directory, "ImportFixture.Lib",
            CorpusSources("Tests/ContractImports/Lib").Append(attributes), language);
        var assemblies = new[]
        {
            CompileCorpus(compiler, toolchain, directory, "Examples",
                CorpusSources("Examples/Assembly").Append(attributes), language),
            library,
            CompileCorpus(compiler, toolchain, directory, "ImportFixture.App",
                CorpusSources("Tests/ContractImports/App").Append(attributes), language, [library]),
            CompileCorpus(compiler, toolchain, directory, "NativeProbe",
                CorpusSources("Tests/NativeProbe").Concat([attributes, implicitUsings]), language,
                [typeof(ModuleDefinition).Assembly.Location], executable: true)
        };
        foreach (var assembly in assemblies)
        {
            using var module = ModuleDefinition.ReadModule(assembly);
            var signatures = module.GetTypes().SelectMany(type => type.Methods).Select(method => method.FullName)
                .Order(StringComparer.Ordinal).ToArray();
            var manifest = assembly + ".entries.json";
            var report = assembly + ".coverage.json";
            File.WriteAllText(manifest, JsonSerializer.Serialize(new
            {
                entries = signatures.Select(signature => new { signature, profile = "scalar" })
            }));
            Run(["dotnet", ExtractorPath, "blockers", assembly, "--manifest", manifest, "--output", report]);
            using var coverage = JsonDocument.Parse(File.ReadAllText(report));
            foreach (var entry in coverage.RootElement.GetProperty("entries").EnumerateArray())
            {
                if (entry.GetProperty("status").GetString() == "notChecked")
                    uncheckedEntries.Add((Path.GetFileNameWithoutExtension(assembly),
                        entry.GetProperty("signature").GetString()!, entry.GetProperty("reason").GetString()!));
                results.Add(Path.GetFileNameWithoutExtension(assembly) + ":" + entry.GetProperty("signature").GetString(),
                    entry.GetProperty("status").GetString() switch
                    {
                        "admitted" => 'A', "blocked" => 'B', "notChecked" => 'N',
                        var status => throw new InvalidDataException("Unexpected coverage status: " + status)
                    });
            }
            Console.WriteLine($"COVERAGE {Path.GetFileNameWithoutExtension(assembly)} {language}: " +
                coverage.RootElement.GetProperty("counts"));
        }
        File.WriteAllLines(Path.Combine(directory, "not-checked.tsv"),
            new[] { "assembly\tmethod\treason" }.Concat(uncheckedEntries.Select(entry =>
                $"{entry.Assembly}\t{entry.Signature}\t{entry.Reason.ReplaceLineEndings(" ")}")));
        foreach (var group in uncheckedEntries.GroupBy(entry => entry.Reason).OrderBy(group => group.Key))
            Console.WriteLine($"NOT CHECKED {language}: {group.Count()} methods: {group.Key}");
        return results;
    }

    static void CheckCoverageBaseline(string directory,
        SortedDictionary<string, SortedDictionary<string, char>> columns, bool update, bool advisory)
    {
        var methods = columns.Values.SelectMany(column => column.Keys).Distinct().Order(StringComparer.Ordinal);
        var lines = new[] { "method\t" + string.Join('\t', columns.Keys) }.Concat(methods.Select(method =>
            method + "\t" + string.Join('\t', columns.Values.Select(column => column.GetValueOrDefault(method, '-')))))
            .ToArray();
        File.WriteAllLines(Path.Combine(directory, "acceptance.tsv"), lines);
        File.WriteAllLines(Path.Combine(directory, "summary.md"),
            new[] { "# Compiler extraction coverage", "", "Admission is not proof success.", "",
                "| Compiler / language | Admitted | Blocked | Not checked |",
                "| --- | ---: | ---: | ---: |" }.Concat(columns.Select(column =>
                $"| {column.Key} | {column.Value.Values.Count(state => state == 'A')} | " +
                $"{column.Value.Values.Count(state => state == 'B')} | " +
                $"{column.Value.Values.Count(state => state == 'N')} |")));
        var baseline = At("Tests/CompilerCoverageBaseline.tsv");
        if (update) File.WriteAllLines(baseline, lines);
        var expected = File.ReadAllLines(baseline);
        if (advisory)
        {
            var oldColumns = expected[0].Split('\t').Skip(1).ToArray();
            var previous = expected.Skip(1).Select(line => line.Split('\t'))
                .ToDictionary(fields => fields[0], fields => fields.Skip(1).ToArray(), StringComparer.Ordinal);
            var lost = new List<string>();
            var gained = new List<string>();
            foreach (var (column, actual) in columns)
            {
                var language = column[(column.IndexOf('/') + 1)..];
                var index = Array.IndexOf(oldColumns, CorpusCompilerVersions[^1] + "/" + language);
                if (index < 0) throw new InvalidDataException("Missing comparison baseline for " + language);
                foreach (var method in previous.Keys.Union(actual.Keys).Order(StringComparer.Ordinal))
                {
                    var wasAdmitted = previous.TryGetValue(method, out var states) && states[index] == "A";
                    var admitted = actual.GetValueOrDefault(method) == 'A';
                    if (wasAdmitted && !admitted) lost.Add(column + ": " + method);
                    if (!wasAdmitted && admitted) gained.Add(column + ": " + method);
                }
            }
            File.WriteAllLines(Path.Combine(directory, "changes.txt"),
                lost.Select(method => "LOST " + method).Concat(gained.Select(method => "GAINED " + method)));
            Console.WriteLine($"Latest compiler: {lost.Count} lost, {gained.Count} gained admissions");
            if (lost.Count != 0) throw new InvalidOperationException(string.Join('\n', lost));
        }
        else if (!expected.SequenceEqual(lines))
            throw new InvalidOperationException("Compiler coverage changed; review acceptance.tsv and use --update.\n" +
                string.Join('\n', lines.Except(expected).Select(line => "+ " + line)
                    .Concat(expected.Except(lines).Select(line => "- " + line)).Take(100)));
    }
}
