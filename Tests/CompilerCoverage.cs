#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include CompilerToolchain.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Text.Json;

if (args.Length != 0) throw new ArgumentException("Usage: CompilerCoverage.cs");
var root = At("artifacts/CompilerCoverage");
Directory.CreateDirectory(root);
var toolchain = RestoreCompilerToolchain();
var source = At("Tests/CompilerCorpus/Corpus.cs");
var sourceHash = Sha(source);
var report = new List<object>();
var failures = new List<string>();
var evidence = new GeneratedEvidence(root);
string[] methods = ["TypeTest", "Throw", "NullInner", "SpanLocal", "SpanSlice", "PointerRead", "Allocate", "Unsupported"];
foreach (var version in CorpusCompilerVersions)
{
    var compiler = Path.Combine(toolchain.Packages, "microsoft.net.compilers.toolset", version,
        "tasks/netcore/bincore/csc.dll");
    var compilerHash = Sha(compiler);
    var directory = Path.Combine(root, version);
    Directory.CreateDirectory(directory);
    var assembly = Path.Combine(directory, "Corpus.dll");
    var response = Path.Combine(directory, "compile.rsp");
    File.WriteAllLines(response, new[] { "/nologo", "/target:library", "/optimize+", "/debug-", "/unsafe+",
        "/langversion:13", "/nostdlib+", "/out:" + Quote(assembly), Quote(source) }
        .Concat(Directory.EnumerateFiles(toolchain.References, "*.dll").Order(StringComparer.Ordinal)
            .Select(path => "/reference:" + Quote(path))));
    Run(["dotnet", "exec", "--roll-forward", "Major", compiler, "@" + response]);
    var compilerVersion = Run(["dotnet", "exec", "--roll-forward", "Major", compiler, "/version"]).Trim();
    foreach (var method in methods)
    {
        var output = Path.Combine(directory, method);
        var result = Execute(["dotnet", ExtractorPath, "extract", assembly, "Corpus::" + method + (method switch
        {
            "SpanLocal" => "(System.Int32&)",
            "SpanSlice" => "(System.Span<System.Int32>,System.Int32)",
            "PointerRead" => "(System.Int32*)",
            _ => "(System.Int32)"
        }), output]);
        var accepted = result.Code == 0;
        var expected = method != "Unsupported";
        report.Add(new { compiler = version, compilerVersion, compilerSha256 = compilerHash,
            sourceSha256 = sourceHash, referencePack = CorpusReferenceVersion, method,
            accepted, expected, diagnostic = accepted ? "" : result.Output.Trim() });
        var unsupported = result.Output.Contains("Unsupported instruction", StringComparison.Ordinal);
        if (accepted != expected || (!expected && !unsupported))
            failures.Add($"Roslyn {version}: {method}: {result.Output}");
        if (accepted) evidence.Add(Path.Combine(output, "Extracted.lean"), $"PASS Roslyn {version}: {method}");
    }
}
File.WriteAllText(Path.Combine(root, "coverage.json"), JsonSerializer.Serialize(report,
    new JsonSerializerOptions { WriteIndented = true }));
if (failures.Count != 0) throw new InvalidOperationException(string.Join(Environment.NewLine, failures));
evidence.Check();
Console.WriteLine($"PASS pinned compiler corpus: {CorpusCompilerVersions.Length} compilers × {methods.Length} cases");

static string Quote(string value) => "\"" + value.Replace("\\", "/") + "\"";
