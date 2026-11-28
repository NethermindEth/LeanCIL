#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include CompilerToolchain.cs
#:include CompilerCorpusCoverage.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Text.Json;
using Mono.Cecil;

if (args.Any(argument => argument is not ("--update" or "--latest" or "--whole-only" or "--all-compilers")))
    throw new ArgumentException("Usage: CompilerCoverage.cs [--update] [--latest] [--whole-only] [--all-compilers]");
var advisory = args.Contains("--latest");
var allCompilers = args.Contains("--all-compilers");
if (advisory && args.Contains("--update")) throw new ArgumentException("Latest runs cannot update pinned baselines.");
var versions = allCompilers ? CorpusCompilerVersions : [LatestPinnedCompilerVersion];
var selectedLanguages = allCompilers ? CorpusLanguages : [DefaultCorpusLanguage];
if (advisory)
{
    using var http = new HttpClient();
    using var index = JsonDocument.Parse(await http.GetStringAsync(
        "https://api.nuget.org/v3-flatcontainer/microsoft.net.compilers.toolset/index.json"));
    versions = [index.RootElement.GetProperty("versions").EnumerateArray().Select(item => item.GetString()!)
        .Where(version => Version.TryParse(version, out _)).MaxBy(Version.Parse)!];
}
var root = At(advisory ? "artifacts/CompilerCoverageLatest" : "artifacts/CompilerCoverage");
Directory.CreateDirectory(root);
var toolchain = RestoreCompilerToolchain(versions);
var source = At("Tests/CompilerCorpus/Corpus.cs");
var sourceHash = Sha(source);
var report = new List<object>();
var failures = new List<string>();
var evidence = new GeneratedEvidence(root);
var checkedEvidence = new HashSet<string>(StringComparer.Ordinal);
var columns = new SortedDictionary<string, SortedDictionary<string, char>>(StringComparer.Ordinal);
foreach (var version in versions)
{
    var compiler = Path.Combine(toolchain.Packages, "microsoft.net.compilers.toolset", version,
        "tasks/netcore/bincore/csc.dll");
    var compilerHash = Sha(compiler);
    var compilerVersion = Run(["dotnet", "exec", "--roll-forward", "Major", compiler, "/version"]).Trim();
    var languages = Run(["dotnet", "exec", "--roll-forward", "Major", compiler, "/langversion:?"]);
    foreach (var language in selectedLanguages)
    {
        if (language == "14" && !languages.Split('\n').Any(line => line.Trim().StartsWith("14.0")))
        {
            report.Add(new { compiler = version, language, status = "language unavailable" });
            continue;
        }
        var directory = Path.Combine(root, version, language);
        columns.Add(version + "/" + language, WholeCorpus(compiler, toolchain, directory, language));
        report.Add(new { compiler = version, language, compilerVersion, compilerSha256 = compilerHash,
            referencePack = CorpusReferenceVersion, methods = columns[version + "/" + language].Count });
        if (args.Contains("--whole-only")) continue;
        var assembly = CompileCorpus(compiler, toolchain, directory, "Corpus", [source], language);
        using var module = ModuleDefinition.ReadModule(assembly);
        var cases = module.GetType("Corpus").Methods.Where(method => method.IsPublic)
            .Select(method => (Method: method, Output: Path.Combine(directory, method.Name),
                Expected: method.Name != "Unsupported")).ToArray();
        var positive = cases.Where(item => item.Expected)
            .Select(item => new GeneratedExtraction(assembly, item.Method.FullName, item.Output));
        var batchPassed = true;
        try { ExtractBatch("extract", null, positive); }
        catch (InvalidOperationException error)
        {
            // Keep the batch failure and collect each method's diagnostic for the coverage report.
            failures.Add($"Roslyn {version}/{language} extraction batch: {error.Message}");
            batchPassed = false;
        }
        foreach (var (method, output, expected) in cases)
        {
            var accepted = true;
            var diagnostic = "";
            if (!expected || !batchPassed)
            {
                var result = Execute(["dotnet", ExtractorPath, "extract", assembly, method.FullName, output]);
                accepted = result.Code == 0;
                diagnostic = result.Output.Trim();
            }
            report.Add(new { compiler = version, language, compilerVersion, compilerSha256 = compilerHash,
                sourceSha256 = sourceHash, referencePack = CorpusReferenceVersion, method = method.FullName,
                accepted, expected, diagnostic = accepted ? "" : diagnostic });
            var unsupported = diagnostic.Contains("Unsupported instruction", StringComparison.Ordinal);
            if (accepted != expected || (!expected && !unsupported))
                failures.Add($"Roslyn {version}/{language}: {method.Name}: {diagnostic}");
            if (accepted)
            {
                var generated = Path.Combine(output, "Extracted.lean");
                if (checkedEvidence.Add(Sha(generated)))
                    evidence.Add(generated, $"PASS Roslyn {version}/{language}: {method.Name}");
            }
        }
    }
}
File.WriteAllText(Path.Combine(root, "coverage.json"), JsonSerializer.Serialize(report,
    new JsonSerializerOptions { WriteIndented = true }));
CheckCoverageBaseline(root, columns, args.Contains("--update"), advisory, allCompilers);
if (failures.Count != 0) throw new InvalidOperationException(string.Join(Environment.NewLine, failures));
if (!args.Contains("--whole-only")) evidence.Check();
Console.WriteLine($"PASS compiler coverage: {columns.Count} compiler/language columns; " +
    $"{checkedEvidence.Count} distinct targeted certificates");
