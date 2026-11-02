#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Text.Json;
using System.Text.Json.Nodes;

// Two SDK-built assemblies: App calls into Lib, and Lib is passed as a pinned `--reference`.
string root = At("artifacts/MultiAssembly-" + Guid.NewGuid().ToString("N"));
string[] cli = ["dotnet", ExtractorPath];
const string libName = "MultiFixture.Lib";
const string unsigned = ", Culture=neutral, PublicKeyToken=null";
const string libraryText = """
namespace MultiFixture;
public struct Cell { public ulong Value; }
public static class Mix
{
    public static ulong Step(ulong x) => x * STEP;
    public static ulong Twice(ulong x) => Step(Step(x));
    public static void Bump(ref Cell cell) => cell.Value = Step(cell.Value);
}
public static class Seeded
{
    static Seeded() { System.GC.KeepAlive(new object()); }
    public static ulong Get(ulong x) => x;
}
""";

string Project(string name, string assembly, string properties = "", string references = "")
{
    string directory = Path.Combine(root, name);
    Directory.CreateDirectory(directory);
    File.WriteAllText(Path.Combine(directory, name + ".csproj"), $"""
        <Project Sdk="Microsoft.NET.Sdk"><PropertyGroup><TargetFramework>net10.0</TargetFramework>
        <AssemblyName>{assembly}</AssemblyName><Optimize>true</Optimize>{properties}</PropertyGroup>
        <ItemGroup>{references}</ItemGroup></Project>
        """);
    return directory;
}

string Library(string name, string step, string properties = "")
{
    string directory = Project(name, libName, properties);
    File.WriteAllText(Path.Combine(directory, "Library.cs"), libraryText.Replace("STEP", step));
    Run(["dotnet", "build", Path.Combine(directory, name + ".csproj"), "-c", "Release"]);
    return Path.Combine(directory, "bin", libName + ".dll");
}

string lib = Library("Lib", "3 + 1");
// Same identity with a different body, and the same body under a different version.
string substitute = Library("Substitute", "3 + 2");
string versioned = Library("Versioned", "3 + 1", "<AssemblyVersion>2.0.0.0</AssemblyVersion>");
string appDirectory = Project("App", "MultiFixture.App", "",
    """<ProjectReference Include="../Lib/Lib.csproj" />""");
File.WriteAllText(Path.Combine(appDirectory, "Application.cs"), """
using System.Runtime.CompilerServices;
namespace MultiFixture;
public static class Application
{
    public static ulong Direct(ulong x) => Mix.Step(x) + 1;
    public static ulong Nested(ulong x) => Mix.Twice(x);
    public static ulong Local(ulong x) { Cell cell = default; cell.Value = x; Mix.Bump(ref cell); return cell.Value; }
    public static ulong Size<T>(ulong x) where T : struct => x + (ulong)Unsafe.SizeOf<T>();
    public static ulong Seeded(ulong x) => MultiFixture.Seeded.Get(x);
}
""");
Run(["dotnet", "build", Path.Combine(appDirectory, "App.csproj"), "-c", "Release"]);
string app = Path.Combine(appDirectory, "bin", "MultiFixture.App.dll");
string libSha = Sha(lib);
if (Sha(substitute) == libSha)
    throw new InvalidOperationException("Precondition: the substitute must differ from the pinned reference.");

string Artifact(string name) => Path.Combine(root, "x-" + name);
string[] Reference(string path) => ["--reference", path];

void Proved(string name, string selector, string proof, bool referencedBody, params string[] extra)
{
    string artifact = Artifact(name);
    Run([.. cli, "extract", app, selector, artifact, .. Reference(lib), .. extra]);
    JsonElement identity =
        JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(artifact, "identity.json")));
    JsonElement pin = identity.GetProperty("references").EnumerateArray().Single();
    if (pin.GetProperty("sha256").GetString() != libSha ||
        !pin.GetProperty("assemblyIdentity").GetString()!.StartsWith(libName + ",", StringComparison.Ordinal))
        throw new InvalidOperationException("Artifact did not record the pinned reference: " + pin);
    string extracted = File.ReadAllText(Path.Combine(artifact, "Extracted.lean"));
    if (!extracted.Contains("def assembly1 : Extraction.AssemblyPin", StringComparison.Ordinal) ||
        !extracted.Contains($"sha256 := \"{libSha}\"", StringComparison.Ordinal) ||
        extracted.Contains("assembly := assembly1", StringComparison.Ordinal) != referencedBody)
        throw new InvalidOperationException("Certificate misattributes the referenced assembly's bodies: " + name);
    Run([.. cli, "verify", artifact, "--proof", At(proof),
        "--theorem", "MultiAssemblyProof.correctness"]);
    Console.WriteLine("PASS cross-assembly " + name + ": pinned reference, attributed body and proof");
}

Proved("Direct", "MultiFixture.Application::Direct(ulong)", "Tests/MultiAssembly/Direct.lean", referencedBody: true);
Proved("Nested", "MultiFixture.Application::Nested(ulong)", "Tests/MultiAssembly/Nested.lean", referencedBody: true);
Proved("Local", "MultiFixture.Application::Local(ulong)", "Tests/MultiAssembly/Local.lean", referencedBody: true);
// Only the layout comes from Lib here, so no body is attributed to it.
Proved("Size", "MultiFixture.Application::Size(ulong)", "Tests/MultiAssembly/Size.lean", referencedBody: false,
    "--type-argument", "MultiFixture.Cell, " + libName);

void Rejected(string name, string marker, string[] command)
{
    (int Code, string Output, string Stdout, string Stderr) result = Execute(command);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new InvalidOperationException($"Expected rejection {name} ({marker}): {result.Output}");
    Console.WriteLine("PASS rejected " + name);
}

string RejectedExtract(string name, string marker, string selector, params string[] extra)
{
    string output = Path.Combine(root, "r-" + name);
    Rejected(name, marker, [.. cli, "extract", app, selector, output, .. extra]);
    if (File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Rejected extraction left a certificate: " + name);
    return output;
}

const string direct = "MultiFixture.Application::Direct(ulong)";
// Cecil's ambient resolver would find Lib beside App; without a pin the call stays external.
RejectedExtract("missing reference", "External managed dependency", direct);
RejectedExtract("duplicate reference", "Duplicate pinned assembly identity", direct,
    [.. Reference(lib), .. Reference(lib)]);
RejectedExtract("version mismatch", "Pinned assembly does not match its reference", direct, Reference(versioned));
RejectedExtract("platform reference", "Platform assemblies are runtime models",
    direct, [.. Reference(lib), .. Reference(typeof(object).Assembly.Location)]);
RejectedExtract("referenced static initialiser", "Unsupported static initialisation in a referenced assembly",
    "MultiFixture.Application::Seeded(ulong)", Reference(lib));
RejectedExtract("unpinned entry type argument", "no single pinned --reference assembly",
    "MultiFixture.Application::Size(ulong)", "--type-argument", "MultiFixture.Cell, Other");

// Each tampered copy starts from a verified artifact; `verify` must recheck every pinned reference.
string Copy(string name)
{
    string copy = Path.Combine(root, "t-" + name);
    Directory.CreateDirectory(copy);
    foreach (string file in Directory.EnumerateFiles(Artifact("Direct")))
        File.Copy(file, Path.Combine(copy, Path.GetFileName(file)));
    return copy;
}

string[] Verify(string artifact) => [.. cli, "verify", artifact, "--proof", At("Tests/MultiAssembly/Direct.lean"),
    "--theorem", "MultiAssemblyProof.correctness"];

void Edit(string path, Action<JsonObject> change)
{
    JsonObject document = JsonNode.Parse(File.ReadAllText(path))!.AsObject();
    change(document);
    File.WriteAllText(path, document.ToJsonString());
}

string pinnedPath = Path.Combine(root, "Pinned", libName + ".dll");
Directory.CreateDirectory(Path.GetDirectoryName(pinnedPath)!);
File.Copy(lib, pinnedPath);
string swapped = Path.Combine(root, "x-Swapped");
Run([.. cli, "extract", app, direct, swapped, .. Reference(pinnedPath)]);
Run([.. cli, "verify", swapped, "--proof", At("Tests/MultiAssembly/Direct.lean"),
    "--theorem", "MultiAssemblyProof.correctness"]);
File.Copy(substitute, pinnedPath, overwrite: true);
Rejected("substituted reference", "Referenced assembly hash mismatch", Verify(swapped));

string hashed = Copy("Hash");
Edit(Path.Combine(hashed, "identity.json"), identity =>
    identity["references"]![0]!["sha256"] = new string('0', 64));
Rejected("changed reference hash", "Referenced assembly hash mismatch", Verify(hashed));

string renamed = Copy("Identity");
Edit(Path.Combine(renamed, "identity.json"), identity =>
    identity["references"]![0]!["assemblyIdentity"] = libName + ", Version=9.0.0.0" + unsigned);
Rejected("changed reference identity", "is not the recorded " + libName + ", Version=9.0.0.0", Verify(renamed));

string dropped = Copy("Dropped");
Edit(Path.Combine(dropped, "identity.json"), identity => identity["references"] = new JsonArray());
Rejected("dropped reference", "External managed dependency", Verify(dropped));

// `check` regenerates the certificate. Lean rejects inconsistent pins; only `check` hashes the bytes.
string extractedSource = File.ReadAllText(Path.Combine(Artifact("Direct"), "Extracted.lean"));
string libIdentity = libName + ", Version=0.1.0.0" + unsigned;
string appIdentity = "MultiFixture.App, Version=0.1.0.0" + unsigned;
if (!extractedSource.Contains($"identity := \"{libIdentity}\"", StringComparison.Ordinal))
    throw new InvalidOperationException("Precondition: the certificate must pin " + libIdentity);
foreach ((string name, string from, string to, bool leanRejects) in new[]
{
    ("misattributed body", "assembly := assembly1", "assembly := assembly0", true),
    ("duplicate certificate identity", $"identity := \"{libIdentity}\"", $"identity := \"{appIdentity}\"", true),
    ("changed certificate hash", $"sha256 := \"{libSha}\"", $"sha256 := \"{new string('0', 64)}\"", false)
})
{
    string forged = Copy(name.Replace(' ', '-'));
    string lean = Path.Combine(forged, "Extracted.lean");
    File.WriteAllText(lean, extractedSource.Replace(from, to, StringComparison.Ordinal));
    Rejected(name, "Stale", Verify(forged));
    if (!leanRejects) continue;
    (int Code, string Output, string Stdout, string Stderr) kernel =
        Execute(["lake", "env", "lean", lean], cwd: FixturePackage());
    if (kernel.Code == 0 || !kernel.Output.Contains("Extraction.AssemblyPinsValid", StringComparison.Ordinal))
        throw new InvalidOperationException($"Lean accepted the forged certificate {name}: {kernel.Output}");
    Console.WriteLine("PASS Lean rejected " + name);
}
Console.WriteLine("PASS pinned referenced assemblies: proofs, missing, duplicate, substituted, misattributed");
