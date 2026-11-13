#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include GeneratedEvidence.cs
#:include MultiAssemblyFixture.cs
#:include MultiAssemblyGenerics.cs

using System.Text.Json;
using System.Text.Json.Nodes;

// Two SDK-built assemblies: App calls into Lib, and Lib is passed as a pinned `--reference`.
MultiAssemblyFixture fixture = new("MultiAssembly");
string root = fixture.Root;
string[] cli = fixture.Cli;
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
public interface IFlag { static abstract bool IsActive { get; } }
public struct On : IFlag { public static bool IsActive => true; }
public struct Off : IFlag { public static bool IsActive => false; }
public interface IScale { static virtual ulong Scale(ulong x) => x * 2; }
public struct Plain : IScale { }
public interface IScaleTwice : IScale { static ulong IScale.Scale(ulong x) => x * 4; }
public struct Shadowed : IScaleTwice { }
public interface IGet { ulong Get(); }
public struct Holder : IGet { public ulong Value; public ulong Get() => Value + 1; }
public struct GenericOn<T> : IFlag where T : unmanaged { public static bool IsActive => true; }
public struct GenericPlain<T> : IScale where T : unmanaged { }
""";

string Library(string name, string step, string properties = "") =>
    fixture.Build(name, libName, libraryText.Replace("STEP", step), properties);

string lib = Library("Lib", "3 + 1");
// Same identity with a different body, and the same body under a different version.
string substitute = Library("Substitute", "3 + 2");
string versioned = Library("Versioned", "3 + 1", "<AssemblyVersion>2.0.0.0</AssemblyVersion>");
// An assembly App references but extraction never pins.
fixture.Build("Other", "MultiFixture.Other", "namespace MultiFixture.Other;\npublic interface IMarker { }\n");
string appDirectory = fixture.Project("App", "MultiFixture.App", "",
    """<ProjectReference Include="../Lib/Lib.csproj" /><ProjectReference Include="../Other/Other.csproj" />""");
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
    public static ulong Run<TFlag>(ulong x) where TFlag : struct, IFlag => TFlag.IsActive ? Mix.Step(x) : x;
    public static ulong Scaled<T>(ulong x) where T : struct, IScale => T.Scale(x);
    public static ulong Got(ulong x) { Holder holder = default; holder.Value = x; return Use(ref holder); }
    static ulong Use<T>(ref T value) where T : struct, IGet => value.Get();
    public static ulong Mine(ulong x) => Scaled<AppScale>(x);
    public static ulong RunGenericOn(ulong x) => Run<GenericOn<uint>>(x);
    public static ulong RunAppGenericOff(ulong x) => Run<AppGenericOff<uint>>(x);
    public static ulong ScaledGenericPlain(ulong x) => Scaled<GenericPlain<uint>>(x);
}
// App structs and interfaces built on Lib's interfaces: dispatch reads both pinned assemblies.
public struct AppScale : IScale { public static ulong Scale(ulong x) => x + 9; }
public struct AppOn : IFlag { public static bool IsActive => true; }
public struct AppOff : IFlag { public static bool IsActive => false; }
public struct AppPlain : IScale { }
public interface IAppScale : IScale { static ulong IScale.Scale(ulong x) => x * 4; }
public struct AppDerived : IAppScale { }
public struct Marked : IScale, MultiFixture.Other.IMarker { }
public struct AppGenericOff<T> : IFlag where T : unmanaged { public static bool IsActive => false; }
""");
Run(["dotnet", "build", Path.Combine(appDirectory, "App.csproj"), "-c", "Release"]);
string app = Path.Combine(appDirectory, "bin", "MultiFixture.App.dll");
string libSha = Sha(lib);
if (Sha(substitute) == libSha)
    throw new InvalidOperationException("Precondition: the substitute must differ from the pinned reference.");

string Artifact(string name) => fixture.Artifact(name);
string[] Reference(string path) => MultiAssemblyFixture.Reference(path);
// One Lean check covers every accepted case; `leancil verify` runs only where its recheck is tested.
GeneratedEvidence evidence = new(Path.Combine(root, "accepted"));

string Extract(string name, string selector, bool referencedBody, string[] extra)
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
        extracted.Contains("assembly := assembly1 }", StringComparison.Ordinal) != referencedBody)
        throw new InvalidOperationException("Certificate misattributes the referenced assembly's bodies: " + name);
    // The certificate depends on the program alone; byte hashes and MVIDs stay in identity.json.
    string[] rebuildSensitive = [libSha, Sha(app), pin.GetProperty("mvid").GetString()!,
        identity.GetProperty("mvid").GetString()!];
    if (rebuildSensitive.Any(value => extracted.Contains(value, StringComparison.OrdinalIgnoreCase)))
        throw new InvalidOperationException("Extracted.lean depends on assembly bytes: " + name);
    return extracted;
}

// The certificate and its proof module, without its import, join the batch.
void Proved(string name, string selector, string proof, bool referencedBody, params string[] extra)
{
    string path = Path.Combine(root, "accepted-" + name + ".lean");
    File.WriteAllText(path, Extract(name, selector, referencedBody, extra) + "\n" +
        File.ReadAllText(At(proof)).Replace("import Extracted", "", StringComparison.Ordinal));
    evidence.Add(path, "PASS cross-assembly " + name + ": pinned reference, attributed body and proof");
}

// The CLI path: `check` rehashes the pinned reference and regenerates the certificate first.
void Verified(string name, string selector, string proof, bool referencedBody, params string[] extra)
{
    _ = Extract(name, selector, referencedBody, extra);
    Run([.. cli, "verify", Artifact(name), "--proof", At(proof), "--theorem", "MultiAssemblyProof.correctness"]);
    Console.WriteLine("PASS cross-assembly " + name + ": verified through the CLI");
}

// Each constant flag decides whether Lib's `Mix.Step` is extracted at all.
void Decided(params (string Name, bool Stepped)[] runs)
{
    foreach ((string name, bool stepped) in runs)
        if (File.ReadAllText(Path.Combine(Artifact(name), "Extracted.lean"))
                .Contains("::MultiFixture.Mix\"", StringComparison.Ordinal) != stepped)
            throw new InvalidOperationException("Constant flag did not decide which branch is extracted: " + name);
}

Verified("Direct", "MultiFixture.Application::Direct(ulong)", "Tests/MultiAssembly/Direct.lean", referencedBody: true);
Proved("Nested", "MultiFixture.Application::Nested(ulong)", "Tests/MultiAssembly/Nested.lean", referencedBody: true);
Proved("Local", "MultiFixture.Application::Local(ulong)", "Tests/MultiAssembly/Local.lean", referencedBody: true);
// Only the layout comes from Lib here, so no body is attributed to it.
Proved("Size", "MultiFixture.Application::Size(ulong)", "Tests/MultiAssembly/Size.lean", referencedBody: false,
    "--type-argument", "MultiFixture.Cell, " + libName);

// Constrained static dispatch to flag structs declared in Lib; each constant getter folds its branch away.
const string run = "MultiFixture.Application::Run(ulong)";
Proved("RunOff", run, "Tests/MultiAssembly/RunOff.lean", referencedBody: true,
    "--type-argument", "MultiFixture.Off, " + libName);
Proved("RunOn", run, "Tests/MultiAssembly/RunOn.lean", referencedBody: true,
    "--type-argument", "MultiFixture.On, " + libName);
Decided(("RunOff", false), ("RunOn", true));
// A Lib interface's static virtual default body, and an instance slot reached through a Lib struct.
Proved("Scaled", "MultiFixture.Application::Scaled(ulong)", "Tests/MultiAssembly/Scaled.lean",
    referencedBody: true, "--type-argument", "MultiFixture.Plain, " + libName);
Proved("Got", "MultiFixture.Application::Got(ulong)", "Tests/MultiAssembly/Got.lean", referencedBody: true);
// Lib's derived interface re-implements its own default, which the runtime prefers.
const string scaled = "MultiFixture.Application::Scaled(ulong)";
Proved("Shadowed", scaled, "Tests/MultiAssembly/Quadrupled.lean", referencedBody: true,
    "--type-argument", "MultiFixture.Shadowed, " + libName);

// App structs implementing Lib interfaces: App's own getter and Scale, Lib's default body and App's derived
// interface body. Each constant App getter decides which branch is extracted, as a Lib one does.
Proved("RunAppOn", run, "Tests/MultiAssembly/RunOn.lean", referencedBody: true,
    "--type-argument", "MultiFixture.AppOn");
Proved("RunAppOff", run, "Tests/MultiAssembly/RunOff.lean", referencedBody: false,
    "--type-argument", "MultiFixture.AppOff");
Decided(("RunAppOff", false), ("RunAppOn", true));
Proved("Mine", "MultiFixture.Application::Mine(ulong)", "Tests/MultiAssembly/Mine.lean", referencedBody: false);
Proved("ScaledAppPlain", scaled, "Tests/MultiAssembly/Scaled.lean", referencedBody: true,
    "--type-argument", "MultiFixture.AppPlain");
Proved("ScaledAppDerived", scaled, "Tests/MultiAssembly/Quadrupled.lean", referencedBody: false,
    "--type-argument", "MultiFixture.AppDerived");

// Closed generic struct receivers of either assembly: a Lib flag and an App flag, each closed at its type
// argument, fold their branch, and a Lib generic struct runs Lib's default body.
Proved("RunGenericOn", "MultiFixture.Application::RunGenericOn(ulong)", "Tests/MultiAssembly/RunOn.lean",
    referencedBody: true);
Proved("RunAppGenericOff", "MultiFixture.Application::RunAppGenericOff(ulong)",
    "Tests/MultiAssembly/RunOff.lean", referencedBody: false);
Decided(("RunAppGenericOff", false), ("RunGenericOn", true));
Proved("ScaledGenericPlain", "MultiFixture.Application::ScaledGenericPlain(ulong)",
    "Tests/MultiAssembly/Scaled.lean", referencedBody: true);

evidence.Check();

void Rejected(string name, string marker, string[] command) => MultiAssemblyFixture.Rejected(name, marker, command);

string RejectedExtract(string name, string marker, string selector, params string[] extra) =>
    fixture.RejectedExtract(name, marker, app, selector, extra);

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
// An interface of an unpinned assembly could hide a more specific body, so the default is not selected.
RejectedExtract("unpinned receiver interface", "Unpinned assembly reference: MultiFixture.Other",
    scaled, [.. Reference(lib), "--type-argument", "MultiFixture.Marked"]);

// A pinned type its assembly does not define has no definition to link, unlike a custom modifier, which needs none.
string gone = fixture.Build("Gone", libName, libraryText.Replace("STEP", "3 + 1")
    .Replace("public struct Cell { public ulong Value; }\n", "")
    .Replace("    public static void Bump(ref Cell cell) => cell.Value = Step(cell.Value);\n", ""));
RejectedExtract("pinned type without definition", "Unresolved pinned type", "MultiFixture.Application::Local(ulong)",
    Reference(gone));

// Proofs bind bodies by unscoped signature, so a same-named type in two pinned assemblies is rejected.
string aliasDirectory = fixture.Project("Alias", "MultiFixture.Alias", "",
    """<ProjectReference Include="../Lib/Lib.csproj" Aliases="lib" />""");
File.WriteAllText(Path.Combine(aliasDirectory, "Twin.cs"), """
extern alias lib;
namespace MultiFixture;
public static class Mix { public static ulong Step(ulong x) => x + 7; }
public static class Twin { public static ulong Both(ulong x) => lib::MultiFixture.Mix.Step(x) + Mix.Step(x); }
""");
Run(["dotnet", "build", Path.Combine(aliasDirectory, "Alias.csproj"), "-c", "Release"]);
Rejected("ambiguous signature", "Ambiguous method signature across pinned assemblies",
    [.. cli, "extract", Path.Combine(aliasDirectory, "bin", "MultiFixture.Alias.dll"),
        "MultiFixture.Twin::Both(ulong)", Path.Combine(root, "r-ambiguous"), .. Reference(lib)]);

// Each tampered copy starts from a verified artifact; `verify` must recheck every pinned reference.
string Copy(string name, string source = "Direct")
{
    string copy = Path.Combine(root, "t-" + name);
    Directory.CreateDirectory(copy);
    foreach (string file in Directory.EnumerateFiles(Artifact(source)))
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

// `check` regenerates the certificate and hashes the bytes; Lean rejects a misattributed body.
string extractedSource = File.ReadAllText(Path.Combine(Artifact("Direct"), "Extracted.lean"));
string libIdentity = libName + ", Version=0.1.0.0" + unsigned;
string appIdentity = "MultiFixture.App, Version=0.1.0.0" + unsigned;
if (!extractedSource.Contains($"identity := \"{libIdentity}\"", StringComparison.Ordinal))
    throw new InvalidOperationException("Precondition: the certificate must pin " + libIdentity);
foreach ((string name, string from, string to) in new[]
{
    ("misattributed body", "assembly := assembly1 }", "assembly := assembly0 }"),
    ("duplicate certificate identity", $"identity := \"{libIdentity}\"", $"identity := \"{appIdentity}\"")
})
{
    string forged = Copy(name.Replace(' ', '-'));
    string lean = Path.Combine(forged, "Extracted.lean");
    File.WriteAllText(lean, extractedSource.Replace(from, to, StringComparison.Ordinal));
    Rejected(name, "Stale", Verify(forged));
    (int Code, string Output, string Stdout, string Stderr) kernel =
        Execute(["lake", "env", "lean", lean], cwd: FixturePackage());
    if (kernel.Code == 0 || !kernel.Output.Contains("Extraction.AttributionValid", StringComparison.Ordinal))
        throw new InvalidOperationException($"Lean accepted the forged certificate {name}: {kernel.Output}");
    Console.WriteLine("PASS Lean rejected " + name);
}
// A dispatch catalog that moves the Lib interface into App no longer resolves the Lib receiver's slot.
string catalogued = Copy("Catalog", "RunOn");
string catalog = Path.Combine(catalogued, "Extracted.lean");
string[] catalogLines = File.ReadAllLines(catalog);
int dispatch = Array.FindIndex(catalogLines,
    line => line.StartsWith("def method0DispatchTypes", StringComparison.Ordinal));
if (dispatch < 0 || !catalogLines[dispatch].Contains(libIdentity, StringComparison.Ordinal))
    throw new InvalidOperationException("Precondition: Run<On> must catalog the Lib flag interface.");
catalogLines[dispatch] = catalogLines[dispatch].Replace(libIdentity, appIdentity, StringComparison.Ordinal);
File.WriteAllLines(catalog, catalogLines);
Rejected("moved dispatch catalog", "Stale", [.. cli, "verify", catalogued, "--proof",
    At("Tests/MultiAssembly/RunOn.lean"), "--theorem", "MultiAssemblyProof.correctness"]);
(int Code, string Output, string Stdout, string Stderr) moved =
    Execute(["lake", "env", "lean", catalog], cwd: FixturePackage());
if (moved.Code == 0 || !moved.Output.Contains("ConstrainedCallsValid", StringComparison.Ordinal))
    throw new InvalidOperationException("Lean accepted a dispatch catalog moved to another assembly: " + moved.Output);
Console.WriteLine("PASS Lean rejected moved dispatch catalog");
// The App receiver's catalog reads Lib's IScale entry; attributing that entry to App's pin fails dispatch.
string repinned = Copy("Repinned", "ScaledAppDerived");
string repinnedCatalog = Path.Combine(repinned, "Extracted.lean");
string libPinText = $"assembly := {{ identity := \"{libIdentity}\" }}";
string repinnedSource = File.ReadAllText(repinnedCatalog);
if (!repinnedSource.Contains(libPinText, StringComparison.Ordinal))
    throw new InvalidOperationException("Precondition: Scaled<AppDerived> must catalog a Lib entry.");
File.WriteAllText(repinnedCatalog, repinnedSource.Replace(libPinText,
    $"assembly := {{ identity := \"{appIdentity}\" }}", StringComparison.Ordinal));
(int Code, string Output, string Stdout, string Stderr) repinnedKernel =
    Execute(["lake", "env", "lean", repinnedCatalog], cwd: FixturePackage());
if (repinnedKernel.Code == 0 || !repinnedKernel.Output.Contains("ConstrainedCallsValid", StringComparison.Ordinal))
    throw new InvalidOperationException("Lean accepted a catalog entry outside its pin: " + repinnedKernel.Output);
Console.WriteLine("PASS Lean rejected catalog entry attributed to another pin");
// A well-formed sidecar for Lib: the explicit import is rejected because Lib is also a pinned reference.
JsonObject contract = JsonNode.Parse(File.ReadAllText(At("Tests/ContractImports/Lib.leancil.contracts")))!.AsObject();
IEnumerable<string> framework = Directory.EnumerateFiles(At("CIL"), "*.lean", SearchOption.AllDirectories)
    .Append(At("CIL.lean")).Append(At("lean-toolchain"));
contract["frameworkKey"] = ContentKey(string.Join("\n", framework
    .Select(path => (Name: Path.GetRelativePath(Root, path).Replace('\\', '/'), Path: path))
    .OrderBy(item => item.Name, StringComparer.Ordinal).Select(item => item.Name + "=" + Sha(item.Path))));
JsonElement libPin = JsonSerializer.Deserialize<JsonElement>(
    File.ReadAllText(Path.Combine(Artifact("Direct"), "identity.json"))).GetProperty("references")[0];
string placeholder = new('0', 64);
string export = libIdentity + "::System.UInt64 MultiFixture.Mix::Step(System.UInt64)";
contract["assemblyIdentity"] = libIdentity;
contract["mvid"] = libPin.GetProperty("mvid").GetString();
contract["implementationSha256"] = libSha;
contract["interfaceModules"]![0]!["name"] = "LibContract";
contract["interfaceModules"]![0]!["source"] = "-- not compiled: extraction rejects the import first";
contract["exports"]![0]!["identity"] = export;
contract["exports"]![0]!["closureDigest"] = placeholder;
contract["certifications"]![0]!["identity"] = export;
contract["certifications"]![0]!["closureDigest"] = placeholder;
contract["certifications"]![0]!["implementationSha256"] = libSha;
JsonObject descriptor = [];
foreach (string field in new[] { "schema", "semanticsVersion", "formatVersion", "frameworkKey", "assemblyIdentity",
    "targetFramework", "interfaceModules", "exports", "dependencies" })
    descriptor[field] = contract[field]!.DeepClone();
string interfaceDigest = ContentKey(descriptor.ToJsonString());
contract["interfaceDigest"] = interfaceDigest;
contract["certifications"]![0]!["interfaceDigest"] = interfaceDigest;
string libSidecar = Path.Combine(root, libName + ".leancil.contracts");
File.WriteAllText(libSidecar, contract.ToJsonString());
string[] import = ["--import", libSidecar, "--import-sha256", libName + "=" + libSha,
    "--import-interface-sha256", libName + "=" + interfaceDigest];
// Without the pin the same sidecar passes reading, so the rejection below is the conflict itself.
(int Code, string Output, string Stdout, string Stderr) imported =
    Execute([.. cli, "extract", app, direct, Path.Combine(root, "r-import-only"), .. import]);
if (imported.Output.Contains("framework key mismatch", StringComparison.Ordinal) ||
    imported.Output.Contains("Invalid contract", StringComparison.Ordinal) ||
    imported.Output.Contains("cannot be both", StringComparison.Ordinal))
    throw new InvalidOperationException("Precondition: the Lib sidecar must read as a contract: " + imported.Output);
RejectedExtract("import and reference", "An assembly cannot be both a typed import and an extracted reference",
    direct, [.. import, .. Reference(lib)]);
Console.WriteLine("PASS pinned referenced assemblies: proofs, missing, duplicate, substituted, misattributed");

// Generic structs and generic class statics run in the same job with their own Lib and App.
CheckGenericAssemblies();
