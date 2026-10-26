#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

using System.Collections;
using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;

var assembly = Assembly.LoadFrom(ExtractorPath);
var contractType = assembly.GetType("Nethermind.LeanCIL.ContractInterface", true)!;
var resolutionType = assembly.GetType("Nethermind.LeanCIL.ImportResolution", true)!;
var libraryType = resolutionType.GetNestedType("Library", BindingFlags.NonPublic)!;
const BindingFlags hiddenStatic = BindingFlags.Static | BindingFlags.NonPublic;
const BindingFlags hiddenInstance = BindingFlags.Instance | BindingFlags.NonPublic;
var json = (JsonSerializerOptions)contractType.GetField("Json", hiddenStatic)!.GetValue(null)!;
var read = contractType.GetMethod("Read", hiddenStatic)!;
object Read(JsonObject value) => read.Invoke(null, [JsonSerializer.SerializeToUtf8Bytes(value)])!;
var savedBaseDirectory = AppContext.GetData("APP_CONTEXT_BASE_DIRECTORY");
try
{
    AppContext.SetData("APP_CONTEXT_BASE_DIRECTORY", Path.GetDirectoryName(Path.GetFullPath(ExtractorPath)) +
        Path.DirectorySeparatorChar);
    var framework = contractType.GetMethod("CurrentFrameworkKey", hiddenStatic)!.Invoke(null, null);
    var digest = new string('0', 64);
    var exports = new[] { "Method", "method" }.Select(identity => new
    {
        Identity = identity, Signature = "System.Void Fixture::" + identity + "()", ParameterCount = 0,
        HasThis = false, ReturnsValue = false, Visibility = "public", ContractConstant = "Published.contract",
        ClosureDigest = digest, Profiles = new[] { "scalar", "x64-v3" }, Kind = "method"
    }).ToArray();
    var certifications = exports.SelectMany(export => export.Profiles.Select(profile => new
    {
        export.Identity, Profile = profile, ImplementationSha256 = digest, InterfaceDigest = digest,
        ClosureDigest = digest, Theorem = "Published.correct", Statement = "True", StatementDigest = digest,
        StaticIdentities = Array.Empty<object>()
    })).ToArray();
    var contract = JsonSerializer.Deserialize(JsonSerializer.Serialize(new
    {
        Schema = 1, SemanticsVersion = 1, FormatVersion = 1, FrameworkKey = framework,
        AssemblyIdentity = "Fixture", Mvid = Guid.NewGuid(), TargetFramework = ".NETCoreApp,Version=v10.0",
        ImplementationSha256 = digest, IsReferenceAssembly = false,
        InterfaceModules = new[] { new { Name = "Published", Source = "namespace Published\nend Published\n" } },
        InterfaceDigest = digest, Exports = exports, Certifications = certifications,
        Dependencies = Array.Empty<object>()
    }, json), contractType, json)!;
    var value = JsonSerializer.SerializeToNode(contract, contractType, json)!.AsObject();
    value["interfaceDigest"] = (string)contractType.GetMethod("ComputeInterfaceDigest", hiddenInstance)!
        .Invoke(contract, null)!;
    contract = Read(value);
    var library = Activator.CreateInstance(libraryType, BindingFlags.Instance | BindingFlags.Public |
        BindingFlags.NonPublic, null, [null, contract, "", null], null)!;
    var indexedExports = (IDictionary)libraryType.GetProperty("Exports", hiddenInstance)!.GetValue(library)!;
    var indexedCertifications = (IDictionary)libraryType.GetProperty("Certifications", hiddenInstance)!.GetValue(library)!;
    if (indexedExports.Count != 2 || !indexedExports.Contains("Method") || !indexedExports.Contains("method") ||
        indexedExports.Contains("METHOD") || indexedCertifications.Count != 4 ||
        !indexedCertifications.Contains(("Method", "scalar")) ||
        !indexedCertifications.Contains(("Method", "x64-v3")) ||
        indexedCertifications.Contains(("Method", "SCALAR")))
        throw new Exception("Import indexes changed identity or profile matching");
    foreach (var field in new[] { "exports", "certifications" })
    {
        var duplicate = value.DeepClone().AsObject();
        duplicate[field]!.AsArray().Add(duplicate[field]![0]!.DeepClone());
        try { Read(duplicate); throw new Exception("Duplicate " + field + " accepted"); }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
            rejected.Message == (field == "exports" ? "Invalid or duplicate contract export." :
                "Invalid or duplicate contract certification.")) { }
    }
    Console.WriteLine("PASS exact import identity/profile indexing and production duplicate rejection");
    SortedDictionary<string, string> MergeModules(params (string Name, string Source)[] entries)
    {
        var libraries = Array.CreateInstance(libraryType, entries.Length);
        for (var index = 0; index < entries.Length; index++)
        {
            var fixture = value.DeepClone().AsObject();
            fixture["interfaceModules"] = new JsonArray(new JsonObject
                { ["name"] = entries[index].Name, ["source"] = entries[index].Source });
            var description = JsonSerializer.Deserialize(fixture.ToJsonString(), contractType, json)!;
            libraries.SetValue(Activator.CreateInstance(libraryType, BindingFlags.Instance | BindingFlags.Public |
                BindingFlags.NonPublic, null, [null, description, "", null], null), index);
        }
        return (SortedDictionary<string, string>)resolutionType.GetMethod("Modules", hiddenStatic)!
            .Invoke(null, [libraries])!;
    }
    var merged = MergeModules(("Z", "last"), ("A", "first"), ("A", "first"));
    if (!merged.Keys.SequenceEqual(new[] { "A", "Z" }) || merged["A"] != "first")
        throw new Exception("Module merging lost sorted output or identical-content deduplication");
    foreach (var pair in new[] { ("A", "one", "A", "two"), ("A", "one", "a", "one"),
        ("Σ", "one", "σ", "one") })
    {
        try
        {
            MergeModules((pair.Item1, pair.Item2), (pair.Item3, pair.Item4));
            throw new Exception("Conflicting module names or contents accepted");
        }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
            rejected.Message == "Conflicting contract interface module: " + pair.Item3) { }
    }
    Console.WriteLine("PASS module ordering, exact deduplication, conflicting contents and ordinal case collisions");
}
finally { AppContext.SetData("APP_CONTEXT_BASE_DIRECTORY", savedBaseDirectory); }
