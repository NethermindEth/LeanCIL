#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PinnedMetadata.cs

using System.Collections;
using System.Reflection;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
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
        AssemblyIdentity = "Fixture", Mvid = Guid.NewGuid(), TargetFramework = ".NETCoreApp,Version=v11.0",
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

    var implementation = At("Examples/Assembly/bin/Examples.dll");
    var implementationHash = Convert.ToHexStringLower(SHA256.HashData(File.ReadAllBytes(implementation)));
    var sourceType = resolutionType.GetNestedType("Source", BindingFlags.NonPublic)!;
    var directory = At("artifacts/ImportIndexes");
    Directory.CreateDirectory(directory);
    var sidecar = Path.Combine(directory, "Examples.leancil.contracts");
    using (var pinned = new PinnedMetadata(assembly, implementation))
    {
        var description = value.DeepClone().AsObject();
        description["assemblyIdentity"] = pinned.Module.Assembly.Name.FullName;
        description["mvid"] = pinned.Module.Mvid;
        description["implementationSha256"] = implementationHash;
        var descriptionValue = JsonSerializer.Deserialize(description.ToJsonString(), contractType, json)!;
        var interfaceHash = (string)contractType.GetMethod("ComputeInterfaceDigest", hiddenInstance)!
            .Invoke(descriptionValue, null)!;
        description["interfaceDigest"] = interfaceHash;
        File.WriteAllText(sidecar, description.ToJsonString());
        var importedContract = Read(description);
        object Source(string hash) => Activator.CreateInstance(sourceType,
            hiddenInstance | BindingFlags.Public, null, [sidecar, implementation, hash, interfaceHash, false], null)!;
        IDisposable Resolution(params object[] sources)
        {
            var entries = Array.CreateInstance(sourceType, sources.Length);
            for (int index = 0; index < sources.Length; index++) entries.SetValue(sources[index], index);
            return (IDisposable)Activator.CreateInstance(resolutionType, hiddenInstance, null, [entries], null)!;
        }
        var registry = (IDictionary)pinned.Context.GetType().GetField("identityImages", hiddenInstance)!
            .GetValue(pinned.Context)!;
        var baselineCount = registry.Count;
        PEReader[] Readers() => registry.Values.Cast<object>().Select(entry =>
            (PEReader)entry.GetType().GetField("Item1")!.GetValue(entry)!).ToArray();
        void Released(PEReader[] readers)
        {
            if (registry.Count != baselineCount) throw new Exception("Disposed import retained identity metadata.");
            foreach (var reader in readers)
            {
                try { reader.GetMetadata(); }
                catch (ObjectDisposedException) { continue; }
                throw new Exception("Disposed import retained an open metadata reader.");
            }
        }
        for (int repeat = 0; repeat < 32; repeat++)
        {
            var resolution = Resolution(Source(implementationHash));
            if (registry.Count != baselineCount + 1) throw new Exception("Import metadata was not registered.");
            var readers = Readers();
            using (var child = (IDisposable)Activator.CreateInstance(resolutionType, hiddenInstance, null,
                [resolution, importedContract], null)!) { }
            if (registry.Count != baselineCount + 1) throw new Exception("A child released its parent's metadata.");
            using (var other = new PinnedMetadata(assembly, implementation)) resolution.Dispose();
            Released(readers);
            resolution.Dispose();
            Released(readers);
        }
        var first = Source(implementationHash);
        var invalid = Source(new string('0', 64));
        PEReader[] failedReaders = [];
        IEnumerable<object> FailingSources()
        {
            yield return first;
            failedReaders = Readers();
            yield return invalid;
        }
        var failingSources = typeof(Enumerable).GetMethod("Cast")!.MakeGenericMethod(sourceType)
            .Invoke(null, [FailingSources()]);
        try
        {
            using var failed = (IDisposable)Activator.CreateInstance(resolutionType, hiddenInstance, null,
                [failingSources], null)!;
            throw new Exception("Import with a wrong implementation hash was accepted.");
        }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException rejected &&
            rejected.Message.StartsWith("Import implementation SHA-256 mismatch:", StringComparison.Ordinal)) { }
        if (failedReaders.Length != 1) throw new Exception("Failure did not follow a registered import.");
        Released(failedReaders);
        Console.WriteLine("PASS import metadata release, child ownership, changed context " +
            "and failed constructor cleanup");
    }
    using (var empty = (IDisposable)Activator.CreateInstance(resolutionType, hiddenInstance, null,
        [Array.CreateInstance(sourceType, 0)], null)!) { }
}
finally { AppContext.SetData("APP_CONTEXT_BASE_DIRECTORY", savedBaseDirectory); }
