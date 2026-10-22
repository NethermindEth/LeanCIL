using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Nodes;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;

namespace Nethermind.LeanCIL;

internal sealed record InterfaceModule(string Name, string Source);
internal sealed record ContractExport(string Identity, string Signature, int ParameterCount, bool HasThis,
    bool ReturnsValue, string Visibility, string ContractConstant, string ClosureDigest, string[] Profiles, string Kind);
internal sealed record ContractCertification(string Identity, string Profile, string ImplementationSha256,
    string InterfaceDigest, string ClosureDigest, string Theorem, string Statement, string StatementDigest,
    StaticIdentityRecord[] StaticIdentities);
internal sealed record ContractDependency(string AssemblyIdentity, string ImplementationSha256, string InterfaceDigest);
internal sealed record ContractInterface(int Schema, int SemanticsVersion, int FormatVersion, string FrameworkKey,
    string AssemblyIdentity, Guid Mvid, string TargetFramework, string ImplementationSha256, bool IsReferenceAssembly,
    InterfaceModule[] InterfaceModules, string InterfaceDigest, ContractExport[] Exports,
    ContractCertification[] Certifications, ContractDependency[] Dependencies, string? FullVerificationLocator = null)
{
    internal static readonly JsonSerializerOptions Json = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow
    };

    internal static string Hash(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));
    internal static bool Digest(string value) => value is not null && Regex.IsMatch(value, @"\A[0-9a-f]{64}\z");
    internal static bool Constant(string value) => value is not null && !value.Split('.').Contains("_root_", StringComparer.Ordinal) && Regex.IsMatch(value, @"\A[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\z");
    internal static bool ModuleName(string value) => Constant(value) && value.Split('.')[0] is not
        ("CIL" or "Lean" or "Init" or "Std" or "Extracted" or "ExtractedImports" or "Proof" or "Audit" or "ExtractionAudit" or "ExtractedSymbols" or "Symbols" or "Examples" or "Tests" or "lakefile");

    internal static string CurrentFrameworkKey()
    {
        string root = Path.Combine(AppContext.BaseDirectory, "verification");
        IEnumerable<string> sources = Directory.EnumerateFiles(Path.Combine(root, "CIL"), "*.lean", SearchOption.AllDirectories)
            .Append(Path.Combine(root, "CIL.lean")).Append(Path.Combine(root, "lean-toolchain"));
        string manifest = string.Join("\n", sources.Select(path => (Name: Path.GetRelativePath(root, path).Replace('\\', '/'), Path: path))
            .OrderBy(item => item.Name, StringComparer.Ordinal).Select(item => item.Name + "=" + Hash(File.ReadAllBytes(item.Path))));
        return Hash(Encoding.UTF8.GetBytes(manifest));
    }

    // One versioned descriptor API serves sidecars and embedded carriers. Future
    // format revisions must extend this projection and its strict reader together.
    internal byte[] DescriptorBytes() => JsonSerializer.SerializeToUtf8Bytes(new
    {
        Schema, SemanticsVersion, FormatVersion, FrameworkKey, AssemblyIdentity, TargetFramework,
        InterfaceModules, Exports, Dependencies
    }, Json);

    internal string ComputeInterfaceDigest() => Hash(DescriptorBytes());

    internal static void ValidateDescriptor(byte[] bytes, ContractInterface contract)
    {
        using JsonDocument embedded = JsonDocument.Parse(bytes);
        ValidateProperties(embedded.RootElement);
        using JsonDocument expected = JsonDocument.Parse(contract.DescriptorBytes());
        string[] actualFields = embedded.RootElement.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal).ToArray();
        string[] expectedFields = expected.RootElement.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal).ToArray();
        if (!actualFields.SequenceEqual(expectedFields, StringComparer.Ordinal))
            throw new InvalidDataException("Embedded contract descriptor fields differ from the supported format.");
        // The sidecar already passed the full versioned reader. Require the
        // complete same JSON structure and typed values without hashing the
        // framework a second time for this alternative carrier.
        JsonObject combined = JsonNode.Parse(JsonSerializer.Serialize(contract, Json))!.AsObject();
        foreach (JsonProperty property in embedded.RootElement.EnumerateObject())
            combined[property.Name] = JsonNode.Parse(property.Value.GetRawText());
        ContractInterface supplied = combined.Deserialize<ContractInterface>(Json)
            ?? throw new InvalidDataException("Missing embedded contract descriptor.");
        if (!JsonElement.DeepEquals(embedded.RootElement, expected.RootElement) ||
            !supplied.DescriptorBytes().AsSpan().SequenceEqual(contract.DescriptorBytes()))
            throw new InvalidDataException("Embedded and sidecar contract interface digests differ.");
    }

    internal static ContractInterface Read(byte[] bytes)
    {
        using JsonDocument document = JsonDocument.Parse(bytes);
        ValidateProperties(document.RootElement);
        Require(document.RootElement, "schema", "semanticsVersion", "formatVersion", "frameworkKey", "assemblyIdentity", "mvid",
            "targetFramework", "implementationSha256", "isReferenceAssembly", "interfaceModules", "interfaceDigest", "exports", "certifications", "dependencies");
        foreach (JsonElement module in document.RootElement.GetProperty("interfaceModules").EnumerateArray()) Require(module, "name", "source");
        foreach (JsonElement export in document.RootElement.GetProperty("exports").EnumerateArray())
            Require(export, "identity", "signature", "parameterCount", "hasThis", "returnsValue", "visibility", "contractConstant", "closureDigest", "profiles", "kind");
        foreach (JsonElement record in document.RootElement.GetProperty("certifications").EnumerateArray())
        {
            Require(record, "identity", "profile", "implementationSha256", "interfaceDigest", "closureDigest", "theorem", "statement", "statementDigest", "staticIdentities");
            foreach (JsonElement identity in record.GetProperty("staticIdentities").EnumerateArray())
                Require(identity, "identity", "assemblyIdentity", "fieldName");
        }
        foreach (JsonElement dependency in document.RootElement.GetProperty("dependencies").EnumerateArray())
            Require(dependency, "assemblyIdentity", "implementationSha256", "interfaceDigest");
        ContractInterface value = document.RootElement.Deserialize<ContractInterface>(Json)
            ?? throw new InvalidDataException("Missing contract interface.");
        if (value.Schema != 1 || value.SemanticsVersion != 1 || value.FormatVersion != 1)
            throw new InvalidDataException("Unsupported contract interface format or semantics version.");
        if (value.Dependencies is null || value.Dependencies.Any(dependency => dependency is null ||
            string.IsNullOrWhiteSpace(dependency.AssemblyIdentity) || !Digest(dependency.ImplementationSha256) ||
            !Digest(dependency.InterfaceDigest)) ||
            value.Dependencies.Select(dependency => dependency.AssemblyIdentity).Distinct(StringComparer.Ordinal).Count() != value.Dependencies.Length)
            throw new InvalidDataException("Invalid or duplicate contract dependency.");
        if (value.FrameworkKey != CurrentFrameworkKey())
            throw new InvalidDataException("Contract interface framework key mismatch.");
        if (!Digest(value.ImplementationSha256) || !Digest(value.InterfaceDigest) || value.Mvid == Guid.Empty ||
            string.IsNullOrWhiteSpace(value.AssemblyIdentity) || string.IsNullOrWhiteSpace(value.TargetFramework))
            throw new InvalidDataException("Invalid contract interface identity or digest.");
        if (value.InterfaceModules is null || value.InterfaceModules.Length == 0 ||
            value.InterfaceModules.Any(module => module is null || !ModuleName(module.Name) || string.IsNullOrWhiteSpace(module.Source)) ||
            value.InterfaceModules.Select(module => module.Name).Distinct(StringComparer.Ordinal).Count() != value.InterfaceModules.Length)
            throw new InvalidDataException("Invalid or duplicate contract interface module.");
        if (value.Exports is not null && value.Exports.Any(export => export is not null && export.Kind is not ("method" or "outcome")))
            throw new InvalidDataException("Unsupported contract export kind; expected method or outcome.");
        if (value.Exports is null || value.Exports.Length == 0 || value.Certifications is null ||
            value.Exports.Any(export => export is null || string.IsNullOrWhiteSpace(export.Identity) || string.IsNullOrWhiteSpace(export.Signature) ||
                export.ParameterCount < 0 || export.HasThis || export.Kind is not ("method" or "outcome") || !Constant(export.ContractConstant) || !Digest(export.ClosureDigest) ||
                export.Profiles is null || export.Profiles.Length == 0 || export.Profiles.Any(string.IsNullOrWhiteSpace) ||
                export.Profiles.Distinct(StringComparer.Ordinal).Count() != export.Profiles.Length) ||
            value.Exports.Select(export => export.Identity).Distinct(StringComparer.Ordinal).Count() != value.Exports.Length)
            throw new InvalidDataException("Invalid or duplicate contract export.");
        if (value.Certifications.Any(record => record is null || !Digest(record.ImplementationSha256) ||
            !Digest(record.InterfaceDigest) || !Digest(record.ClosureDigest) || !Constant(record.Theorem) ||
            string.IsNullOrWhiteSpace(record.Statement) || !Digest(record.StatementDigest) || record.StaticIdentities is null ||
            record.StaticIdentities.Distinct().Count() != record.StaticIdentities.Length) ||
            value.Certifications.Select(record => (record.Identity, record.Profile)).Distinct().Count() != value.Certifications.Length)
            throw new InvalidDataException("Invalid or duplicate contract certification.");
        foreach (ContractCertification certification in value.Certifications) StaticIdentity.Validate(certification.StaticIdentities);
        if (value.ComputeInterfaceDigest() != value.InterfaceDigest)
            throw new InvalidDataException("Contract interface digest mismatch.");
        return value;
    }

    static void Require(JsonElement element, params string[] fields)
    {
        foreach (string field in fields)
            if (!element.TryGetProperty(field, out JsonElement value) || value.ValueKind == JsonValueKind.Null)
                throw new InvalidDataException("Missing contract interface field: " + field);
    }

    static void ValidateProperties(JsonElement element)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            HashSet<string> names = new(StringComparer.Ordinal);
            foreach (JsonProperty property in element.EnumerateObject())
            {
                if (!names.Add(property.Name)) throw new InvalidDataException("Duplicate contract interface property: " + property.Name);
                ValidateProperties(property.Value);
            }
        }
        else if (element.ValueKind == JsonValueKind.Array)
            foreach (JsonElement child in element.EnumerateArray()) ValidateProperties(child);
    }
}
