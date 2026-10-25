using System.Security.Cryptography;
using System.Text;
using System.Text.Json;
using System.Text.Json.Serialization;
using System.Text.RegularExpressions;

namespace Nethermind.LeanCIL;

internal sealed record InterfaceModule(string Name, string Source);
internal sealed record ContractExport(string Identity, string Signature, int ParameterCount, bool HasThis,
    bool ReturnsValue, string Visibility, string ContractConstant, string ClosureDigest, string[] Profiles, string Kind,
    [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string? DefinitionSignature = null,
    [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] string[]? TypeArguments = null,
    [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractMethodSignature? TypedSignature = null,
    [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)] ContractLayout[]? Layouts = null,
    [property: JsonIgnore(Condition = JsonIgnoreCondition.WhenWritingNull)]
    ProfileInitializationAssumptions[]? InitializationAssumptions = null);
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
    internal static bool Constant(string value) => global::Program.ContractModules.Name(value);
    internal static bool ModuleName(string value) => global::Program.ContractModules.Interface(value);

    internal static string CurrentFrameworkKey()
    {
        string root = Path.Combine(AppContext.BaseDirectory, "verification");
        IEnumerable<string> sources = Directory.EnumerateFiles(Path.Combine(root, "CIL"), "*.lean", SearchOption.AllDirectories)
            .Append(Path.Combine(root, "CIL.lean")).Append(Path.Combine(root, "lean-toolchain"));
        string manifest = string.Join("\n", sources.Select(path => (Name: Path.GetRelativePath(root, path).Replace('\\', '/'), Path: path))
            .OrderBy(item => item.Name, StringComparer.Ordinal).Select(item => item.Name + "=" + Hash(File.ReadAllBytes(item.Path))));
        return Hash(Encoding.UTF8.GetBytes(manifest));
    }

    internal string ComputeInterfaceDigest() => Hash(JsonSerializer.SerializeToUtf8Bytes(new
    {
        Schema, SemanticsVersion, FormatVersion, FrameworkKey, AssemblyIdentity, TargetFramework,
        InterfaceModules, Exports, Dependencies
    }, Json));

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
        if (value.Schema != 1 || value.SemanticsVersion != 1 || value.FormatVersion is not (1 or 2))
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
            value.InterfaceModules.Select(module => module.Name).Distinct(StringComparer.OrdinalIgnoreCase).Count() != value.InterfaceModules.Length)
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
        foreach (ContractExport export in value.Exports)
        {
            InitializationAssumption.ValidateExport(export, value.FormatVersion);
            bool metadata = export.DefinitionSignature is not null || export.TypeArguments is not null ||
                export.TypedSignature is not null || export.Layouts is not null;
            if (value.FormatVersion == 1 && metadata)
                throw new InvalidDataException("Legacy contract exports cannot carry typed instance or layout metadata.");
            if (value.FormatVersion == 2)
            {
                if (string.IsNullOrWhiteSpace(export.DefinitionSignature) || export.TypeArguments is null ||
                    export.TypedSignature is null || export.Layouts is null)
                    throw new InvalidDataException("Typed contract exports require definition, arguments, signature and layouts.");
                ContractMethodMetadata.ValidatePublished(export.TypedSignature, export.TypeArguments, export.ParameterCount, export.ReturnsValue);
                ImportedLayoutMetadata.ValidatePublished(export.Layouts);
            }
        }
        JsonElement[] suppliedExports = document.RootElement.GetProperty("exports").EnumerateArray().ToArray();
        for (int index = 0; index < suppliedExports.Length; index++)
            ValidateDescriptorShape(suppliedExports[index], JsonSerializer.SerializeToElement(value.Exports[index], Json));
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

    // Use the canonical serializer's schema recursively so carriers cannot omit
    // default-valued metadata or introduce ignored fields through a legacy format.
    static void ValidateDescriptorShape(JsonElement supplied, JsonElement canonical)
    {
        if (supplied.ValueKind != canonical.ValueKind)
            throw new InvalidDataException("Contract descriptor metadata kind mismatch.");
        if (canonical.ValueKind == JsonValueKind.Object)
        {
            string[] actual = supplied.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal).ToArray();
            string[] expected = canonical.EnumerateObject().Select(property => property.Name).Order(StringComparer.Ordinal).ToArray();
            if (!actual.SequenceEqual(expected, StringComparer.Ordinal))
                throw new InvalidDataException("Missing or unsupported contract descriptor metadata field.");
            foreach (JsonProperty property in canonical.EnumerateObject())
                ValidateDescriptorShape(supplied.GetProperty(property.Name), property.Value);
        }
        else if (canonical.ValueKind == JsonValueKind.Array)
        {
            JsonElement[] actual = supplied.EnumerateArray().ToArray();
            JsonElement[] expected = canonical.EnumerateArray().ToArray();
            if (actual.Length != expected.Length) throw new InvalidDataException("Contract descriptor metadata length mismatch.");
            for (int index = 0; index < actual.Length; index++) ValidateDescriptorShape(actual[index], expected[index]);
        }
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
