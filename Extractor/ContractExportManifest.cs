using System.Text.Json;
using System.Text.Json.Serialization;

namespace Nethermind.LeanCIL;

internal sealed record ContractSource(string Module, string Source);
internal sealed record ContractExportProfile(string Profile, string Artifact);
internal sealed record ContractExportRequest(string Method, string Artifact, string Contract, string Theorem,
    string[]? TypeArguments = null, ContractExportProfile[]? Profiles = null, string? Program = null,
    string? ReferenceProfile = null)
{
    [JsonIgnore] internal string? ReferenceArtifact { get; init; }
}
internal sealed record ContractExportManifest(int Schema, string Assembly, string ProofRoot,
    ContractSource[] Interface, ContractExportRequest[] Exports)
{
    internal string SourceSha256 { get; init; } = "";

    internal static readonly JsonSerializerOptions Json = new()
    {
        PropertyNamingPolicy = JsonNamingPolicy.CamelCase,
        UnmappedMemberHandling = JsonUnmappedMemberHandling.Disallow,
        WriteIndented = true
    };

    internal static ContractExportManifest Read(string path)
    {
        byte[] bytes = File.ReadAllBytes(path);
        using JsonDocument document = JsonDocument.Parse(bytes);
        RejectDuplicates(document.RootElement);
        ContractExportManifest manifest = document.RootElement.Deserialize<ContractExportManifest>(Json)
            ?? throw new InvalidDataException("Missing contract export manifest.");
        if (manifest.Schema != 1 || string.IsNullOrWhiteSpace(manifest.Assembly) || string.IsNullOrWhiteSpace(manifest.ProofRoot) ||
            manifest.Interface is null || manifest.Interface.Length == 0 || manifest.Exports is null || manifest.Exports.Length == 0)
            throw new InvalidDataException("Contract export requires schema 1, assembly, proofRoot, interface and exports.");
        if (manifest.Interface.Any(source => source is null || !ContractInterface.ModuleName(source.Module) || string.IsNullOrWhiteSpace(source.Source)) ||
            manifest.Interface.Select(source => source.Module).Distinct(StringComparer.Ordinal).Count() != manifest.Interface.Length)
            throw new InvalidDataException("Invalid or duplicate contract interface module.");
        string root = Path.GetDirectoryName(Path.GetFullPath(path))!;
        return manifest with
        {
            SourceSha256 = ContractInterface.Hash(bytes),
            Assembly = Path.GetFullPath(manifest.Assembly, root),
            ProofRoot = Path.GetFullPath(manifest.ProofRoot, root),
            Interface = manifest.Interface.Select(source => source with { Source = Path.GetFullPath(source.Source, root) })
                .OrderBy(source => source.Module, StringComparer.Ordinal).ToArray(),
            Exports = ExpandExports(manifest.Exports, root)
        };
    }

    internal static ContractExportRequest[] ExpandExports(ContractExportRequest[] exports, string root)
    {
        if (exports.Any(export => export is null || string.IsNullOrWhiteSpace(export.Method) ||
            !ContractInterface.Constant(export.Contract) || !ContractInterface.Constant(export.Theorem)))
            throw new InvalidDataException("Each contract export requires method, contract and theorem identifiers.");
        return exports.SelectMany(export => Expand(export, root)).ToArray();
    }

    // Expanded requests retain the family metadata while every artifact has its own ordinary export checks.
    static IEnumerable<ContractExportRequest> Expand(ContractExportRequest export, string root)
    {
        if (export.Profiles is null)
        {
            if (string.IsNullOrWhiteSpace(export.Artifact) || export.Program is not null ||
                export.ReferenceProfile is not null)
                throw new InvalidDataException("A single-profile export requires artifact and no family metadata.");
            yield return export with { Artifact = Path.GetFullPath(export.Artifact, root) };
            yield break;
        }
        if (export.Artifact is not null || export.Profiles.Length == 0 ||
            !ContractInterface.Constant(export.Program ?? "") || string.IsNullOrWhiteSpace(export.ReferenceProfile) ||
            export.Profiles.Any(profile => profile is null || string.IsNullOrWhiteSpace(profile.Profile) ||
                string.IsNullOrWhiteSpace(profile.Artifact)) ||
            export.Profiles.Select(profile => profile.Profile).Distinct(StringComparer.Ordinal).Count() !=
                export.Profiles.Length)
            throw new InvalidDataException("A profile family requires program, referenceProfile and " +
                "distinct profiles with profile/artifact, and cannot also specify artifact.");
        RequireBuiltIn(export.ReferenceProfile);
        var reference = export.Profiles.SingleOrDefault(profile => profile.Profile == export.ReferenceProfile)
            ?? throw new InvalidDataException("A profile family must include its referenceProfile artifact.");
        foreach (var profile in export.Profiles)
        {
            RequireBuiltIn(profile.Profile);
            yield return export with
            {
                Artifact = Path.GetFullPath(profile.Artifact, root), Profiles = [profile],
                ReferenceArtifact = Path.GetFullPath(reference.Artifact, root)
            };
        }
    }

    static void RequireBuiltIn(string profile)
    {
        if (profile.StartsWith('@')) throw new InvalidDataException("Profile families require built-in profiles.");
        _ = FeatureProfile.Select(profile);
    }

    static void RejectDuplicates(JsonElement element)
    {
        if (element.ValueKind == JsonValueKind.Object)
        {
            HashSet<string> names = new(StringComparer.Ordinal);
            foreach (JsonProperty property in element.EnumerateObject())
            {
                if (!names.Add(property.Name)) throw new InvalidDataException("Duplicate contract export property: " + property.Name);
                RejectDuplicates(property.Value);
            }
        }
        else if (element.ValueKind == JsonValueKind.Array)
            foreach (JsonElement item in element.EnumerateArray()) RejectDuplicates(item);
    }
}
