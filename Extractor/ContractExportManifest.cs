using System.Text.Json;
using System.Text.Json.Serialization;

namespace Nethermind.LeanCIL;

internal sealed record ContractSource(string Module, string Source);
internal sealed record ContractExportRequest(string Method, string Artifact, string Contract, string Theorem);
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
        if (manifest.Exports.Any(export => export is null || string.IsNullOrWhiteSpace(export.Method) || string.IsNullOrWhiteSpace(export.Artifact) ||
            !ContractInterface.Constant(export.Contract) || !ContractInterface.Constant(export.Theorem)))
            throw new InvalidDataException("Each contract export requires method, artifact, contract and theorem identifiers.");
        string root = Path.GetDirectoryName(Path.GetFullPath(path))!;
        return manifest with
        {
            SourceSha256 = ContractInterface.Hash(bytes),
            Assembly = Path.GetFullPath(manifest.Assembly, root),
            ProofRoot = Path.GetFullPath(manifest.ProofRoot, root),
            Interface = manifest.Interface.Select(source => source with { Source = Path.GetFullPath(source.Source, root) })
                .OrderBy(source => source.Module, StringComparer.Ordinal).ToArray(),
            Exports = manifest.Exports.Select(export => export with { Artifact = Path.GetFullPath(export.Artifact, root) }).ToArray()
        };
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
