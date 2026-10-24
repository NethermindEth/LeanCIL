using System.Security.Cryptography;
using System.Text.Json;

namespace Nethermind.LeanCIL;

internal static partial class Program
{
    sealed record ExtractionRequest(string Assembly, string? Identity, string Entry, string Output, string Profile);

    // Only immutable assembly bytes cross requests. Validation rewrites Cecil instruction operands,
    // and symbols attach readers to modules, so every request owns fresh modules and symbol readers.
    sealed class ExtractionBatch
    {
        internal sealed record AssemblySnapshot(byte[] Bytes, string Hash)
        {
            bool signaturesValidated;

            internal void ValidateSignatures()
            {
                if (signaturesValidated) return;
                VectorSignatures.Validate(Bytes);
                signaturesValidated = true;
            }
        }
        readonly Dictionary<string, AssemblySnapshot> assemblies = new(StringComparer.Ordinal);
        readonly Dictionary<string, string?> files = new(StringComparer.Ordinal);

        internal string ExtractorHash { get; }

        internal ExtractionBatch()
        {
            var extractor = typeof(LeanEmitter).Assembly.Location;
            ExtractorHash = Hash(File.ReadAllBytes(extractor));
            files.Add(extractor, ExtractorHash);
        }

        static string Hash(byte[] bytes) => Convert.ToHexStringLower(SHA256.HashData(bytes));

        static string? FileHash(string path) => File.Exists(path) ? Hash(File.ReadAllBytes(path)) : null;

        internal void Track(string path)
        {
            path = Path.GetFullPath(path);
            if (!files.ContainsKey(path)) files.Add(path, FileHash(path));
        }

        internal AssemblySnapshot ReadAssembly(string path)
        {
            path = Path.GetFullPath(path);
            if (assemblies.TryGetValue(path, out var snapshot)) return snapshot;
            var bytes = File.ReadAllBytes(path);
            snapshot = new(bytes, Hash(bytes));
            assemblies.Add(path, snapshot);
            files.TryAdd(path, snapshot.Hash);
            Track(Path.ChangeExtension(path, ".pdb"));
            return snapshot;
        }

        internal void RequireUnchanged()
        {
            foreach (var (path, hash) in files)
                if (FileHash(path) != hash)
                    throw new InvalidDataException("Extraction batch input changed: " + CliPaths.Display(path));
        }
    }

    // A batch contains one extraction operation and cannot dispatch other CLI commands.
    static int RunExtractionBatch(string[] args)
    {
        if (args is not ["extract" or "check", _])
            throw new ArgumentException("Usage: generated-extraction-batch extract|check requests.json");
        var requests = JsonSerializer.Deserialize<ExtractionRequest[]>(File.ReadAllBytes(args[1]),
            new JsonSerializerOptions(JsonSerializerDefaults.Web))
            ?? throw new InvalidDataException("Missing extraction batch requests.");
        var outputs = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var request in requests)
        {
            if (request is null || string.IsNullOrWhiteSpace(request.Assembly) ||
                string.IsNullOrWhiteSpace(request.Entry) || string.IsNullOrWhiteSpace(request.Output) ||
                string.IsNullOrWhiteSpace(request.Profile))
                throw new InvalidDataException("Incomplete extraction batch request.");
            if (!outputs.Add(Path.TrimEndingDirectorySeparator(Path.GetFullPath(request.Output))))
                throw new InvalidDataException("Extraction batch outputs must be distinct.");
        }
        var batch = new ExtractionBatch();
        foreach (var request in requests)
        {
            if (request.Profile.StartsWith('@')) batch.Track(request.Profile[1..]);
            var result = Run([args[0], request.Assembly, request.Entry, request.Output, request.Profile,
                .. request.Identity is null ? Array.Empty<string>() : ["--assembly", request.Identity]], batch);
            if (result != 0) return result;
        }
        batch.RequireUnchanged();
        return 0;
    }
}
