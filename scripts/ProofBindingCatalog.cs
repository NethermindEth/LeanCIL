using System.Text;

namespace LeanCIL;

/// <summary>The exact method, profile, proof source and theorem selected for certification.</summary>
internal sealed record ProofGate(string Method, string Profile, string Proof, string Theorem);

/// <summary>A consumer-reviewed recipe's complete source for one exact gate.</summary>
internal sealed record ProofBinding(ProofGate Gate, string Source);

/// <summary>
/// Validates and materializes explicit binding recipes. Generated Lean still needs ordinary
/// extraction binding, source hashing and kernel certification; generation establishes no theorem.
/// </summary>
internal static class ProofBindingCatalog
{
    /// <summary>
    /// Checks exact identities and complete profile coverage for each generated method. Recipes,
    /// rather than catalog order or guessed theorem names, determine the generated sources.
    /// </summary>
    internal static Dictionary<string, string> Sources(IEnumerable<ProofGate> catalog,
        IEnumerable<ProofBinding> recipes)
    {
        ProofGate[] gates = [.. catalog];
        HashSet<(string Method, string Profile)> identities = [];
        foreach (ProofGate gate in gates)
        {
            if (string.IsNullOrWhiteSpace(gate.Method) || string.IsNullOrWhiteSpace(gate.Profile) ||
                string.IsNullOrWhiteSpace(gate.Theorem) || !identities.Add((gate.Method, gate.Profile)))
                throw new InvalidOperationException("Missing or duplicate gate identity: " + gate);
            CheckPath(gate.Proof);
        }

        HashSet<ProofGate> registered = [.. gates], expected = [];
        Dictionary<string, string> sources = new(StringComparer.Ordinal);
        HashSet<string> portablePaths = new(StringComparer.OrdinalIgnoreCase);
        foreach (ProofBinding binding in recipes.OrderBy(binding => binding.Gate.Proof, StringComparer.Ordinal))
        {
            ProofGate gate = binding.Gate;
            if (!registered.Contains(gate) || !expected.Add(gate))
                throw new InvalidOperationException("Missing, changed or duplicate binding gate: " + gate);
            if (string.IsNullOrWhiteSpace(binding.Source))
                throw new InvalidOperationException("Empty generated binding: " + gate.Proof);
            string source = binding.Source.ReplaceLineEndings("\n");
            if (sources.TryGetValue(gate.Proof, out string? existing))
            {
                if (existing != source)
                    throw new InvalidOperationException("Conflicting generated sources: " + gate.Proof);
            }
            else
            {
                if (!portablePaths.Add(gate.Proof))
                    throw new InvalidOperationException("Case-dependent generated path: " + gate.Proof);
                sources.Add(gate.Proof, source);
            }
        }
        HashSet<string> methods = [.. expected.Select(gate => gate.Method)];
        if (gates.Any(gate => (methods.Contains(gate.Method) || portablePaths.Contains(gate.Proof)) &&
                !expected.Contains(gate)))
            throw new InvalidOperationException("Unexpected profile, proof or theorem for a generated binding");
        return sources;
    }

    /// <summary>
    /// Writes canonical UTF-8 sources, or checks their exact bytes without modifying them. Call before
    /// import selection and source capture so the verifier audits generated bindings like other Lean.
    /// </summary>
    internal static void Materialize(string root, IEnumerable<ProofGate> catalog,
        IEnumerable<ProofBinding> recipes, bool check = false)
    {
        Dictionary<string, string> sources = Sources(catalog, recipes);
        root = Path.GetFullPath(root);
        var files = sources.Select(pair => (Path: Path.Combine(root, pair.Key),
            Bytes: Encoding.UTF8.GetBytes(pair.Value))).ToArray();
        foreach (var file in files) CheckLinks(root, file.Path);
        foreach (var file in files)
        {
            bool same = File.Exists(file.Path) && File.ReadAllBytes(file.Path).AsSpan().SequenceEqual(file.Bytes);
            if (check && !same) throw new InvalidOperationException("Generated binding differs: " + file.Path);
            if (same || check) continue;
            Directory.CreateDirectory(Path.GetDirectoryName(file.Path)!);
            File.WriteAllBytes(file.Path, file.Bytes);
        }
    }

    private static void CheckPath(string path)
    {
        if (string.IsNullOrEmpty(path) || !path.EndsWith(".lean", StringComparison.Ordinal) ||
            path.Contains('\\') || path.Contains(':') || Path.IsPathRooted(path) ||
            path.Split('/').Any(part => part is "" or "." or ".." ||
                part.IndexOfAny(Path.GetInvalidFileNameChars()) >= 0))
            throw new InvalidOperationException("Expected a relative Lean source path: " + path);
    }

    private static void CheckLinks(string root, string path)
    {
        for (string? current = path; current is not null; current = Path.GetDirectoryName(current))
        {
            if ((File.Exists(current) || Directory.Exists(current)) &&
                (File.GetAttributes(current) & FileAttributes.ReparsePoint) != 0)
                throw new InvalidOperationException("Generated binding path contains a link: " + current);
            if (current == root) break;
        }
    }
}
