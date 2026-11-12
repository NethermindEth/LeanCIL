using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using LeanCIL;
using Nethermind.LeanCIL;

partial class Program
{
    sealed record CatalogFile(int schema, string generatedRoot, CatalogFamily[] families);
    sealed record CatalogFamily(string template, CatalogGatePattern gate,
        Dictionary<string, string>[][]? dimensions = null, Dictionary<string, string>[]? exclude = null,
        Dictionary<string, string>[]? rows = null, CatalogAssign[]? assign = null,
        Dictionary<string, string>[]? handwritten = null);
    sealed record CatalogAssign(Dictionary<string, string> match, Dictionary<string, string> set);
    sealed record CatalogGatePattern(string name, string method, string[] profiles, string proof, string theorem);

    /// <summary>
    /// A gate that a binding catalog row yields. `Proof` is absolute. `Inputs` are the catalog and the family
    /// template the gate comes from, so a change to either selects it.
    /// </summary>
    internal sealed record CatalogGate(string Name, string Method, string[] Profiles, string Proof, string Theorem,
        string[] Inputs);

    /// <summary>
    /// A loaded binding catalog: its gates, and the exact text of each source it generates under
    /// `GeneratedRoot`, by absolute path. Generation establishes no theorem; each source is verified like any other.
    /// </summary>
    internal sealed record BindingCatalog(string Path, string GeneratedRoot, CatalogGate[] Gates,
        SortedDictionary<string, string> Sources);

    /// <summary>A combination of a family's variables, and the proof and theorem that replace its generated ones.
    /// </summary>
    sealed class CatalogRow(Dictionary<string, string> values)
    {
        internal Dictionary<string, string> Values { get; } = values;
        internal (string Proof, string Theorem)? Handwritten;
        internal string Shown => JsonSerializer.Serialize(new SortedDictionary<string, string>(Values,
            StringComparer.Ordinal));
    }

    const string BindingsUsage = "Usage: leancil bindings catalog.json [--check]";

    // A handwritten entry gives these besides the variables it matches, so no variable may take their names.
    static readonly string[] HandwrittenKeys = ["proof", "theorem"];

    /// <summary>
    /// Writes the sources of a binding catalog, or with `--check` reports each missing or differing source and each
    /// `.lean` file under its `generatedRoot` that no row produces, without writing anything.
    /// </summary>
    internal static int RunBindings(string[] args)
    {
        var (path, check) = args switch
        {
            [var file] when !file.StartsWith("--", StringComparison.Ordinal) => (file, false),
            [var file, "--check"] => (file, true),
            _ => throw new ArgumentException(BindingsUsage)
        };
        var catalog = LoadBindingCatalog(Path.GetFullPath(path));
        var (written, problems) = MaterializeBindings(catalog, check);
        foreach (var problem in problems) Console.WriteLine((check ? "FAIL " : "WARNING ") + problem);
        if (check)
            Console.WriteLine(problems.Count == 0
                ? $"Bindings: {catalog.Sources.Count} generated sources of {catalog.Gates.Length} gates match."
                : $"Bindings: {problems.Count} problems in {CliPaths.Display(catalog.GeneratedRoot)}.");
        else
            Console.WriteLine($"Bindings: wrote {written} of {catalog.Sources.Count} generated sources for " +
                $"{catalog.Gates.Length} gates.");
        return check && problems.Count > 0 ? 1 : 0;
    }

    /// <summary>
    /// Writes each source of `catalog` whose bytes differ, or under `check` writes nothing and reports each missing
    /// or differing source. Both report `.lean` files under the generated root that no row produces.
    /// </summary>
    static (int Written, List<string> Problems) MaterializeBindings(BindingCatalog catalog, bool check)
    {
        var problems = new List<string>();
        var written = 0;
        foreach (var (path, source) in catalog.Sources)
        {
            ProofBindingCatalog.CheckLinks(catalog.GeneratedRoot, path);
            var bytes = new UTF8Encoding(false).GetBytes(source);
            var exists = File.Exists(path);
            if (exists && File.ReadAllBytes(path).AsSpan().SequenceEqual(bytes)) continue;
            if (check)
            {
                problems.Add((exists ? "Generated source differs: " : "Generated source missing: ") +
                    CliPaths.Display(path));
                continue;
            }
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllBytes(path, bytes);
            written++;
        }
        var comparer = OperatingSystem.IsWindows() ? StringComparer.OrdinalIgnoreCase : StringComparer.Ordinal;
        var produced = new HashSet<string>(catalog.Sources.Keys, comparer);
        if (Directory.Exists(catalog.GeneratedRoot))
            problems.AddRange(Directory.EnumerateFiles(catalog.GeneratedRoot, "*.lean", SearchOption.AllDirectories)
                .Where(path => !produced.Contains(Path.GetFullPath(path))).Order(StringComparer.Ordinal)
                .Select(path => "No catalog row produces " + CliPaths.Display(path)));
        return (written, problems);
    }

    /// <summary>
    /// Reads the catalog at `path` and expands every family into its gates and generated sources. Paths in the
    /// catalog are relative to its directory, and generated proof paths to its `generatedRoot`. Nothing is written.
    /// </summary>
    internal static BindingCatalog LoadBindingCatalog(string path)
    {
        var directory = Path.GetDirectoryName(path)!;
        var shown = CliPaths.Display(path);
        CatalogFile? file;
        try { file = JsonSerializer.Deserialize<CatalogFile>(File.ReadAllText(path), GateManifestJson); }
        catch (JsonException error)
        {
            throw new InvalidDataException($"Invalid binding catalog {shown}: {error.Message}");
        }
        if (file is null || file.schema != 1 || file.families is not { Length: > 0 } || file.families.Contains(null))
            throw new InvalidDataException($"Binding catalog {shown}: expected schema 1, generatedRoot and families.");
        CheckRelativeDirectory("generatedRoot of " + shown, file.generatedRoot);
        var generatedRoot = Path.GetFullPath(file.generatedRoot, directory);
        var gates = new List<CatalogGate>();
        var sources = new SortedDictionary<string, string>(StringComparer.Ordinal);
        var spellings = new Dictionary<string, string>(StringComparer.OrdinalIgnoreCase);
        for (var index = 0; index < file.families.Length; index++)
            ExpandFamily($"{shown} family {index + 1}", file.families[index], path, directory, generatedRoot, gates,
                sources, spellings);
        var names = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        foreach (var gate in gates)
        {
            if (!SafeGateName(gate.Name))
                throw new InvalidDataException($"Binding catalog {shown} yields gate name {gate.Name}, which is " +
                    "not made of letters, digits, _, . and -.");
            if (!names.Add(gate.Name))
                throw new InvalidDataException($"Binding catalog {shown} yields gate {gate.Name} twice.");
        }
        return new(path, generatedRoot, [.. gates], sources);
    }

    /// <summary>
    /// Adds the gates and sources of `family`: the product of its dimensions without the excluded rows, then its
    /// explicit rows, then each handwritten entry that matches no row, with every assign applied to every row.
    /// </summary>
    static void ExpandFamily(string owner, CatalogFamily family, string catalog, string directory,
        string generatedRoot, List<CatalogGate> gates, SortedDictionary<string, string> sources,
        Dictionary<string, string> spellings)
    {
        var pattern = family.gate;
        if (string.IsNullOrWhiteSpace(family.template) || pattern is null ||
            new[] { pattern.name, pattern.method, pattern.proof, pattern.theorem }.Any(string.IsNullOrWhiteSpace) ||
            pattern.profiles is not { Length: > 0 } || pattern.profiles.Any(string.IsNullOrWhiteSpace))
            throw new InvalidDataException(owner + ": expected a template and a gate with name, method, " +
                "profiles, proof and theorem.");
        var templatePath = Path.GetFullPath(family.template, directory);
        if (!File.Exists(templatePath))
            throw new InvalidDataException(owner + ": template not found: " + CliPaths.Display(templatePath));
        var template = File.ReadAllText(templatePath);
        Dictionary<string, string> Variables(string kind, Dictionary<string, string>? values, bool handwritten = false)
        {
            if (values is null) throw new InvalidDataException($"{owner}: a {kind} is null.");
            foreach (var (name, value) in values)
                if (value is null || !Regex.IsMatch(name, @"\A[A-Za-z_][A-Za-z0-9_]*\z") ||
                    (!handwritten && HandwrittenKeys.Contains(name)))
                    throw new InvalidDataException($"{owner}: {kind} variable {name} needs an identifier name, " +
                        "other than proof or theorem, and a string value.");
            return new(values, StringComparer.Ordinal);
        }
        static bool Matches(Dictionary<string, string> row, IReadOnlyDictionary<string, string> match) =>
            match.All(pair => row.TryGetValue(pair.Key, out var value) && value == pair.Value);

        var rows = new List<CatalogRow>();
        if (family.dimensions is { Length: > 0 } dimensions)
        {
            List<Dictionary<string, string>> product = [new(StringComparer.Ordinal)];
            foreach (var dimension in dimensions)
            {
                if (dimension is not { Length: > 0 })
                    throw new InvalidDataException(owner + ": a dimension lists no values.");
                product = [.. product.SelectMany(partial => dimension.Select(entry =>
                {
                    var merged = new Dictionary<string, string>(partial, StringComparer.Ordinal);
                    foreach (var (name, value) in Variables("dimension", entry))
                        if (!merged.TryAdd(name, value))
                            throw new InvalidDataException($"{owner}: variable {name} is given by two dimensions.");
                    return merged;
                }))];
            }
            var excludes = (family.exclude ?? []).Select(entry => Variables("exclude", entry)).ToArray();
            foreach (var exclude in excludes)
                if (exclude.Count == 0 || !product.Any(row => Matches(row, exclude)))
                    throw new InvalidDataException($"{owner}: exclude {JsonSerializer.Serialize(exclude)} matches " +
                        "no row of the product.");
            rows.AddRange(product.Where(row => !excludes.Any(exclude => Matches(row, exclude)))
                .Select(row => new CatalogRow(row)));
        }
        else if (family.exclude is { Length: > 0 })
            throw new InvalidDataException(owner + ": exclude needs dimensions.");
        rows.AddRange((family.rows ?? []).Select(row => new CatalogRow(Variables("row", row))));

        var assigns = (family.assign ?? []).Select(assign => assign is null ? throw new InvalidDataException(
            owner + ": an assign is null.") : (Match: Variables("assign match", assign.match),
            Set: Variables("assign set", assign.set))).ToArray();
        var assigned = new bool[assigns.Length];
        void Assign(CatalogRow row)
        {
            for (var index = 0; index < assigns.Length; index++)
            {
                if (!Matches(row.Values, assigns[index].Match)) continue;
                assigned[index] = true;
                foreach (var (name, value) in assigns[index].Set)
                    if (!row.Values.TryAdd(name, value))
                        throw new InvalidDataException($"{owner}: variable {name} of row {row.Shown} is set twice.");
            }
        }
        foreach (var row in rows) Assign(row);
        foreach (var entry in family.handwritten ?? [])
        {
            var values = Variables("handwritten", entry, handwritten: true);
            if (!values.Remove("proof", out var proof) || !values.Remove("theorem", out var theorem) ||
                string.IsNullOrWhiteSpace(proof) || string.IsNullOrWhiteSpace(theorem) || values.Count == 0)
                throw new InvalidDataException(owner + ": a handwritten entry gives variables, a proof and a theorem.");
            var matching = rows.Where(row => Matches(row.Values, values)).ToList();
            if (matching.Count == 0)
            {
                var own = new CatalogRow(values);
                Assign(own);
                rows.Add(own);
                matching.Add(own);
            }
            foreach (var row in matching)
            {
                if (row.Handwritten is not null)
                    throw new InvalidDataException($"{owner}: two handwritten entries match row {row.Shown}.");
                row.Handwritten = (proof, theorem);
            }
        }
        for (var index = 0; index < assigns.Length; index++)
            if (!assigned[index])
                throw new InvalidDataException($"{owner}: assign {JsonSerializer.Serialize(assigns[index].Match)} " +
                    "matches no row.");
        if (rows.Count == 0) throw new InvalidDataException(owner + ": the family has no rows.");

        string[] patterns = [pattern.name, pattern.method, .. pattern.profiles, pattern.proof, pattern.theorem];
        var referenced = patterns.Prepend(template).SelectMany(TemplatePlaceholders)
            .Concat(assigns.SelectMany(assign => assign.Match.Keys)).ToHashSet(StringComparer.Ordinal);
        foreach (var row in rows)
        {
            if (row.Values.Keys.FirstOrDefault(name => !referenced.Contains(name)) is { } unused)
                throw new InvalidDataException($"{owner}: variable {unused} of row {row.Shown} is used by no " +
                    "placeholder of the template or the gate, and by no assign.");
            string Fill(string text, string what)
            {
                try { return Substitute(text, row.Values); }
                catch (InvalidDataException error)
                {
                    throw new InvalidDataException($"{owner}: row {row.Shown} cannot fill the {what}: {error.Message}");
                }
            }
            var name = Fill(pattern.name, "gate name");
            string proof, theorem;
            if (row.Handwritten is { } handwritten)
            {
                (proof, theorem) = (Path.GetFullPath(handwritten.Proof, directory), handwritten.Theorem);
                if (Path.GetExtension(proof) != ".lean" || Under(proof, generatedRoot))
                    throw new InvalidDataException($"{owner}: handwritten proof {handwritten.Proof} must be a .lean " +
                        "file outside generatedRoot.");
            }
            else
            {
                var relative = Fill(pattern.proof, "proof path");
                ProofBindingCatalog.CheckPath(relative);
                proof = Path.GetFullPath(Path.Combine(generatedRoot, relative));
                theorem = Fill(pattern.theorem, "theorem");
                var source = Fill(template, "template").ReplaceLineEndings("\n");
                if (spellings.TryGetValue(proof, out var spelled) && spelled != proof)
                    throw new InvalidDataException($"{owner}: generated paths {spelled} and {proof} differ only " +
                        "in case.");
                if (sources.TryGetValue(proof, out var existing) && existing != source)
                    throw new InvalidDataException($"{owner}: rows generate different sources at {relative}.");
                (spellings[proof], sources[proof]) = (proof, source);
            }
            gates.Add(new(name, Fill(pattern.method, "method"),
                [.. pattern.profiles.Select(profile => Fill(profile, "profile"))], proof, theorem,
                [catalog, templatePath]));
        }
    }

    /// <summary>Rejects a path that is not relative and made of `/`-separated names.</summary>
    static void CheckRelativeDirectory(string owner, string? path)
    {
        if (string.IsNullOrWhiteSpace(path) || Path.IsPathRooted(path) || path.Contains(':') ||
            path.Contains('\\') || path.Split('/').Any(part => part is "" or "." or ".." ||
                part.IndexOfAny(Path.GetInvalidFileNameChars()) >= 0))
            throw new InvalidDataException(owner + " must be a relative path of `/`-separated names.");
    }

    /// <summary>
    /// `template` with each `@NAME@` replaced by `values[NAME]` and LF line endings; nothing else changes.
    /// A placeholder without a value, or a value no placeholder uses, is an error.
    /// </summary>
    static string Instantiate(string template, IReadOnlyDictionary<string, string> values)
    {
        var used = new HashSet<string>(StringComparer.Ordinal);
        var text = Substitute(template, values, used);
        var unused = values.Keys.Where(name => !used.Contains(name)).Order(StringComparer.Ordinal).ToArray();
        if (unused.Length > 0)
            throw new InvalidDataException("Template values no placeholder uses: " + string.Join(", ", unused));
        return text.ReplaceLineEndings("\n");
    }

    /// <summary>
    /// `text` with each `@NAME@` replaced by `values[NAME]`, adding each replaced name to `used`. A placeholder
    /// without a value is an error.
    /// </summary>
    static string Substitute(string text, IReadOnlyDictionary<string, string> values, ISet<string>? used = null)
    {
        var missing = new SortedSet<string>(StringComparer.Ordinal);
        var result = TemplatePlaceholder().Replace(text, match =>
        {
            var name = match.Groups[1].Value;
            if (!values.TryGetValue(name, out var value))
            {
                missing.Add(name);
                return match.Value;
            }
            used?.Add(name);
            return value;
        });
        if (missing.Count > 0)
            throw new InvalidDataException("Template placeholders without a value: " + string.Join(", ", missing));
        return result;
    }

    /// <summary>The names of the placeholders in `text`.</summary>
    static IEnumerable<string> TemplatePlaceholders(string text) =>
        TemplatePlaceholder().Matches(text).Select(match => match.Groups[1].Value);

    [GeneratedRegex(@"@([A-Za-z_][A-Za-z0-9_]*)@")]
    private static partial Regex TemplatePlaceholder();
}

namespace LeanCIL
{
    /// <summary>Path checks for proof sources the tool generates.</summary>
    internal static class ProofBindingCatalog
    {
        /// <summary>Rejects a generated source path that is not a relative, `/`-separated `.lean` path.</summary>
        internal static void CheckPath(string path)
        {
            if (string.IsNullOrEmpty(path) || !path.EndsWith(".lean", StringComparison.Ordinal) ||
                path.Contains('\\') || path.Contains(':') || Path.IsPathRooted(path) ||
                path.Split('/').Any(part => part is "" or "." or ".." ||
                    part.IndexOfAny(Path.GetInvalidFileNameChars()) >= 0))
                throw new InvalidDataException("Expected a relative Lean source path: " + path);
        }

        /// <summary>Rejects a generated path under `root` that would be written through a link.</summary>
        internal static void CheckLinks(string root, string path)
        {
            for (string? current = path; current is not null; current = Path.GetDirectoryName(current))
            {
                if ((File.Exists(current) || Directory.Exists(current)) &&
                    (File.GetAttributes(current) & FileAttributes.ReparsePoint) != 0)
                    throw new InvalidDataException("Generated proof path contains a link: " + current);
                if (current == root) break;
            }
        }
    }
}
