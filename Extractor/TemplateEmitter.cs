using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace Nethermind.LeanCIL;

// Templates are proof inputs. Only the generated, kernel-checked bindings connect them to CIL.
internal static partial class TemplateEmitter
{
    internal sealed record Method(string Identity, string Metadata, string[] Ops, bool HasStaticSites);
    internal sealed record Variant(string Directory, string AssemblyHash, FeatureProfile Profile, Method[] Methods);
    sealed record Row(Variant Variant, Method Method, string[] Ops);
    sealed record Template(string Identity, string Metadata, Feature[] Features, string[] Callees, Row[] Rows);

    const string MissingProfile = ".unsupported \"Profile combination not selected for template\"";
    const string Usage = "Usage: leancil templates output-directory extraction-directory... [--check] " +
        "[--namespace name] [--omit-equations] [--module file.lean]";

    /// <summary>
    /// The options of <c>templates</c>: the namespace of the shared bodies, whether to omit their per-position
    /// equations, the template module's path and Lean name, and whether to compare instead of write.
    /// </summary>
    sealed record Options(string Output, string[] Extractions, string Namespace, bool OmitEquations,
        string ModulePath, string ModuleName, bool Check);

    static Options Parse(string[] args)
    {
        var positional = new List<string>();
        string? name = null, module = null;
        bool check = false, omit = false;
        for (var index = 0; index < args.Length; index++)
        {
            string Value() => ++index < args.Length && !args[index].StartsWith("--", StringComparison.Ordinal)
                ? args[index] : throw new ArgumentException(Usage);
            switch (args[index])
            {
                case "--check" when !check: check = true; break;
                case "--omit-equations" when !omit: omit = true; break;
                case "--namespace" when name is null: name = Value(); break;
                case "--module" when module is null: module = Value(); break;
                case var option when option.StartsWith("--", StringComparison.Ordinal):
                    throw new ArgumentException("Unknown or duplicate option: " + option + "\n" + Usage);
                case var path: positional.Add(path); break;
            }
        }
        if (positional.Count < 2) throw new ArgumentException(Usage);
        if (name is not null && !LeanName().IsMatch(name))
            throw new ArgumentException("--namespace takes a Lean name such as Proofs.Generated: " + name);
        var output = Path.GetFullPath(positional[0]);
        var modulePath = Path.GetFullPath(module ?? Path.Combine(output, "Templates.lean"));
        var relative = Path.GetRelativePath(output, modulePath).Replace('\\', '/');
        // The bindings import the module by its path under the output directory, a Lean source root.
        var moduleName = relative.EndsWith(".lean", StringComparison.Ordinal) ? relative[..^".lean".Length]
            .Replace('/', '.') : "";
        if (!LeanName().IsMatch(moduleName))
            throw new ArgumentException("--module takes a .lean file under the output directory whose path " +
                "names a Lean module: " + module);
        return new(output, [.. positional.Skip(1).Select(Path.GetFullPath)], name ?? "Templates", omit, modulePath,
            moduleName, check);
    }

    [GeneratedRegex(@"\A[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*\z")]
    private static partial Regex LeanName();

    /// <summary>
    /// Writes the shared template module, one binding per extraction and <c>templates.json</c>, with LF line endings,
    /// or under <c>--check</c> fails unless the files hold exactly what it would write.
    /// </summary>
    internal static void Run(string[] args, Func<string, Variant> read)
    {
        var options = Parse(args);
        var output = options.Output;
        var variants = options.Extractions.Select(read).ToArray();
        if (variants.Select(variant => variant.AssemblyHash).Distinct(StringComparer.Ordinal).Count() != 1)
            throw new InvalidDataException("Template inputs must come from the same exact assembly.");
        if (variants.Any(variant => variant.Methods.Select(method => method.Identity)
            .Distinct(StringComparer.Ordinal).Count() != variant.Methods.Length))
            throw new InvalidDataException("Template inputs contain ambiguous managed method identities.");
        if (variants.Any(variant => string.Equals(output, variant.Directory, StringComparison.OrdinalIgnoreCase)))
            throw new InvalidDataException("Template output must be separate from its extraction inputs.");
        var methods = variants.SelectMany(variant => variant.Methods.Select(method =>
            (Variant: variant, Method: method))).ToLookup(row => row.Method.Identity, StringComparer.Ordinal);
        var templates = methods.OrderBy(group => group.Key, StringComparer.Ordinal)
            .Select(group => Prepare(group.Key, group.ToArray())).ToArray();
        var templateIndices = templates.Select((template, index) => (template.Identity, index))
            .ToDictionary(pair => pair.Identity, pair => pair.index, StringComparer.Ordinal);
        var files = new SortedDictionary<string, string>(StringComparer.Ordinal)
        {
            [options.ModulePath] = EmitTemplates(templates, options.Namespace, options.OmitEquations)
        };
        for (var index = 0; index < variants.Length; index++)
            files[Path.Combine(output, $"TemplateBindings{index}.lean")] =
                EmitBindings(templates, templateIndices, variants[index], options);
        files[Path.Combine(output, "templates.json")] = JsonSerializer.Serialize(new
        {
            schema = 1,
            assemblySha256 = variants[0].AssemblyHash,
            module = options.ModuleName,
            instructionEquations = !options.OmitEquations,
            profiles = variants.Select((variant, index) => new
            {
                module = $"TemplateBindings{index}",
                extraction = Path.GetRelativePath(output, variant.Directory).Replace('\\', '/'),
                profile = variant.Profile
            }),
            methods = templates.Select((template, index) => new
            {
                name = $"{options.Namespace}.method{index}", signature = template.Identity,
                flags = template.Features.Select(Flag), callees = template.Callees
            })
        }, new JsonSerializerOptions { WriteIndented = true, NewLine = "\n" });
        if (options.Check)
        {
            Check(output, files);
            Console.WriteLine($"Checked {templates.Length} shared templates and {variants.Length} profile bindings.");
            return;
        }
        foreach (var (path, text) in files)
        {
            Directory.CreateDirectory(Path.GetDirectoryName(path)!);
            File.WriteAllText(path, text, new UTF8Encoding(false));
        }
        Console.WriteLine($"Emitted {templates.Length} shared templates and {variants.Length} profile bindings.");
        Console.WriteLine("Compile each binding against its recorded extraction; " +
            "templates alone certify no extraction.");
    }

    /// <summary>
    /// Fails, naming each file, unless every file of `files` holds exactly its text and the output directory holds
    /// no binding beyond them.
    /// </summary>
    static void Check(string output, SortedDictionary<string, string> files)
    {
        var problems = new List<string>();
        foreach (var (path, text) in files)
        {
            var exists = File.Exists(path);
            if (!exists || !File.ReadAllBytes(path).AsSpan().SequenceEqual(new UTF8Encoding(false).GetBytes(text)))
                problems.Add((exists ? "Template output differs: " : "Template output missing: ") + path);
        }
        if (Directory.Exists(output))
            problems.AddRange(Directory.EnumerateFiles(output, "TemplateBindings*.lean")
                .Where(path => Regex.IsMatch(Path.GetFileName(path), @"\ATemplateBindings[0-9]+\.lean\z") &&
                    !files.ContainsKey(Path.GetFullPath(path)))
                .Order(StringComparer.Ordinal).Select(path => "Template output has no input: " + path));
        if (problems.Count > 0) throw new InvalidDataException(string.Join("\n", problems));
    }

    static string Flag(Feature feature) => FeatureProfile.LeanFeature(feature)[1..];

    static (string Identity, string Prefix, string Tail)? Callee(Variant variant, string op)
    {
        if (op.StartsWith(".newVector256 ", StringComparison.Ordinal))
            throw new InvalidDataException("Templates do not yet support vector constructor calls: " + op);
        var prefix = new[] { ".call ", ".callInstance ", ".newAggregate ", ".newObject " }
            .FirstOrDefault(prefix => op.StartsWith(prefix, StringComparison.Ordinal));
        if (prefix is null) return null;
        var end = op.IndexOf(' ', prefix.Length);
        if (end < 0 || !int.TryParse(op[prefix.Length..end], out var index) ||
            index < 0 || index >= variant.Methods.Length)
            throw new InvalidDataException("Templates do not support imported callee slots: " + op);
        return (variant.Methods[index].Identity, prefix, op[end..]);
    }

    static Template Prepare(string identity, (Variant Variant, Method Method)[] selected)
    {
        var first = selected[0].Method;
        if (selected.Any(row => row.Method.HasStaticSites != first.HasStaticSites ||
            row.Method.Metadata != first.Metadata ||
            row.Method.Ops.Length != first.Ops.Length))
            throw new InvalidDataException("Template metadata or instruction count differs between profiles: " +
                identity);
        var features = Enum.GetValues<Feature>().Where(feature => selected.Any(row =>
            row.Method.Ops.Contains(".feature " + FeatureProfile.LeanFeature(feature), StringComparer.Ordinal)))
            .ToArray();
        var callees = selected.SelectMany(row => row.Method.Ops.Select(op => Callee(row.Variant, op)))
            .Where(callee => callee is not null).Select(callee => callee!.Value.Identity)
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var calleeIndices = callees.Select((callee, index) => (callee, index))
            .ToDictionary(pair => pair.callee, pair => pair.index, StringComparer.Ordinal);
        var rows = selected.Select(row => new Row(row.Variant, row.Method, row.Method.Ops.Select(op =>
        {
            var callee = Callee(row.Variant, op);
            return callee is null ? op : callee.Value.Prefix +
                "callee" + calleeIndices[callee.Value.Identity] + callee.Value.Tail;
        }).ToArray())).ToArray();
        return new(identity, first.Metadata, features, callees, rows);
    }

    // Missing combinations stay unsupported even where all selected rows share an instruction.
    static string Instruction(Template template, Row[] rows, int pc, int featureIndex = 0)
    {
        if (rows.Length == 0) return MissingProfile;
        if (featureIndex == template.Features.Length)
        {
            var values = rows.Select(row => row.Ops[pc]).Distinct(StringComparer.Ordinal).ToArray();
            if (values.Length != 1)
                throw new InvalidDataException("Profiles with identical observed flags emit different instructions: " +
                    template.Identity + " at pc " + pc);
            return values[0];
        }
        var feature = template.Features[featureIndex];
        var enabled = Instruction(template, rows.Where(row => row.Variant.Profile.Get(feature)).ToArray(),
            pc, featureIndex + 1);
        var disabled = Instruction(template, rows.Where(row => !row.Variant.Profile.Get(feature)).ToArray(),
            pc, featureIndex + 1);
        return enabled == disabled ? enabled : $"if {Flag(feature)} then ({enabled}) else ({disabled})";
    }

    // Lines end in LF on every platform, so committed output compares equal wherever it was generated.
    static string EmitTemplates(Template[] templates, string space, bool omitEquations)
    {
        var depth = LeanEmitter.RecursionDepth(templates.Max(template => template.Rows[0].Ops.Length));
        var lean = new StringBuilder("import CIL.InstructionEquations\n\n" +
            "/-! Shared bodies for the selected extraction profiles; bindings establish their CIL identity. -/\n\n" +
            $"namespace {space}\nopen CIL\n\nset_option maxRecDepth {depth}\n\n");
        void Line(string text = "") => lean.Append(text).Append('\n');
        for (var index = 0; index < templates.Length; index++)
        {
            var template = templates[index];
            Line($"/-- The stable managed identity of `method{index}`. -/");
            Line($"def method{index}Signature : String := {JsonSerializer.Serialize(template.Identity)}");
            Line("/-- A fixed-PC template for the selected flag combinations, with explicit callee indices. -/");
            lean.Append($"@[cil_code] def method{index} (profile : FeatureProfile)");
            foreach (var feature in template.Features) lean.Append($" ({Flag(feature)} : Bool)");
            for (var callee = 0; callee < template.Callees.Length; callee++) lean.Append($" (callee{callee} : Nat)");
            Line($" : Method := {{ profile, {template.Metadata}, code := [");
            Line(string.Join(",\n", Enumerable.Range(0, template.Rows[0].Ops.Length)
                .Select(pc => "  " + Instruction(template, template.Rows, pc))) + "] }");
            if (!omitEquations)
            {
                Line($"cil_instruction_equations method{index}");
                // The last equation's proof reaches every code suffix, so its axioms include every equation's.
                if (template.Rows[0].Ops.Length is > 0 and var length)
                    Line($"#print axioms method{index}_instruction{length - 1}");
            }
            Line();
        }
        Line($"end {space}");
        return lean.ToString();
    }

    static string EmitBindings(Template[] templates, Dictionary<string, int> templateIndices, Variant variant,
        Options options)
    {
        var lean = new StringBuilder($"import Extracted\nimport {options.ModuleName}\n\n" +
            "/-! Exact bindings for one checked profile extraction; recheck with that extraction. -/\n\n" +
            "namespace TemplateBindings\nopen CIL\n\n");
        void Line(string text) => lean.Append(text).Append('\n');
        var methodIndices = variant.Methods.Select((method, index) => (method.Identity, index))
            .ToDictionary(pair => pair.Identity, pair => pair.index, StringComparer.Ordinal);
        for (var index = 0; index < variant.Methods.Length; index++)
        {
            var templateIndex = templateIndices[variant.Methods[index].Identity];
            var template = templates[templateIndex];
            var arguments = new List<string> { "Extracted.profile" };
            arguments.AddRange(template.Features.Select(feature => variant.Profile.Get(feature) ? "true" : "false"));
            foreach (var callee in template.Callees)
            {
                var target = methodIndices.GetValueOrDefault(callee, -1);
                // A callee absent from this extraction can occur only under an excluded branch.
                arguments.Add(Math.Max(0, target).ToString(System.Globalization.CultureInfo.InvariantCulture));
            }
            Line("/-- This extracted method is exactly the instantiated shared template. -/");
            Line($"@[cil_code] theorem method{index}_template : Extracted.program[{index}]? =");
            Line($"    some ({options.Namespace}.method{templateIndex} {string.Join(' ', arguments)}) := rfl");
            Line($"#print axioms method{index}_template");
        }
        Line("end TemplateBindings");
        return lean.ToString();
    }
}
