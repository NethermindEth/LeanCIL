using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace Nethermind.LeanCIL;

// Templates are proof inputs. Only the generated, kernel-checked bindings connect them to CIL.
internal static partial class TemplateEmitter
{
    /// <summary>One extracted method: its identity, frame, operations and the raw opcode at each pc.</summary>
    internal sealed record Method(string Identity, FrameMetadata Frame, Operation[] Operations, int[] Opcodes);
    internal sealed record Variant(string Directory, string AssemblyHash, FeatureProfile Profile, Method[] Methods)
    {
        internal required string DecoderInputs;
    }
    /// <summary>One profile's frame and body, its callees renumbered to the template's callee parameters.</summary>
    sealed record Row(Variant Variant, FrameMetadata Frame, Operation[] Ops)
    {
        internal required string Body;
    }
    sealed record Template(string Identity, FrameMetadata Frame, Feature[] Features, string[] Callees, Row[] Rows,
        int[] Opcodes);

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
        if (name is not null && !LeanName.IsMatch(name))
            throw new ArgumentException("--namespace takes a Lean name such as Proofs.Generated: " + name);
        var output = Path.GetFullPath(positional[0]);
        var modulePath = Path.GetFullPath(module ?? Path.Combine(output, "Templates.lean"));
        var relative = Path.GetRelativePath(output, modulePath).Replace('\\', '/');
        // The bindings import the module by its path under the output directory, a Lean source root.
        var moduleName = relative.EndsWith(".lean", StringComparison.Ordinal) ? relative[..^".lean".Length]
            .Replace('/', '.') : "";
        if (!LeanName.IsMatch(moduleName))
            throw new ArgumentException("--module takes a .lean file under the output directory whose path " +
                "names a Lean module: " + module);
        return new(output, [.. positional.Skip(1).Select(Path.GetFullPath)], name ?? "Templates", omit, modulePath,
            moduleName, check);
    }

    [GeneratedRegex(@"\A[A-Za-z_][A-Za-z0-9_']*(\.[A-Za-z_][A-Za-z0-9_']*)*\z")]
    internal static partial Regex LeanName { get; }

    [GeneratedRegex(@"\ATemplateBindings[0-9]+\.lean\z")]
    internal static partial Regex BindingName { get; }

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
        var methods = variants.SelectMany((variant, input) => variant.Methods.Select((method, index) =>
            (Variant: variant, Method: method, Body: $"Input{input}.method{index}")))
            .ToLookup(row => row.Method.Identity, StringComparer.Ordinal);
        var templates = methods.OrderBy(group => group.Key, StringComparer.Ordinal)
            .Select(group => Prepare(group.Key, group.ToArray())).ToArray();
        var templateIndices = templates.Select((template, index) => (template.Identity, index))
            .ToDictionary(pair => pair.Identity, pair => pair.index, StringComparer.Ordinal);
        var files = new SortedDictionary<string, string>(StringComparer.Ordinal)
        {
            [options.ModulePath] = EmitTemplates(templates, variants, options.Namespace, options.OmitEquations)
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
                .Where(path => BindingName.IsMatch(Path.GetFileName(path)) &&
                    !files.ContainsKey(Path.GetFullPath(path)))
                .Order(StringComparer.Ordinal).Select(path => "Template output has no input: " + path));
        if (problems.Count > 0) throw new InvalidDataException(string.Join("\n", problems));
    }

    static string Flag(Feature feature) => FeatureProfile.LeanFeature(feature)[1..];

    static string CalleeIdentity(Variant variant, int index) => index >= 0 && index < variant.Methods.Length
        ? variant.Methods[index].Identity
        : throw new InvalidDataException("Templates do not support imported callee slots: method " + index);

    static Template Prepare(string identity, (Variant Variant, Method Method, string Body)[] selected)
    {
        var first = selected[0].Method;
        if (selected.Any(row => row.Method.Operations.Length != first.Operations.Length ||
            !row.Method.Opcodes.AsSpan().SequenceEqual(first.Opcodes)))
            throw new InvalidDataException("Template metadata or instruction count differs between profiles: " +
                identity);
        var features = Enum.GetValues<Feature>().Where(feature => selected.Any(row =>
            row.Method.Operations.Any(operation => operation is ModelCall { Model: FeatureTest test } &&
                test.Feature == feature)))
            .ToArray();
        var callees = selected.SelectMany(row => row.Method.Operations.SelectMany(operation => operation.Methods)
                .Concat(row.Method.Frame.Methods).Select(index => CalleeIdentity(row.Variant, index)))
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var calleeIndices = callees.Select((callee, index) => (callee, index))
            .ToDictionary(pair => pair.callee, pair => pair.index, StringComparer.Ordinal);
        var rows = selected.Select(row =>
        {
            int Renumbered(int index) => calleeIndices[CalleeIdentity(row.Variant, index)];
            return new Row(row.Variant, row.Method.Frame.Renumber(Renumbered),
                [.. row.Method.Operations.Select(operation => operation.Renumber(Renumbered))]) { Body = row.Body };
        }).ToArray();
        // Frames compare once their callees share the template's numbering, as each body does.
        if (rows.Any(row => row.Frame != rows[0].Frame))
            throw new InvalidDataException("Template metadata or instruction count differs between profiles: " +
                identity);
        return new(identity, rows[0].Frame, features, callees, rows, first.Opcodes);
    }

    static string Callee(int index) => $"callee{index}";

    /// <summary>The selected decoder's code, or the raw opcode holes of an unselected combination.</summary>
    static string Code(Template template, Row[] rows, int featureIndex = 0)
    {
        if (rows.Length == 0)
            return $"{template.Rows[0].Body}Closed.code.map (fun site => .unadmitted site.opcode)";
        if (featureIndex == template.Features.Length) return $"{rows[0].Body}.code";
        var feature = template.Features[featureIndex];
        var enabled = Code(template, [.. rows.Where(row => row.Variant.Profile.Get(feature))], featureIndex + 1);
        var disabled = Code(template, [.. rows.Where(row => !row.Variant.Profile.Get(feature))], featureIndex + 1);
        return $"if {Flag(feature)} then ({enabled}) else ({disabled})";
    }

    /// <summary>Profiles with identical flags must agree on the operation and its callee at this pc.</summary>
    static Operation Instruction(Template template, Row[] rows, int pc)
    {
        var values = rows.Select(row => row.Ops[pc]).Distinct().ToArray();
        if (values.Length != 1)
            throw new InvalidDataException($"""
                Profiles with identical observed flags emit different instructions: {template.Identity} at pc {pc}
                """);
        return values[0];
    }

    /// <summary>The table entries of one pc, as a list expression over the template's feature flags.</summary>
    static string LinkEntries(Template template, Row[] rows, int pc, int featureIndex = 0)
    {
        if (rows.Length == 0) return "[]";
        if (featureIndex == template.Features.Length)
            return Instruction(template, rows, pc).Link(Callee) is { } link ? $"[({pc}, {link})]" : "[]";
        var feature = template.Features[featureIndex];
        var enabled = LinkEntries(template, [.. rows.Where(row => row.Variant.Profile.Get(feature))], pc,
            featureIndex + 1);
        var disabled = LinkEntries(template, [.. rows.Where(row => !row.Variant.Profile.Get(feature))], pc,
            featureIndex + 1);
        return enabled == disabled ? enabled : $"if {Flag(feature)} then ({enabled}) else ({disabled})";
    }

    /// <summary>The links field of a template: one entry per call site, in pc order, linear in the code.</summary>
    static string LinkTable(Template template)
    {
        var entries = Enumerable.Range(0, template.Opcodes.Length)
            .Select(pc => LinkEntries(template, template.Rows, pc)).Where(entry => entry != "[]").ToArray();
        return entries.Length == 0 ? "[]" : string.Join(" ++ ", entries.Select(entry => $"({entry})"));
    }

    // Lines end in LF on every platform, so committed output compares equal wherever it was generated.
    static string EmitTemplates(Template[] templates, Variant[] variants, string space, bool omitEquations)
    {
        var depth = LeanEmitter.RecursionDepth(templates.Max(template => template.Opcodes.Length));
        var lean = new StringBuilder();
        void Line(string text = "") => lean.Append(text).Append('\n');
        Line("import CIL.InstructionEquations");
        Line("import CIL.Extraction.TemplateCode");
        Line();
        Line("/-! Shared decoded bodies for the selected extraction profiles. -/");
        Line();
        Line($"namespace {space}");
        Line("open CIL");
        Line($"set_option maxRecDepth {depth}");
        Line();
        for (var input = 0; input < variants.Length; input++)
        {
            Line($"namespace Input{input}");
            lean.Append(variants[input].DecoderInputs);
            Line($"end Input{input}");
            Line();
        }
        for (var index = 0; index < templates.Length; index++)
        {
            var template = templates[index];
            Line($"/-- The stable managed identity of `method{index}`. -/");
            Line($"def method{index}Signature : String := {IdentityText.Quote(template.Identity)}");
            Line("/-- A fixed-PC template for the selected flag combinations, with explicit callee indices. -/");
            lean.Append($"@[cil_code] def method{index} (profile : FeatureProfile) " +
                $"({FrameMetadata.EnvironmentLean} : LayoutEnvironment)");
            foreach (var feature in template.Features) lean.Append($" ({Flag(feature)} : Bool)");
            for (var callee = 0; callee < template.Callees.Length; callee++) lean.Append($" (callee{callee} : Nat)");
            var sites = template.Frame.StaticSitesLeanWith(Callee);
            Line($$""" : Method := { {{template.Rows[0].Body}} with""");
            Line("  profile, environment,");
            Line($"  links := {LinkTable(template)}, staticSites := [{sites}],");
            Line($$"""  code := cil_template_code% ({{Code(template, template.Rows)}}) }""");
            if (!omitEquations)
            {
                Line($"cil_instruction_equations method{index}");
                // The last equation's proof reaches every code suffix, so its axioms include every equation's.
                if (template.Opcodes.Length is > 0 and var length)
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
            var arguments = new List<string> { "Extracted.profile", "Extracted.environment" };
            arguments.AddRange(template.Features.Select(feature => LeanText.Bool(variant.Profile.Get(feature))));
            foreach (var callee in template.Callees)
            {
                var target = methodIndices.GetValueOrDefault(callee, -1);
                // A callee absent from this extraction can occur only under an excluded branch.
                arguments.Add(Math.Max(0, target).ToString(System.Globalization.CultureInfo.InvariantCulture));
            }
            var instance = $"{options.Namespace}.method{templateIndex} {string.Join(' ', arguments)}";
            var method = $"Extracted.method{index}";
            var inputs = $"Extracted.profile Extracted.environment {method}Links {method}Reachable";
            Line("/-- This extracted method is exactly the instantiated shared template. -/");
            Line($"@[cil_code] theorem method{index}_template : Extracted.program[{index}]? =");
            Line($"    some ({instance}) := rfl");
            Line($"#print axioms method{index}_template");
            Line($"""
                theorem method{index}_decoder_eq : Method.ofClosed? {inputs} {method}Closed {method}RawArguments =
                    .ok ({instance}) := {method}_decoder_eq
                #print axioms method{index}_decoder_eq
                theorem method{index}_decoded : Method.ofRaw? {inputs} {method}Original {method}TypeArgumentsRaw =
                    some ({instance}) := {method}_decoded
                #print axioms method{index}_decoded
                theorem method{index}_decoded_code : ({instance}).code =
                    Extraction.methodCode {inputs} {method}Closed := {method}_decoded_code
                #print axioms method{index}_decoded_code
                """.ReplaceLineEndings("\n"));
        }
        Line("end TemplateBindings");
        return lean.ToString();
    }
}
