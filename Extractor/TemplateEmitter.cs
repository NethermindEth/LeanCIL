using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;

namespace Nethermind.LeanCIL;

// Templates are proof inputs. Only the generated, kernel-checked bindings connect them to CIL.
internal static partial class TemplateEmitter
{
    /// <summary>One decoded method's frame, observed hardware features, raw opcodes and linked method indices.</summary>
    internal sealed record Method(string Identity, FrameMetadata Frame, Feature[] Features, int[] Opcodes,
        int[] LinkedMethods);
    internal sealed record Variant(string Directory, string AssemblyHash, FeatureProfile Profile, Method[] Methods)
    {
        /// <summary>The closed decoder inputs for this extraction in method index order.</summary>
        internal required string DecoderInputs;
    }
    /// <summary>One profile's frame and body, its callees renumbered to the template's callee parameters.</summary>
    sealed record Row(Variant Variant, FrameMetadata Frame, string ComparisonBody)
    {
        /// <summary>The qualified name of the decoded method in the shared module.</summary>
        internal required string Body;
        /// <summary>The decoded body's links with its method indices mapped to template parameters.</summary>
        internal required string RelocatedLinks;
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

    /// <summary>The generated binding filenames checked for stale inputs.</summary>
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

    // Callable signature keys belong to the extraction that interned them. Templates compare
    // these slots on the decoded methods, which retain their types across metadata sessions.
    static bool HasCallableSlots(FrameMetadata frame) =>
        frame.LocalKinds.Any(Callable) || frame.ParameterHomes.Any(home => Callable(home.Kind));

    static bool Callable(LocalKind kind) =>
        kind is LocalKind.MethodPointer or LocalKind.MethodTable or LocalKind.NativeMethodTable;

    static string Flag(Feature feature) => FeatureProfile.LeanFeature(feature)[1..];

    static string CalleeIdentity(Variant variant, int index) => index >= 0 && index < variant.Methods.Length
        ? variant.Methods[index].Identity
        : throw new InvalidDataException("Templates do not support imported callee slots: method " + index);

    static Template Prepare(string identity, (Variant Variant, Method Method, string Body)[] selected)
    {
        var first = selected[0].Method;
        if (selected.Any(row => !row.Method.Opcodes.AsSpan().SequenceEqual(first.Opcodes)))
            throw new InvalidDataException("Template metadata or instruction count differs between profiles: " +
                identity);
        var features = selected.SelectMany(row => row.Method.Features).Distinct().Order().ToArray();
        var callees = selected.SelectMany(row => row.Method.LinkedMethods.Concat(row.Method.Frame.Methods)
                .Select(index => CalleeIdentity(row.Variant, index)))
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var calleeIndices = callees.Select((callee, index) => (callee, index))
            .ToDictionary(pair => pair.callee, pair => pair.index, StringComparer.Ordinal);
        var rows = selected.Select(row =>
        {
            int Renumbered(int index) => calleeIndices[CalleeIdentity(row.Variant, index)];
            string Relocate(Func<int, string> name)
            {
                if (row.Method.LinkedMethods.Length == 0) return row.Body;
                var cases = string.Join(" ", row.Method.LinkedMethods.Select(index =>
                    $"| {index} => {name(Renumbered(index))}"));
                return $"({row.Body}.reindexLinks (fun {cases} | index => index))";
            }
            return new Row(row.Variant, row.Method.Frame.Renumber(Renumbered),
                Relocate(index => index.ToString(System.Globalization.CultureInfo.InvariantCulture)))
                { Body = row.Body, RelocatedLinks = Relocate(Callee) + ".links" };
        }).ToArray();
        // Frames compare once their callees share the template's numbering, as each body does.
        var firstFrame = rows[0].Frame;
        var stableFrame = firstFrame with { LocalKinds = [], ParameterHomes = [] };
        if (rows.Skip(1).Any(row => HasCallableSlots(firstFrame) || HasCallableSlots(row.Frame)
                ? (row.Frame with { LocalKinds = [], ParameterHomes = [] }) != stableFrame
                : row.Frame != firstFrame))
            throw new InvalidDataException("Template metadata or instruction count differs between profiles: " +
                identity);
        return new(identity, rows[0].Frame, features, callees, rows, first.Opcodes);
    }

    static string Callee(int index) => $"callee{index}";

    /// <summary>The decoded code and relocated links selected by the same feature flags.</summary>
    static (string Code, string Links) SelectBody(Template template, Row[] rows,
        List<(string Identity, string Left, string Right)> comparisons, int featureIndex = 0)
    {
        if (rows.Length == 0) return ($"Extraction.templateHoles {template.Rows[0].Body}Closed.code", "[]");
        if (featureIndex == template.Features.Length)
        {
            var selected = rows[0];
            foreach (var other in rows.AsSpan(1))
                comparisons.Add((template.Identity, selected.ComparisonBody, other.ComparisonBody));
            return ($"{selected.Body}.code", selected.RelocatedLinks);
        }
        var feature = template.Features[featureIndex];
        var enabled = SelectBody(template, [.. rows.Where(row => row.Variant.Profile.Get(feature))], comparisons, featureIndex + 1);
        var disabled = SelectBody(template, [.. rows.Where(row => !row.Variant.Profile.Get(feature))], comparisons, featureIndex + 1);
        string Select(string yes, string no) => yes == no ? yes : $"if {Flag(feature)} then ({yes}) else ({no})";
        return (Select(enabled.Code, disabled.Code), Select(enabled.Links, disabled.Links));
    }

    // Lines end in LF on every platform, so committed output compares equal wherever it was generated.
    static string EmitTemplates(Template[] templates, Variant[] variants, string space, bool omitEquations)
    {
        var depth = LeanEmitter.RecursionDepth(templates.Max(template => template.Opcodes.Length));
        var lean = new StringBuilder();
        void Line(string text = "") => lean.Append(text).Append('\n');
        Line("import CIL.InstructionEquations");
        Line("import CIL.Extraction.TemplateCode");
        Line("import CIL.Safety.Linking");
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
        var decoderLength = lean.Length;
        List<(string Identity, string Left, string Right)> comparisons = [];
        List<(string Identity, string Left, string Right)> slots = [];
        for (var index = 0; index < templates.Length; index++)
        {
            var template = templates[index];
            var first = template.Rows[0];
            foreach (var other in template.Rows.AsSpan(1))
                if (HasCallableSlots(first.Frame) || HasCallableSlots(other.Frame))
                    slots.Add((template.Identity, first.Body, other.Body));
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
            var body = SelectBody(template, template.Rows, comparisons);
            Line($"  links := {body.Links}, staticSites := [{sites}],");
            Line($$"""  code := cil_template_code% ({{body.Code}}) }""");
            var callees = Enumerable.Range(0, template.Callees.Length).Select(Callee).ToArray();
            var binders = callees.Length == 0 ? "" : $" ({string.Join(' ', callees)} : Nat)";
            foreach (var (rowIndex, row) in template.Rows.Index())
            {
                var arguments = new List<string> { "profile", "environment" };
                foreach (var feature in template.Features)
                    arguments.Add(LeanText.Bool(row.Variant.Profile.Get(feature)));
                arguments.AddRange(callees);
                var instance = $"(method{index} {string.Join(' ', arguments)})";
                var name = $"method{index}_input{rowIndex}";
                Line("/-- The selected flags give this input's decoded code for every caller. -/");
                Line($"theorem {name}_code (profile : FeatureProfile) (environment : LayoutEnvironment){binders} :");
                Line($"    {instance}.code = {row.Body}.code := rfl");
                Line($"#print axioms {name}_code");
                Line("/-- The selected links enter this input's callees at the supplied method indices. -/");
                Line($"theorem {name}_links (profile : FeatureProfile) (environment : LayoutEnvironment){binders} :");
                Line($"    {instance}.links = {row.RelocatedLinks} := rfl");
                Line($"#print axioms {name}_links");
            }
            if (!omitEquations)
            {
                Line($"cil_instruction_equations method{index}");
                // The last equation's proof reaches every code suffix, so its axioms include every equation's.
                if (template.Opcodes.Length is > 0 and var length)
                    Line($"#print axioms method{index}_instruction{length - 1}");
            }
            Line();
        }
        if (comparisons.Count != 0 || slots.Count != 0)
            global::Program.CheckTemplateBodies(lean.ToString(0, decoderLength), space, comparisons, slots);
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
            Line("/-- This extracted method is exactly the instantiated shared template. -/");
            Line($"@[cil_code] theorem method{index}_template : Extracted.program[{index}]? =");
            Line($"    some ({instance}) := rfl");
            Line($"#print axioms method{index}_template");
        }
        Line("end TemplateBindings");
        return lean.ToString();
    }
}
