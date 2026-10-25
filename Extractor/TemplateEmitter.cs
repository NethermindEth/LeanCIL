using System.Text;
using System.Text.Json;

namespace Nethermind.LeanCIL;

// Templates are proof inputs. Only the generated, kernel-checked bindings connect them to CIL.
internal static class TemplateEmitter
{
    internal sealed record Method(string Identity, string Metadata, string[] Ops, bool HasStaticSites);
    internal sealed record Variant(string Directory, string AssemblyHash, FeatureProfile Profile, Method[] Methods);
    sealed record Row(Variant Variant, Method Method, string[] Ops);
    sealed record Template(string Identity, string Metadata, Feature[] Features, string[] Callees, Row[] Rows);

    const string MissingProfile = ".unsupported \"Profile combination not selected for template\"";
    const string Usage = "Usage: leancil templates output-directory extraction-directory...";

    internal static void Run(string[] args, Func<string, Variant> read)
    {
        if (args.Length < 2 || args.Any(argument => argument.StartsWith("--", StringComparison.Ordinal)))
            throw new ArgumentException(Usage);
        var output = Path.GetFullPath(args[0]);
        var variants = args[1..].Select(path => read(Path.GetFullPath(path))).ToArray();
        if (variants.Select(variant => variant.AssemblyHash).Distinct(StringComparer.Ordinal).Count() != 1)
            throw new InvalidDataException("Template inputs must come from the same exact assembly.");
        if (variants.Any(variant => variant.Methods.Select(method => method.Identity)
            .Distinct(StringComparer.Ordinal).Count() != variant.Methods.Length))
            throw new InvalidDataException("Template inputs contain ambiguous managed method identities.");
        if (variants.Any(variant => string.Equals(output, variant.Directory, StringComparison.OrdinalIgnoreCase)))
            throw new InvalidDataException("Template output must be separate from its extraction inputs.");
        var identities = variants.SelectMany(variant => variant.Methods).Select(method => method.Identity)
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var templates = identities.Select(identity => Prepare(identity, variants)).ToArray();
        var source = EmitTemplates(templates);
        var bindings = variants.Select(variant => EmitBindings(templates, variant)).ToArray();
        Directory.CreateDirectory(output);
        File.WriteAllText(Path.Combine(output, "Templates.lean"), source, new UTF8Encoding(false));
        for (var index = 0; index < variants.Length; index++)
            File.WriteAllText(Path.Combine(output, $"TemplateBindings{index}.lean"), bindings[index],
                new UTF8Encoding(false));
        File.WriteAllText(Path.Combine(output, "templates.json"), JsonSerializer.Serialize(new
        {
            schema = 1,
            assemblySha256 = variants[0].AssemblyHash,
            profiles = variants.Select((variant, index) => new
            {
                module = $"TemplateBindings{index}",
                extraction = Path.GetRelativePath(output, variant.Directory).Replace('\\', '/'),
                profile = variant.Profile
            }),
            methods = templates.Select((template, index) => new
            {
                name = $"Templates.method{index}", signature = template.Identity,
                flags = template.Features.Select(Flag), callees = template.Callees
            })
        }, new JsonSerializerOptions { WriteIndented = true }), new UTF8Encoding(false));
        Console.WriteLine($"Emitted {templates.Length} shared templates and {bindings.Length} profile bindings.");
        Console.WriteLine("Compile each binding against its recorded extraction; " +
            "templates alone certify no extraction.");
    }

    static string Flag(Feature feature) => FeatureProfile.LeanFeature(feature)[1..];

    static (string Identity, string Prefix, string Tail)? Callee(Variant variant, string op)
    {
        if (op.StartsWith(".newVector256 ", StringComparison.Ordinal))
            throw new InvalidDataException("Templates do not yet support vector constructor calls: " + op);
        var prefix = op.StartsWith(".call ", StringComparison.Ordinal) ? ".call " :
            op.StartsWith(".newAggregate ", StringComparison.Ordinal) ? ".newAggregate " : null;
        if (prefix is null) return null;
        var end = op.IndexOf(' ', prefix.Length);
        if (end < 0 || !int.TryParse(op[prefix.Length..end], out var index) ||
            index < 0 || index >= variant.Methods.Length)
            throw new InvalidDataException("Templates do not support imported callee slots: " + op);
        return (variant.Methods[index].Identity, prefix, op[end..]);
    }

    static Template Prepare(string identity, Variant[] variants)
    {
        var selected = variants.SelectMany(variant => variant.Methods
            .Where(method => method.Identity == identity).Select(method => (Variant: variant, Method: method)))
            .ToArray();
        var first = selected[0].Method;
        if (selected.Any(row => row.Method.HasStaticSites))
            throw new InvalidDataException("Templates do not yet support static-site metadata: " + identity);
        if (selected.Any(row => row.Method.Metadata != first.Metadata ||
            row.Method.Ops.Length != first.Ops.Length))
            throw new InvalidDataException("Template metadata or instruction count differs between profiles: " +
                identity);
        var features = Enum.GetValues<Feature>().Where(feature => selected.Any(row =>
            row.Method.Ops.Contains(".feature " + FeatureProfile.LeanFeature(feature), StringComparer.Ordinal)))
            .ToArray();
        var callees = selected.SelectMany(row => row.Method.Ops.Select(op => Callee(row.Variant, op)))
            .Where(callee => callee is not null).Select(callee => callee!.Value.Identity)
            .Distinct(StringComparer.Ordinal).Order(StringComparer.Ordinal).ToArray();
        var rows = selected.Select(row => new Row(row.Variant, row.Method, row.Method.Ops.Select(op =>
        {
            var callee = Callee(row.Variant, op);
            return callee is null ? op : callee.Value.Prefix +
                "callee" + Array.IndexOf(callees, callee.Value.Identity) + callee.Value.Tail;
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

    static string EmitTemplates(Template[] templates)
    {
        var lean = new StringBuilder("import CIL.InstructionEquations\n\n" +
            "/-! Shared bodies for the selected extraction profiles; bindings establish their CIL identity. -/\n\n" +
            "namespace Templates\nopen CIL\n\nset_option maxRecDepth 4096\n\n");
        for (var index = 0; index < templates.Length; index++)
        {
            var template = templates[index];
            lean.AppendLine($"/-- The stable managed identity of `method{index}`. -/");
            lean.AppendLine($"def method{index}Signature : String := {JsonSerializer.Serialize(template.Identity)}");
            lean.AppendLine("/-- A fixed-PC template for the selected flag combinations, " +
                "with explicit callee indices. -/");
            lean.Append($"@[cil_code] def method{index} (profile : FeatureProfile)");
            foreach (var feature in template.Features) lean.Append($" ({Flag(feature)} : Bool)");
            for (var callee = 0; callee < template.Callees.Length; callee++) lean.Append($" (callee{callee} : Nat)");
            lean.AppendLine($" : Method := {{ profile, {template.Metadata}, code := [");
            lean.AppendLine(string.Join(",\n", Enumerable.Range(0, template.Rows[0].Ops.Length)
                .Select(pc => "  " + Instruction(template, template.Rows, pc))) + "] }");
            lean.AppendLine($"cil_instruction_equations method{index}");
            for (var pc = 0; pc < template.Rows[0].Ops.Length; pc++)
                lean.AppendLine($"#print axioms method{index}_instruction{pc}");
            lean.AppendLine();
        }
        lean.AppendLine("end Templates");
        return lean.ToString();
    }

    static string EmitBindings(Template[] templates, Variant variant)
    {
        var lean = new StringBuilder("import Extracted\nimport Templates\n\n" +
            "/-! Exact bindings for one checked profile extraction; recheck with that extraction. -/\n\n" +
            "namespace TemplateBindings\nopen CIL\n\n");
        for (var index = 0; index < variant.Methods.Length; index++)
        {
            var templateIndex = Array.FindIndex(templates,
                template => template.Identity == variant.Methods[index].Identity);
            var template = templates[templateIndex];
            var arguments = new List<string> { "Extracted.profile" };
            arguments.AddRange(template.Features.Select(feature => variant.Profile.Get(feature) ? "true" : "false"));
            foreach (var callee in template.Callees)
            {
                var target = Array.FindIndex(variant.Methods, method => method.Identity == callee);
                // A callee absent from this extraction can occur only under an excluded branch.
                arguments.Add(Math.Max(0, target).ToString(System.Globalization.CultureInfo.InvariantCulture));
            }
            lean.AppendLine("/-- This extracted method is exactly the instantiated shared template. -/");
            lean.AppendLine($"@[cil_code] theorem method{index}_template : Extracted.program[{index}]? =");
            lean.AppendLine($"    some (Templates.method{templateIndex} {string.Join(' ', arguments)}) := rfl");
            lean.AppendLine($"#print axioms method{index}_template");
        }
        lean.AppendLine("end TemplateBindings");
        return lean.ToString();
    }
}
