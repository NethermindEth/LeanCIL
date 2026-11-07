using System.Text;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Named fields of the admitted classes an extraction's methods access, so proofs say `Account.Balance`
// instead of an owner and offset. Each name is checked in Lean against an emitted field operation.
internal static partial class ClassViews
{
    /// <summary>One field access: the method and pc whose emitted operation loads or stores the field.</summary>
    internal sealed record Access(FieldDefinition Field, TypeReference Owner, int Method, int Pc, string Op);

    /// <summary>The access a <c>ldfld</c> or <c>stfld</c> on a class instance field emitted, or none.</summary>
    internal static Access? Of(Instruction instruction, int method, int pc, string op) =>
        instruction is { OpCode.Code: Code.Ldfld or Code.Stfld, Operand: FieldReference field } &&
        FieldOperation().IsMatch(op) && field.Resolve() is { } resolved
            ? new(resolved, field.DeclaringType, method, pc, op) : null;

    /// <summary>
    /// The `Extracted.Classes` namespace: per class, its type and one descriptor per accessed field with a theorem
    /// that the descriptor is the operand of the access it names. Empty when no method accesses a class field.
    /// </summary>
    internal static string Emit(IEnumerable<Access> accesses)
    {
        var classes = accesses.GroupBy(access => access.Owner.FullName, StringComparer.Ordinal)
            .OrderBy(group => group.Key, StringComparer.Ordinal).ToArray();
        if (classes.Length == 0) return "";
        var shortNames = classes.GroupBy(group => ShortName(group.First().Owner), StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.Count(), StringComparer.Ordinal);
        var lean = new StringBuilder();
        lean.AppendLine("namespace Classes");
        foreach (var owner in classes)
        {
            var type = owner.First().Owner;
            var shortName = ShortName(type);
            var path = shortNames[shortName] == 1 ? Identifier(shortName)
                : string.Join('.', type.FullName.Split('.', '/').Select(Identifier));
            lean.AppendLine($"-- The fields of `{type.FullName}` this extraction's methods load or store.");
            lean.AppendLine($"namespace {path}");
            lean.AppendLine($"@[reducible] def type : Extraction.TypeExpr := {GenericEvidence.ObjectType(type)}");
            var used = new HashSet<string>(["type"], StringComparer.Ordinal);
            foreach (var field in owner.GroupBy(access => access.Field)
                .Select(group => group.OrderBy(access => access.Method).ThenBy(access => access.Pc).First())
                .OrderBy(access => ObjectTypes.FieldIndex(type, access.Field)))
            {
                var wanted = FieldName(field.Field);
                var name = wanted;
                for (var suffix = 1; !used.Add(name); suffix++) name = wanted + suffix;
                var operation = FieldOperation().Match(field.Op);
                var offset = operation.Groups["offset"].Value;
                var reference = operation.Groups["kind"].Value.Contains("Reference", StringComparison.Ordinal);
                var descriptor = reference ? "Safety.ReferenceField"
                    : $"Safety.WordField {operation.Groups["width"].Value}";
                lean.AppendLine($"/-- `{field.Field.FieldType.FullName} {type.FullName}::{field.Field.Name}`, " +
                    $"at model offset {offset}. -/");
                lean.AppendLine($"@[reducible] def {Identifier(name)} : {descriptor} := ⟨type, {offset}⟩");
                lean.AppendLine($"theorem {Identifier(name + "_accessed")} : " +
                    $"(method{field.Method}.code[{field.Pc}]?).any {Identifier(name)}.accessedBy = true := " +
                    LeanEmitter.Decide);
            }
            lean.AppendLine($"end {path}");
        }
        lean.AppendLine("end Classes");
        return lean.ToString();
    }

    static string ShortName(TypeReference type) => type.Name;

    /// <summary>The name C# source gives a field: an auto-property's backing field takes its property's.</summary>
    internal static string FieldName(FieldDefinition field) =>
        BackingField().Match(field.Name) is { Success: true } backing ? backing.Groups[1].Value : field.Name;

    [GeneratedRegex(@"\A<([A-Za-z_][A-Za-z0-9_]*)>k__BackingField\z")]
    private static partial Regex BackingField();

    // Metadata names may hold characters Lean identifiers cannot, such as a closure class's `<>c__DisplayClass1_0`.
    static string Identifier(string name) =>
        LeanIdentifier().IsMatch(name) && !Keywords.Contains(name) ? name : $"«{name}»";

    static readonly HashSet<string> Keywords = new(StringComparer.Ordinal)
    {
        "at", "by", "do", "else", "end", "fun", "from", "have", "if", "in", "let", "match", "then", "with",
        "show", "open", "theorem", "def", "where", "import", "namespace", "section", "case", "this", "deriving",
        "instance", "class", "structure", "inductive", "abbrev", "example", "universe", "variable", "mutual",
        "private", "protected", "partial", "unsafe", "noncomputable", "macro", "syntax", "set_option", "Type",
        "Prop", "Sort", "forall", "exists", "calc", "suffices", "obtain", "local", "scoped", "attribute"
    };

    [GeneratedRegex(@"\A[A-Za-z_][A-Za-z0-9_']*\z")]
    private static partial Regex LeanIdentifier();

    [GeneratedRegex(@"\A\.memory \(\.(?<kind>objectField|setObjectField|objectReferenceField|" +
        @"setObjectReferenceField) \(.*\) (?<offset>\d+)(?: (?<width>\d+))?(?: (true|false))?\)\z")]
    private static partial Regex FieldOperation();
}
