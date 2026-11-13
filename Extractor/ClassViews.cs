using System.Text;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Named fields of the admitted classes an extraction's methods access, so proofs say `Account.Balance`
// instead of an owner and offset. Each name is checked in Lean against an emitted field operation.
internal static partial class ClassViews
{
    /// <summary>What a class instance field holds: a word, an object reference, or the origin of a whole array of
    /// a value element.</summary>
    internal enum FieldKind { Word, Reference, Array }

    /// <summary>A class instance field operation as emitted: a load or store at model offset `Offset` of an
    /// instance of `Owner`, of a word of `Width` bytes, an object reference, or an array of `Element`.</summary>
    internal sealed record FieldOperation(bool Store, string Owner, int Offset, FieldKind Kind, int? Width,
        bool Signed, Arrays.Element? Element)
    {
        /// <summary>The Lean memory operation term, parenthesized as an argument.</summary>
        internal string Lean() => Kind switch
        {
            FieldKind.Array
                => $"(.{(Store ? "setArrayField" : "arrayField")} ({Owner}) {Offset} {Element!.Expression})",
            FieldKind.Reference =>
                $"(.{(Store ? "setObjectReferenceField" : "objectReferenceField")} ({Owner}) {Offset})",
            _ when Store => $"(.setObjectField ({Owner}) {Offset} {Width})",
            _ => $"(.objectField ({Owner}) {Offset} {Width} {LeanText.Bool(Signed)})"
        };

        // A store, an array or a reference ignores the sign or width its term leaves out, so two accesses are
        // equal exactly when they render the same, as profiles merged into one template must be.
        public bool Equals(FieldOperation? other) => other is not null && Lean() == other.Lean();

        public override int GetHashCode() => Lean().GetHashCode(StringComparison.Ordinal);
    }

    /// <summary>One field access: the method and pc whose emitted operation loads or stores the field.</summary>
    internal sealed record Access(FieldDefinition Field, TypeReference Owner, int Method, int Pc,
        FieldOperation Operation);

    /// <summary>A named field of a class: where it lives, what it holds, and which methods load and store it.
    /// </summary>
    internal sealed record Field(string Name, int Offset, FieldKind Kind, int? Width, Arrays.Element? Element,
        int[] Loaders,
        int[] Storers)
    {
        /// <summary>The name as a Lean identifier.</summary>
        internal string Lean => Identifier(Name);
    }

    /// <summary>A class's `Extracted.Classes` namespace: its full name, Lean path and named fields.</summary>
    internal sealed record View(string FullName, string Path, string Type, Field[] Fields);

    /// <summary>The access a <c>ldfld</c> or <c>stfld</c> on a class instance field emitted, or none.</summary>
    internal static Access? Of(Instruction instruction, int method, int pc, Operation op) =>
        instruction is { OpCode.Code: Code.Ldfld or Code.Stfld, Operand: FieldReference field } &&
        op is ClassField { Field: var operation } && field.Resolve() is { } resolved
            ? new(resolved, field.DeclaringType, method, pc, operation) : null;

    /// <summary>The views of the classes whose fields the accesses touch, each field named once per class.
    /// </summary>
    internal static View[] Views(IEnumerable<Access> accesses)
    {
        var classes = accesses.GroupBy(access => access.Owner.FullName, StringComparer.Ordinal)
            .OrderBy(group => group.Key, StringComparer.Ordinal).ToArray();
        var shortNames = classes.GroupBy(group => ShortName(group.First().Owner), StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.Count(), StringComparer.Ordinal);
        return [.. classes.Select(owner =>
        {
            var type = owner.First().Owner;
            var shortName = ShortName(type);
            var path = shortNames[shortName] == 1 ? Identifier(shortName)
                : string.Join('.', type.FullName.Split('.', '/').Select(Identifier));
            var used = new HashSet<string>(["type"], StringComparer.Ordinal);
            var fields = owner.GroupBy(access => access.Field)
                .OrderBy(group => ObjectTypes.FieldIndex(type, group.Key))
                .Select(group =>
                {
                    var wanted = FieldName(group.Key);
                    var name = wanted;
                    for (var suffix = 1; !used.Add(name); suffix++) name = wanted + suffix;
                    var operation = group.First().Operation;
                    int[] Methods(bool store) => [.. group.Where(access => access.Operation.Store == store)
                        .Select(access => access.Method).Distinct().Order()];
                    return new Field(name, operation.Offset, operation.Kind, operation.Width, operation.Element,
                        Methods(false), Methods(true));
                }).ToArray();
            return new View(type.FullName, path, GenericEvidence.ObjectType(type), fields);
        })];
    }

    /// <summary>
    /// The `Extracted.Classes` namespace: per class, its type and one descriptor per accessed field with a theorem
    /// that the descriptor is the operand of the access it names. Empty when no method accesses a class field.
    /// </summary>
    internal static string Emit(IEnumerable<Access> accesses, View[] views)
    {
        if (views.Length == 0) return "";
        var first = accesses.GroupBy(access => (access.Owner.FullName, access.Operation.Offset))
            .ToDictionary(group => group.Key,
                group => group.OrderBy(access => access.Method).ThenBy(access => access.Pc).First());
        var lean = new StringBuilder();
        lean.AppendLine("namespace Classes");
        foreach (var view in views)
        {
            lean.AppendLine($"-- The fields of `{view.FullName}` this extraction's methods load or store.");
            lean.AppendLine($"namespace {view.Path}");
            lean.AppendLine($"@[reducible] def type : Extraction.TypeExpr := {view.Type}");
            foreach (var field in view.Fields)
            {
                var access = first[(view.FullName, field.Offset)];
                var descriptor = field.Kind switch
                {
                    FieldKind.Word => $"Safety.WordField {field.Width}",
                    FieldKind.Array => $"Safety.ArrayField {field.Element!.Expression}",
                    _ => "Safety.ReferenceField"
                };
                lean.AppendLine($"/-- `{access.Field.FieldType.FullName} {view.FullName}::{access.Field.Name}`, " +
                    $"at model offset {field.Offset}. -/");
                lean.AppendLine($"@[reducible] def {field.Lean} : {descriptor} := ⟨type, {field.Offset}⟩");
                lean.AppendLine($"theorem {Identifier(field.Name + "_accessed")} : " +
                    $"(method{access.Method}.code[{access.Pc}]?).any {field.Lean}.accessedBy = true := " +
                    LeanEmitter.Decide);
            }
            lean.AppendLine($"end {view.Path}");
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
}
