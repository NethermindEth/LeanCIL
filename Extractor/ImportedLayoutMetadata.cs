using System.Text.Json;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal sealed record ContractLayoutField(string Name, ContractType Type, string Storage, int? Offset);
internal sealed record ContractLayout(string Identity, string Scope, string Name, bool IsValueType,
    ContractType BaseType, bool Explicit, bool Auto, int Packing, int DeclaredSize, ContractLayoutField[] Fields);

internal static class ImportedLayoutMetadata
{
    internal static ContractLayout[] ForType(TypeReference reference, ModuleDefinition selected, string architecture)
    {
        List<ContractLayout> layouts = [];
        Include(Definition(reference, selected), selected, architecture, layouts,
            new HashSet<string>(StringComparer.Ordinal), new HashSet<string>(StringComparer.Ordinal));
        return layouts.ToArray();
    }

    internal static void ValidatePublished(ContractLayout[] layouts)
    {
        if (layouts.Any(layout => layout is null || string.IsNullOrWhiteSpace(layout.Name) ||
                string.IsNullOrWhiteSpace(layout.Scope) || layout.Identity != layout.Scope + "::" + layout.Name ||
                !layout.IsValueType || layout.Fields is null || layout.BaseType is null) ||
            layouts.Select(layout => layout.Identity).Distinct(StringComparer.Ordinal).Count() != layouts.Length)
            throw new InvalidDataException("Invalid or duplicate imported layout metadata.");
        foreach (ContractLayout layout in layouts)
        {
            ContractMethodMetadata.ValidateType(layout.BaseType);
            if (layout.Fields.Any(field => field is null || string.IsNullOrWhiteSpace(field.Name) ||
                    field.Storage is not ("aggregate" or "signed8" or "unsigned8" or "boolean" or "signed16" or
                        "unsigned16" or "character" or "signed32" or "unsigned32" or "signed64" or "unsigned64" or
                        "nativeInt" or "nativeUInt")) ||
                layout.Fields.Select(field => field.Name).Distinct(StringComparer.Ordinal).Count() != layout.Fields.Length)
                throw new InvalidDataException("Invalid imported layout field metadata.");
            foreach (ContractLayoutField field in layout.Fields) ContractMethodMetadata.ValidateType(field.Type);
        }
    }

    internal static ContractLayout[] Signature(MethodReference method, ModuleDefinition selected, string architecture)
    {
        List<TypeDefinition> roots = [];
        foreach (TypeReference parameter in CallReturnType.Parameters(method))
        {
            ContractMethodMetadata.RejectModifiers(parameter);
            if (ContractMethodMetadata.Primitive(parameter)) continue;
            if (parameter is not ByReferenceType reference)
                throw new InvalidDataException("Imported structs require managed-reference parameters: " + parameter.FullName);
            if (!ContractMethodMetadata.Primitive(reference.ElementType)) roots.Add(Definition(reference.ElementType, selected));
        }
        TypeReference returned = CallReturnType.Resolve(method);
        if (returned.MetadataType != MetadataType.Void && !ContractMethodMetadata.Primitive(returned))
            throw new InvalidDataException("Imported returns require void or a primitive integer.");
        List<ContractLayout> layouts = [];
        HashSet<string> active = new(StringComparer.Ordinal);
        HashSet<string> included = new(StringComparer.Ordinal);
        foreach (TypeDefinition root in roots.OrderBy(type => type.FullName, StringComparer.Ordinal))
            Include(root, selected, architecture, layouts, active, included);
        return layouts.ToArray();
    }

    internal static TypeDefinition Definition(TypeReference reference, ModuleDefinition selected)
    {
        bool scope = reference.Scope is ModuleDefinition module ? ReferenceEquals(module, selected) :
            reference.Scope is AssemblyNameReference assembly && assembly.FullName == selected.Assembly.Name.FullName;
        TypeDefinition[] matches = selected.GetTypes().Where(type => type.FullName == reference.FullName).ToArray();
        if (!scope || reference is TypeSpecification || !reference.IsValueType || matches.Length != 1 || !matches[0].IsValueType)
            throw new InvalidDataException("Imported value type is not directly defined in its pinned implementation: " + reference.FullName);
        return matches[0];
    }

    static void Include(TypeDefinition type, ModuleDefinition selected, string architecture, List<ContractLayout> layouts,
        HashSet<string> active, HashSet<string> included)
    {
        string identity = LayoutEvidence.Identity(type);
        if (included.Contains(identity)) return;
        if (active.Count >= 128 || !active.Add(identity))
            throw new InvalidDataException("Recursive imported layout: " + identity);
        MetadataValidation.Layout(type, selected, architecture);
        foreach (MetadataValidation.InstanceField field in MetadataValidation.Fields(type))
            if (MetadataValidation.IsAggregate(field.Type, selected))
                Include(Definition(field.Type, selected), selected, architecture, layouts, active, included);
        ContractLayoutField[] fields = MetadataValidation.Fields(type).Select(field =>
        {
            ContractMethodMetadata.RejectModifiers(field.Type);
            return new ContractLayoutField(field.Name, ContractType.Read(field.Type), Storage(field.Type, selected),
                field.Definition.Offset < 0 ? null : field.Definition.Offset);
        }).ToArray();
        layouts.Add(new(identity, selected.Assembly.Name.FullName, type.FullName, type.IsValueType,
            ContractType.Read(type.BaseType), type.IsExplicitLayout, type.IsAutoLayout,
            type.PackingSize, type.ClassSize, fields));
        active.Remove(identity);
        included.Add(identity);
    }

    static string Storage(TypeReference type, ModuleDefinition selected)
    {
        if (MetadataValidation.IsAggregate(type, selected)) return "aggregate";
        return EnumTypes.Storage(type).FullName switch
        {
            "System.SByte" => "signed8", "System.Byte" => "unsigned8", "System.Boolean" => "boolean",
            "System.Int16" => "signed16", "System.UInt16" => "unsigned16", "System.Char" => "character",
            "System.Int32" => "signed32", "System.UInt32" => "unsigned32",
            "System.Int64" => "signed64", "System.UInt64" => "unsigned64",
            "System.IntPtr" => "nativeInt", "System.UIntPtr" => "nativeUInt",
            _ => throw new InvalidDataException("Unsupported imported layout field: " + type.FullName)
        };
    }

    internal static string RawLean(ContractLayout[] layouts)
    {
        Dictionary<string, int> indices = layouts.Select((layout, index) => (layout.Identity, Index: index))
            .ToDictionary(item => item.Identity, item => item.Index, StringComparer.Ordinal);
        return "[" + string.Join(", ", layouts.Select(layout => "{ identity := " + JsonSerializer.Serialize(layout.Identity) +
            ", explicit := " + Bool(layout.Explicit) + ", auto := " + Bool(layout.Auto) + ", packing := " +
            layout.Packing + ", declaredSize := " + layout.DeclaredSize + ", fields := [" +
            string.Join(", ", layout.Fields.Select(field => "{ type := " + (field.Storage == "aggregate" ?
                ".aggregate " + indices[field.Type.Scope + "::" + field.Type.Name] : "." + field.Storage) +
                ", offset := " + (field.Offset is int offset ? "some " + offset : "none") + " }")) + "] }")) + "]";
    }

    internal static string ComputedLean(ContractLayout[] layouts, ModuleDefinition selected, string architecture) =>
        "#[" + string.Join(", ", layouts.Select(layout =>
        {
            TypeDefinition type = Definition(new TypeReference("", layout.Name, selected, selected) { IsValueType = true }, selected);
            MetadataValidation.AggregateInfo computed = MetadataValidation.AggregateLayout(type, selected, architecture);
            return "⟨⟨" + computed.Size + ", [" + string.Join(", ", MetadataValidation.Fields(type).Select(field =>
                "⟨" + computed.Offsets[field.Definition.FullName] + ", " +
                MetadataValidation.FieldSize(field.Type, selected, architecture) + ", " +
                Bool(MetadataValidation.IsAggregate(field.Type, selected)) + "⟩")) + "]⟩, " + computed.Alignment + "⟩";
        })) + "]";

    internal static int[] Projection(ContractLayout[] layouts, IEnumerable<string> artifactIdentities)
    {
        string[] identities = artifactIdentities.ToArray();
        return layouts.Select(layout =>
        {
            int[] matches = identities.Select((identity, index) => (identity, index))
                .Where(item => item.identity == layout.Identity).Select(item => item.index).ToArray();
            return matches.Length == 1 ? matches[0] :
                throw new InvalidDataException("Missing or duplicate artifact layout: " + layout.Identity);
        }).ToArray();
    }

    static string Bool(bool value) => value ? "true" : "false";
}
