using Mono.Cecil;

namespace Nethermind.LeanCIL;

// ValueTuple`2 is auto layout: CoreCLR keeps Item1 before Item2 only when both have the same width.
internal static class ValueTuples
{
    internal static bool Is(TypeReference type) =>
        type is GenericInstanceType { ElementType.FullName: "System.ValueTuple`2", GenericArguments.Count: 2 } tuple &&
        RuntimeModels.ExactScope(tuple.ElementType.Scope, "System.Runtime");

    // Item1 and Item2 with the instance's type arguments, checked against the resolved runtime definition.
    internal static MetadataValidation.InstanceField[] Fields(TypeReference type)
    {
        var tuple = (GenericInstanceType)type;
        var definition = tuple.ElementType.Resolve() ?? throw new InvalidDataException($"Unresolved aggregate: {type.FullName}");
        var fields = definition.Fields.Where(field => !field.IsStatic).ToArray();
        if (!tuple.IsValueType || !tuple.ElementType.IsValueType || !definition.IsValueType || !definition.IsAutoLayout ||
            definition.FullName != "System.ValueTuple`2" || definition.Module.Assembly.Name.Name != "System.Private.CoreLib" ||
            definition.BaseType is not { FullName: "System.ValueType" } || definition.GenericParameters.Count != 2 ||
            definition.PackingSize > 0 || definition.ClassSize > 0 || fields.Length != 2 ||
            fields.Select((field, index) => field.Name == $"Item{index + 1}" &&
                field.FieldType is GenericParameter { Type: GenericParameterType.Type } parameter && parameter.Position == index).Contains(false))
            throw new InvalidDataException($"Unsupported aggregate layout: {type.FullName}");
        return [.. fields.Select((field, index) => new MetadataValidation.InstanceField(field.Name, tuple.GenericArguments[index], field))];
    }

    // Modelled DivRem results store Quotient at offset 0 and Remainder at the element width.
    internal static void RequirePair(TypeReference type, ModuleDefinition module, string architecture = "scalar")
    {
        MetadataValidation.AggregateInfo layout = MetadataValidation.AggregateLayout(type, module, architecture);
        var fields = Fields(type);
        var width = MetadataValidation.PrimitiveWidth(fields[0].Type);
        if (layout.Size != 2 * width || layout.Offsets[fields[0].Definition.FullName] != 0 ||
            layout.Offsets[fields[1].Definition.FullName] != width)
            throw new InvalidDataException($"Unsupported aggregate layout: {type.FullName}");
    }
}
