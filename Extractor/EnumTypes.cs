using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Enums retain their metadata identity, but use their underlying integer storage.
internal static class EnumTypes
{
    [ThreadStatic]
    static MetadataScope? activeScope;

    // A request may specialize method bodies, but enum declarations remain immutable.
    sealed class MetadataScope : IDisposable
    {
        readonly MetadataScope? previous = activeScope;
        internal readonly Dictionary<(TypeReference Reference, Type Descriptor), object> Descriptors = [];
        readonly Dictionary<ModuleDefinition, Dictionary<string, int>> typeCounts = [];

        internal MetadataScope() => activeScope = this;

        internal int Count(TypeDefinition type)
        {
            if (!typeCounts.TryGetValue(type.Module, out var counts))
            {
                counts = type.Module.GetTypes().CountBy(candidate => candidate.FullName, StringComparer.Ordinal)
                    .ToDictionary(StringComparer.Ordinal);
                typeCounts.Add(type.Module, counts);
            }
            return counts.GetValueOrDefault(type.FullName);
        }

        public void Dispose() => activeScope = previous;
    }

    internal static IDisposable BeginScope() => new MetadataScope();

    internal static T Cached<T>(TypeReference reference, Func<TypeReference, T> create) where T : class
    {
        if (activeScope is not { } scope) return create(reference);
        var key = (reference, typeof(T));
        if (scope.Descriptors.TryGetValue(key, out var existing)) return (T)existing;
        var result = create(reference);
        scope.Descriptors.Add(key, result);
        return result;
    }

    internal static bool IsEnum(TypeReference type) => type is not TypeSpecification &&
        type.Scope == type.Module && type.Resolve() is { IsEnum: true };

    internal static TypeReference Storage(TypeReference reference)
    {
        if (!IsEnum(reference)) return reference;
        return Cached(reference, ValidateStorage);
    }

    static TypeReference ValidateStorage(TypeReference reference)
    {
        var type = reference.Resolve();
        var fields = type.Fields.Where(f => !f.IsStatic).ToArray();
        if (!reference.IsValueType || type.HasGenericParameters || !type.IsSealed || type.HasInterfaces ||
            !type.IsAutoLayout ||
            type.BaseType is not { FullName: "System.Enum" } parent ||
            !RuntimeModels.ExactScope(parent.Scope, "System.Runtime") ||
            type.Module != reference.Module || type.Methods.Count != 0 ||
            fields.Length != 1 || fields[0].Name != "value__" ||
            !fields[0].IsSpecialName || !fields[0].IsRuntimeSpecialName ||
            (activeScope?.Count(type) ?? type.Module.GetTypes().Count(t => t.FullName == type.FullName)) != 1)
            throw new InvalidDataException($"Unsupported enum metadata: {reference.FullName}");
        var storage = fields[0].FieldType;
        if (storage is TypeSpecification || !RuntimeModels.ExactScope(storage.Scope, "System.Runtime") ||
            storage.FullName is not ("System.SByte" or "System.Byte" or "System.Int16" or
            "System.UInt16" or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64"))
            throw new InvalidDataException($"Unsupported enum underlying type: {reference.FullName}");
        RuntimeModels.ValidateTypeIdentity(storage, type.Module);
        foreach (var field in type.Fields.Where(f => f.IsStatic))
            if (!field.IsLiteral || !field.HasConstant || field.FieldType.FullName != type.FullName ||
                field.FieldType.Scope != type.Module)
                throw new InvalidDataException($"Unsupported enum constant: {field.FullName}");
        return storage;
    }
}
