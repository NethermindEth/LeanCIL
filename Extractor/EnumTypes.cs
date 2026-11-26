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
        readonly Dictionary<ModuleDefinition, ILookup<string, TypeDefinition>> namedTypes = [];

        internal MetadataScope() => activeScope = this;

        internal IEnumerable<TypeDefinition> Namesakes(TypeDefinition type)
        {
            if (!namedTypes.TryGetValue(type.Module, out var names))
            {
                names = type.Module.GetTypes().ToLookup(candidate => candidate.FullName, StringComparer.Ordinal);
                namedTypes.Add(type.Module, names);
            }
            return names[type.FullName];
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
        PinnedAssemblies.Declares(type, type.Module) && type.Resolve() is { IsEnum: true };

    /// <summary>The enum's declaring rows and defining assembly from its pinned image.</summary>
    internal static TypeIdentity Identity(TypeReference reference) => Cached(reference, type =>
    {
        var definition = type.Resolve();
        var pins = PinnedAssemblies.Active ?? throw new InvalidOperationException("Enum identity requires a pinned image.");
        return TypeIdentity.Of(definition, pins.IdentityMetadata(definition.Module));
    });

    internal static TypeReference Storage(TypeReference reference)
    {
        if (!IsEnum(reference)) return reference;
        return Cached(reference, ValidateStorage);
    }

    /// <summary>The Lean `EnumStorage` of an enum, from its validated primitive storage type.</summary>
    internal static string StorageLean(TypeReference reference) => Storage(reference).MetadataType switch
    {
        MetadataType.SByte => ".signed8",
        MetadataType.Byte => ".unsigned8",
        MetadataType.Int16 => ".signed16",
        MetadataType.UInt16 => ".unsigned16",
        MetadataType.Int32 => ".signed32",
        MetadataType.UInt32 => ".unsigned32",
        MetadataType.Int64 => ".signed64",
        MetadataType.UInt64 => ".unsigned64",
        _ => throw new InvalidDataException($"Unsupported enum underlying type: {reference.FullName}")
    };

    // Cecil's display name selects candidates. Only the physical declaring rows identify the enum.
    static bool UniqueDefinition(TypeDefinition type)
    {
        var candidates = activeScope?.Namesakes(type) ??
            type.Module.GetTypes().Where(other => other.FullName == type.FullName);
        bool found = false;
        foreach (var other in candidates)
        {
            if (ReferenceEquals(other, type)) found = true;
            else if (other.MetadataToken.RID == 0 || Identity(other) == Identity(type)) return false;
        }
        return found;
    }

    static TypeReference ValidateStorage(TypeReference reference)
    {
        var type = reference.Resolve();
        var fields = type.Fields.Where(f => !f.IsStatic).ToArray();
        if (!reference.IsValueType || type.HasGenericParameters || !type.IsSealed || type.HasInterfaces ||
            !type.IsAutoLayout ||
            type.BaseType is not { FullName: "System.Enum" } parent ||
            !RuntimeModels.ExactScope(parent, PlatformAssemblies.SystemRuntime) ||
            type.Module != reference.Module || type.Methods.Count != 0 ||
            fields.Length != 1 || fields[0].Name != "value__" ||
            !fields[0].IsSpecialName || !fields[0].IsRuntimeSpecialName ||
            !UniqueDefinition(type))
            throw new InvalidDataException($"Unsupported enum metadata: {reference.FullName}");
        var storage = fields[0].FieldType;
        if (storage is TypeSpecification ||
            !RuntimeModels.ExactScope(storage, PlatformAssemblies.SystemRuntime) ||
            storage.FullName is not ("System.SByte" or "System.Byte" or "System.Int16" or
            "System.UInt16" or "System.Int32" or "System.UInt32" or "System.Int64" or "System.UInt64"))
            throw new InvalidDataException($"Unsupported enum underlying type: {reference.FullName}");
        RuntimeModels.ValidateTypeIdentity(storage, type.Module);
        foreach (var field in type.Fields.Where(f => f.IsStatic))
            if (!field.IsLiteral || !field.HasConstant || field.FieldType is TypeSpecification ||
                field.FieldType.Resolve() != type ||
                field.FieldType.Scope != type.Module)
                throw new InvalidDataException($"Unsupported enum constant: {field.FullName}");
        return storage;
    }
}
