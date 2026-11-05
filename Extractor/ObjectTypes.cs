using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Class instances the checked heap admits: a reference is an allocation identity, and the
// allocation records the runtime type that every field access is checked against.
internal static class ObjectTypes
{
    const string Unsupported = "Unsupported class instance type: ";

    /// <summary>A class declared in a pinned assembly, before checking that its shape is admitted.</summary>
    internal static bool Candidate(TypeReference type) =>
        type is not TypeSpecification and not GenericParameter && !type.IsValueType &&
        (type.Scope is ModuleDefinition || PinnedAssemblies.Active?.ModuleOf(type) is not null);

    /// <summary>The type is an admitted class instance type.</summary>
    internal static bool Is(TypeReference type)
    {
        if (!Candidate(type)) return false;
        try { Validate(type); return true; }
        catch (InvalidDataException) { return false; }
    }

    /// <summary>Rejects a candidate class whose instances the heap model cannot represent, naming why.</summary>
    internal static TypeDefinition Validate(TypeReference type)
    {
        if (!Candidate(type)) throw new InvalidDataException(Unsupported + type.FullName);
        var definition = type.Resolve() ?? throw new InvalidDataException("Unresolved class: " + type.FullName);
        if (definition.IsInterface)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Interface-typed values need interface dispatch, which is not modelled (#477).");
        if (definition.HasGenericParameters)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Generic classes are not modelled.");
        if (definition.IsAbstract)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  An abstract class has no instances without inheritance, which is not modelled.");
        if (definition.BaseType is not { FullName: "System.Object" } parent ||
            !RuntimeModels.ExactScope(parent.Scope, "System.Runtime"))
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Only classes deriving directly from System.Object are modelled; inheritance is not.");
        if (definition.IsExplicitLayout)
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  Explicit class layout is not modelled.");
        if (definition.Methods.Any(method => method.Name == "Finalize" && method.IsVirtual &&
                !method.HasParameters && method.ReturnType.MetadataType == MetadataType.Void))
            throw new InvalidDataException(Unsupported + type.FullName +
                "\n  A finalizer runs outside the extracted call graph.");
        return definition;
    }
}
