using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Roslyn marks `init` accessors by returning `void modreq(IsExternalInit)`. The modifier only restricts
// which C# callers may bind the accessor: the method returns nothing, exactly as a plain void method.
internal static class InitAccessors
{
    const string Modifier = "System.Runtime.CompilerServices.IsExternalInit";

    // Exactly System.Runtime's IsExternalInit, required directly on a modifier-free System.Void.
    internal static TypeReference? Unwrap(TypeReference type) =>
        type is RequiredModifierType { ModifierType: var modifier, ElementType: var element } &&
        modifier is not TypeSpecification && modifier.FullName == Modifier &&
        RuntimeModels.ExactScope(modifier.Scope, "System.Runtime") &&
        element is not TypeSpecification && element.MetadataType == MetadataType.Void ? element : null;

    internal static bool Is(TypeReference type) => Unwrap(type) is not null;

    // The type a method returns at run time; identity spellings keep the modifier, evidence does not.
    internal static TypeReference Return(TypeReference type) => Unwrap(type) ?? type;
}
