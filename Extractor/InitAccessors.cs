using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Roslyn marks `init` accessors by returning `void modreq(IsExternalInit)`. The modifier only restricts
// which C# callers may bind the accessor: the method returns nothing, exactly as a plain void method.
internal static class InitAccessors
{
    const string Modifier = "System.Runtime.CompilerServices.IsExternalInit";

    // Roslyn binds the marker by full name from any assembly, since libraries for older frameworks
    // declare their own; it carries no IL semantics wherever it is declared.
    internal static TypeReference? Unwrap(TypeReference type) =>
        type is RequiredModifierType { ModifierType: var modifier, ElementType: var element } &&
        modifier is not TypeSpecification && modifier.DeclaringType is null && modifier.FullName == Modifier &&
        element is not TypeSpecification && element.MetadataType == MetadataType.Void ? element : null;

    internal static bool Is(TypeReference type) => Unwrap(type) is not null;

    // The type a method returns at run time; identity spellings keep the modifier, evidence does not.
    internal static TypeReference Return(TypeReference type) => Unwrap(type) ?? type;
}
