using Mono.Cecil;

namespace Nethermind.LeanCIL;

// Only storage whose existing metadata validation excludes references can answer false.
internal static class ReferenceQueries
{
    private sealed class ValidatedStorage
    {
        internal readonly HashSet<(ModuleDefinition Module, string Architecture)> Contexts = [];
    }

    internal static int? Constant(MethodReference reference, string architecture)
    {
        if (reference.Name != "IsReferenceOrContainsReferences" ||
            reference.DeclaringType.FullName != "System.Runtime.CompilerServices.RuntimeHelpers") return null;
        if (!RuntimeModels.ExactScope(reference.DeclaringType.Scope, "System.Runtime") ||
            reference is not GenericInstanceMethod { GenericArguments.Count: 1 } generic ||
            generic.ElementMethod.GenericParameters.Count != 1 || reference.HasThis || reference.ExplicitThis ||
            (generic.ElementMethod.CallingConvention & ~MethodCallingConvention.Generic) !=
                MethodCallingConvention.Default || reference.Parameters.Count != 0 ||
            reference.ReturnType.FullName != "System.Boolean" ||
            generic.ElementMethod.FullName !=
                "System.Boolean System.Runtime.CompilerServices.RuntimeHelpers::IsReferenceOrContainsReferences()")
            throw new InvalidDataException("Unsupported reference-content query signature: " + reference.FullName);
        RuntimeModels.ValidateTypeIdentity(reference.DeclaringType, reference.Module, architecture);
        RuntimeModels.ValidateTypeIdentity(reference.ReturnType, reference.Module, architecture);
        var element = generic.GenericArguments[0];
        var validated = EnumTypes.Cached(element, _ => new ValidatedStorage());
        var context = (reference.Module, architecture);
        if (validated.Contexts.Contains(context)) return 0;
        if (MetadataValidation.IsAggregate(element, reference.Module))
        {
            var layouts = new MetadataValidation.LayoutContext(reference.Module, architecture);
            _ = layouts.Size(element);
        }
        else
        {
            var storage = EnumTypes.Storage(element);
            if (MetadataValidation.IntegerVectorWidth(element) is null &&
                (storage is TypeSpecification || storage.FullName is not
                    ("System.SByte" or "System.Byte" or "System.Boolean" or "System.Char" or
                     "System.Int16" or "System.UInt16" or "System.Int32" or "System.UInt32" or
                     "System.Int64" or "System.UInt64" or "System.IntPtr" or "System.UIntPtr")))
                throw new InvalidDataException("Unsupported reference-content query type: " + element.FullName);
            MetadataValidation.Type(element, reference.Module, architecture: architecture);
        }
        validated.Contexts.Add(context);
        return 0;
    }
}
