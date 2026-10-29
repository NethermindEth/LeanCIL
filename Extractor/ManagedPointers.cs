using System.Text.Json;
using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Callable identities retain exact metadata; no numerical address is admitted as a target.
internal static class ManagedPointers
{
    sealed class CatalogCache(IReadOnlyDictionary<MethodDefinition, int> methods)
    {
        internal readonly Dictionary<string, KeyValuePair<MethodDefinition, int>[]> Targets = methods
            .Where(pair => !pair.Key.HasThis && !pair.Key.ExplicitThis &&
                pair.Key.CallingConvention == MethodCallingConvention.Default)
            .GroupBy(pair => SignatureEvidence(pair.Key), StringComparer.Ordinal)
            .ToDictionary(group => group.Key, group => group.ToArray(), StringComparer.Ordinal);
        internal readonly Dictionary<string, string> Expressions = new(StringComparer.Ordinal);
    }

    static readonly ConditionalWeakTable<IReadOnlyDictionary<MethodDefinition, int>, CatalogCache> Catalogs = new();
    internal static FunctionPointerType? Signature(TypeReference type) => type switch
    {
        FunctionPointerType pointer => pointer,
        ArrayType { IsVector: true, ElementType: FunctionPointerType pointer } => pointer,
        _ => null
    };

    internal static void Validate(IMethodSignature signature, ModuleDefinition module, string architecture)
    {
        if (signature.HasThis || signature.ExplicitThis ||
            signature.CallingConvention != MethodCallingConvention.Default)
            throw new InvalidDataException("Unsupported managed pointer calling convention");
        ValidateType(signature.ReturnType, module, architecture, true);
        foreach (var parameter in signature.Parameters)
            ValidateType(parameter.ParameterType, module, architecture, false);
    }

    static void ValidateType(TypeReference type, ModuleDefinition module, string architecture, bool result)
    {
        if (type is ByReferenceType reference)
        {
            if (reference.ElementType is ByReferenceType)
                throw new InvalidDataException("Nested managed pointer reference parameter");
            ValidateType(reference.ElementType, module, architecture, false);
            return;
        }
        var storage = EnumTypes.Storage(type);
        if (!(result && storage.MetadataType == MetadataType.Void) && storage.MetadataType is not
            (MetadataType.Boolean or MetadataType.Char or MetadataType.SByte or MetadataType.Byte or
             MetadataType.Int16 or MetadataType.UInt16 or MetadataType.Int32 or MetadataType.UInt32 or
             MetadataType.Int64 or MetadataType.UInt64 or MetadataType.IntPtr or MetadataType.UIntPtr))
            throw new InvalidDataException("Unsupported managed pointer signature type: " + type.FullName);
        MetadataValidation.Type(type, module, returns: result, architecture: architecture);
    }

    internal static string TypeEvidence(TypeReference type)
    {
        if (type is ByReferenceType reference) return $".byref ({TypeEvidence(reference.ElementType)})";
        if (type.MetadataType == MetadataType.Void) return ".void";
        if (EnumTypes.IsEnum(type))
            return $".enum {JsonSerializer.Serialize(LayoutEvidence.Identity(type))} " +
                $"({TypeEvidence(EnumTypes.Storage(type))})";
        return $".atom {JsonSerializer.Serialize(LayoutEvidence.Scope(type))} " +
            JsonSerializer.Serialize(type.FullName);
    }

    internal static string SignatureEvidence(IMethodSignature signature) =>
        $"{{ result := {TypeEvidence(signature.ReturnType)}, parameters := " +
        $"[{string.Join(", ", signature.Parameters.Select(parameter => TypeEvidence(parameter.ParameterType)))}] }}";

    internal static string IdentityEvidence(MethodDefinition method) =>
        $"{{ owner := {JsonSerializer.Serialize(LayoutEvidence.Identity(method.DeclaringType))}, " +
        $"token := {method.MetadataToken.ToUInt32()}, arguments := " +
        $"[{string.Join(", ", MethodSpecialization.Arguments(method).Select(TypeEvidence))}] }}";

    internal static bool SameSignature(IMethodSignature left, IMethodSignature right) =>
        !left.HasThis && !right.HasThis && !left.ExplicitThis && !right.ExplicitThis &&
        left.CallingConvention == MethodCallingConvention.Default &&
        right.CallingConvention == MethodCallingConvention.Default &&
        TypeEvidence(left.ReturnType) == TypeEvidence(right.ReturnType) &&
        left.Parameters.Select(parameter => TypeEvidence(parameter.ParameterType))
            .SequenceEqual(right.Parameters.Select(parameter => TypeEvidence(parameter.ParameterType)));

    // Inspect a closed address signature before attempting to admit its body or constraints.
    internal static IMethodSignature ReferenceSignature(MethodReference target)
    {
        if (target is not GenericInstanceMethod && target.DeclaringType is not GenericInstanceType) return target;
        var signature = new Mono.Cecil.CallSite(CallReturnType.Resolve(target))
        {
            CallingConvention = target.CallingConvention & ~MethodCallingConvention.Generic,
            HasThis = target.HasThis,
            ExplicitThis = target.ExplicitThis
        };
        foreach (var parameter in CallReturnType.Parameters(target))
            signature.Parameters.Add(new ParameterDefinition(parameter));
        return signature;
    }

    internal static string TargetEvidence(MethodDefinition method, int index) =>
        $"{{ identity := {IdentityEvidence(method)}, method := {index} }}";

    internal static string Catalog(IMethodSignature signature,
        IReadOnlyDictionary<MethodDefinition, int> methods, int caller, bool tail)
    {
        var signatureKey = SignatureEvidence(signature);
        var key = signatureKey + ":" + (tail ? -1 : caller);
        var cache = Catalogs.GetValue(methods, static values => new(values));
        if (cache.Expressions.TryGetValue(key, out var catalog)) return catalog;
        var targets = cache.Targets.GetValueOrDefault(signatureKey, [])
            .Where(pair => tail || pair.Value > caller).ToArray();
        if (targets.Length == 0) throw new InvalidDataException("Empty managed pointer target catalog");
        catalog = "[" + string.Join(", ", targets.Select(pair => TargetEvidence(pair.Key, pair.Value))) + "]";
        cache.Expressions.Add(key, catalog);
        return catalog;
    }

    internal static IEnumerable<MethodReference> AddressedMethods(ModuleDefinition module) =>
        module.GetTypes().SelectMany(type => type.Methods).Where(method => method.HasBody)
            .SelectMany(method => method.Body.Instructions)
            .Where(instruction => instruction.OpCode.Code == Code.Ldftn)
            .Select(instruction => (MethodReference)instruction.Operand);
}
