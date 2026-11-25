using System.Runtime.CompilerServices;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>A callable stack slot compares by its pinned metadata and carries its Lean rendering for emission.</summary>
internal sealed class CallableSignature(IMethodSignature signature) : IEquatable<CallableSignature>
{
    readonly StructuralSignatures.Signature key = StructuralSignatures.Current.Callable(signature);
    internal string Lean { get; } = ManagedPointers.SignatureEvidence(signature);
    public bool Equals(CallableSignature? other) => other is not null && key == other.key;
    public override bool Equals(object? other) => other is CallableSignature signature && Equals(signature);
    public override int GetHashCode() => key.GetHashCode();
}

/// <summary>
/// A managed method a callable pointer may name: its identity as a Lean term and its index in the extraction.
/// </summary>
internal sealed record ManagedTarget(string Identity, int Method)
{
    /// <summary>The Lean target term, with the method index written as <paramref name="calleeName"/> of it.</summary>
    internal string Lean(Func<int, string> calleeName) =>
        $"{{ identity := {Identity}, method := {calleeName(Method)} }}";
}

// Callable identities retain exact metadata; no numerical address is admitted as a target.
internal static class ManagedPointers
{
    sealed class CatalogCache(IReadOnlyDictionary<MethodDefinition, int> methods)
    {
        internal readonly Dictionary<StructuralSignatures.Signature, KeyValuePair<MethodDefinition, int>[]> Targets = methods
            .Where(pair => !pair.Key.HasThis && !pair.Key.ExplicitThis &&
                pair.Key.CallingConvention == MethodCallingConvention.Default)
            .GroupBy(pair => StructuralSignatures.Current.Callable(pair.Key))
            .ToDictionary(group => group.Key, group => group.ToArray());
        internal readonly Dictionary<(StructuralSignatures.Signature Signature, int Caller), ValueList<ManagedTarget>>
            Catalogs = [];
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
        if (!MetadataValidation.IsAggregate(type, module) &&
            MetadataValidation.IntegerVectorWidth(type) is null &&
            !(result && storage.MetadataType == MetadataType.Void) && storage.MetadataType is not
            (MetadataType.Boolean or MetadataType.Char or MetadataType.SByte or MetadataType.Byte or
             MetadataType.Int16 or MetadataType.UInt16 or MetadataType.Int32 or MetadataType.UInt32 or
             MetadataType.Int64 or MetadataType.UInt64 or MetadataType.IntPtr or MetadataType.UIntPtr))
            throw new InvalidDataException("Unsupported managed pointer signature type: " + type.FullName);
        MetadataValidation.Type(type, module, returns: result, architecture: architecture);
    }

    static string TypeEvidence(TypeReference type)
    {
        if (type is ByReferenceType reference) return $".byref ({TypeEvidence(reference.ElementType)})";
        if (type.MetadataType == MetadataType.Void) return ".void";
        // Callable identity is independent of the extraction's checked layout-table ordering.
        if (MetadataValidation.IsAggregate(type, type.Module))
            return $".aggregate {IdentityText.Quote(LayoutEvidence.Identity(type))} 0";
        if (type is GenericInstanceType generic && MetadataValidation.IntegerVectorWidth(type) is not null)
        {
            var name = GenericEvidence.ClassName(generic.ElementType);
            var element = TypeEvidence(generic.GenericArguments[0]);
            return $".apply (.constructor {GenericEvidence.Scope(generic.ElementType)} {name}) ({element})";
        }
        if (EnumTypes.IsEnum(type))
        {
            var identity = EnumTypes.Identity(type).ToLean();
            return $".enum {identity} {EnumTypes.StorageLean(EnumTypes.Storage(type))}";
        }
        return GenericEvidence.RuntimePrimitive(type) ??
            $".atom {GenericEvidence.Scope(type)} {IdentityText.Quote(type.FullName)}";
    }

    internal static string SignatureEvidence(IMethodSignature signature) =>
        $"{{ result := {TypeEvidence(signature.ReturnType)}, parameters := " +
        $"[{string.Join(", ", signature.Parameters.Select(parameter => TypeEvidence(parameter.ParameterType)))}] }}";

    internal static string IdentityEvidence(MethodDefinition method)
    {
        var owner = IdentityText.Quote(LayoutEvidence.Identity(method.DeclaringType));
        var arguments = string.Join(", ",
            MethodSpecialization.Arguments(method).Select(GenericEvidence.CallableArgument));
        var token = method.MetadataToken.ToUInt32();
        return $$"""{ owner := {{owner}}, token := {{token}}, arguments := [{{arguments}}] }""";
    }

    internal static bool SameSignature(IMethodSignature left, IMethodSignature right) =>
        !left.HasThis && !right.HasThis && !left.ExplicitThis && !right.ExplicitThis &&
        left.CallingConvention == MethodCallingConvention.Default &&
        right.CallingConvention == MethodCallingConvention.Default &&
        StructuralSignatures.Current.Callable(left) == StructuralSignatures.Current.Callable(right);

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

    internal static ManagedTarget Target(MethodDefinition method, int index) =>
        new(IdentityEvidence(method), index);

    internal static ValueList<ManagedTarget> Catalog(IMethodSignature signature,
        IReadOnlyDictionary<MethodDefinition, int> methods, int caller, bool tail)
    {
        var signatureKey = StructuralSignatures.Current.Callable(signature);
        var key = (signatureKey, tail ? -1 : caller);
        var cache = Catalogs.GetValue(methods, static values => new(values));
        if (cache.Catalogs.TryGetValue(key, out var catalog)) return catalog;
        var targets = cache.Targets.GetValueOrDefault(signatureKey, [])
            .Where(pair => tail || pair.Value > caller).ToArray();
        if (targets.Length == 0) throw new InvalidDataException("Empty managed pointer target catalog");
        catalog = [.. targets.Select(pair => Target(pair.Key, pair.Value))];
        cache.Catalogs.Add(key, catalog);
        return catalog;
    }

    internal static IEnumerable<MethodReference> AddressedMethods(ModuleDefinition module) =>
        module.GetTypes().SelectMany(type => type.Methods).Where(method => method.HasBody)
            .SelectMany(method => method.Body.Instructions)
            .Where(instruction => instruction.OpCode.Code == Code.Ldftn)
            .Select(instruction => (MethodReference)instruction.Operand);
}
