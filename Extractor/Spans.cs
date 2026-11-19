using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Span constructors initialize typed local storage without exposing a byte address.
internal static class Spans
{
    internal sealed record Analysis(HashSet<Instruction> Operands, HashSet<Instruction> Interior,
        Dictionary<Instruction, Operation> Constructors);

    // Shape checks do not select an architecture or recompute aggregate layouts.
    internal static bool Is(TypeReference type) =>
        type is GenericInstanceType span && span.ElementType.FullName is "System.Span`1" or "System.ReadOnlySpan`1" &&
        span.GenericArguments.Count == 1 &&
        Arrays.Storage(span.GenericArguments[0]) is not null;

    internal static int? Width(TypeReference type, string architecture) => Is(type)
        ? ElementWidth(((GenericInstanceType)type).GenericArguments[0], architecture) : null;

    // A struct may have different sizes on x64 and ARM64.
    private sealed class ElementLayouts
    {
        internal readonly Dictionary<string, int> Widths = new(StringComparer.Ordinal);
    }

    internal static int? ElementWidth(TypeReference type, string architecture)
    {
        if (Arrays.Storage(type) is { Kind: not NativeOperands.Kind.ArrayComposite } primitive)
            return primitive.Width;
        if (MetadataValidation.IntegerVectorWidth(type) is { } vector) return vector;
        if (!MetadataValidation.IsAggregate(type, type.Module)) return null;
        var widths = EnumTypes.Cached(type, _ => new ElementLayouts()).Widths;
        if (widths.TryGetValue(architecture, out var width)) return width;
        width = MetadataValidation.Layout(type, type.Module, architecture);
        widths.Add(architecture, width);
        return width;
    }
    internal static bool Writable(TypeReference type) =>
        type is GenericInstanceType { ElementType.FullName: "System.Span`1" };

    /// <summary>The array overloads of AsSpan preserve the identity and checked layout of the element.</summary>
    internal static Operation? ArrayExtension(MethodReference reference, string architecture)
    {
        if (reference.Name != "AsSpan" || reference.DeclaringType is TypeSpecification ||
            reference.DeclaringType.FullName != "System.MemoryExtensions" ||
            reference.HasThis || reference.ExplicitThis ||
            !RuntimeModels.ExactScope(reference.DeclaringType, PlatformAssemblies.SystemMemory) ||
            reference is not GenericInstanceMethod { GenericArguments.Count: 1 } method ||
            method.ElementMethod.CallingConvention != MethodCallingConvention.Generic ||
            method.ElementMethod.GenericParameters.Count != 1 || method.Parameters.Count is < 1 or > 3)
            return null;

        var variable = method.ElementMethod.GenericParameters[0];
        if (method.Parameters[0].ParameterType is not ArrayType { IsVector: true } array ||
            array.ElementType != variable || method.ReturnType is not GenericInstanceType result ||
            result.ElementType.FullName != "System.Span`1" || result.GenericArguments.Count != 1 ||
            result.GenericArguments[0] != variable ||
            !RuntimeModels.ExactScope(result.ElementType, PlatformAssemblies.SystemRuntime) ||
            method.Parameters.Skip(1).Any(parameter => parameter.ParameterType.MetadataType != MetadataType.Int32 ||
                !RuntimeModels.ExactScope(parameter.ParameterType, PlatformAssemblies.SystemRuntime)))
            return null;

        if (Arrays.Storage(method.GenericArguments[0], architecture) is not { } element) return null;
        RuntimeModels.ValidateSignature(reference, architecture);
        var range = method.Parameters.Count switch { 1 => ArrayRange.Whole, 2 => ArrayRange.FromStart,
            _ => ArrayRange.Counted };
        return MemoryOperation.Of(new ArraySpan(element, true, range));
    }

    static bool OwnerElement(TypeReference type) =>
        type is GenericParameter { Type: GenericParameterType.Type, Position: 0 };

    static bool DeclaredSpan(TypeReference type, string owner) =>
        type is GenericInstanceType { GenericArguments.Count: 1 } span &&
        span.ElementType.FullName == owner && OwnerElement(span.GenericArguments[0]);

    static bool ElementReference(TypeReference type, bool writable)
    {
        if (!writable)
        {
            if (type is not RequiredModifierType
                { ModifierType.FullName: "System.Runtime.InteropServices.InAttribute" } modifier) return false;
            type = modifier.ElementType;
        }
        return type is ByReferenceType reference && OwnerElement(reference.ElementType);
    }

    /// <summary>A retained span member uses the element of its closed receiver.</summary>
    internal static Operation? Member(MethodReference method, string architecture)
    {
        if (method.DeclaringType is not GenericInstanceType { GenericArguments.Count: 1 } owner ||
            owner.ElementType.FullName is not ("System.Span`1" or "System.ReadOnlySpan`1") ||
            method.HasGenericParameters || method is GenericInstanceMethod || method.ExplicitThis ||
            method.CallingConvention != MethodCallingConvention.Default ||
            method.HasThis == (method.Name is "get_Empty" or "op_Implicit") ||
            !RuntimeModels.ExactScope(owner.ElementType, PlatformAssemblies.SystemRuntime)) return null;

        var name = owner.ElementType.FullName;
        var writable = Writable(owner);
        var parameters = method.Parameters;
        var result = method.ReturnType;
        var element = owner.GenericArguments[0];
        if (method.Name is not ("get_Item" or "get_Length" or "Slice" or "get_IsEmpty" or
            "GetPinnableReference" or "op_Implicit" or "get_Empty" or "Clear" or "Fill" or "CopyTo" or "TryCopyTo"))
            return null;
        if (ElementWidth(element, architecture) is not int width) return null;
        MemoryOperation? operation = method.Name switch
        {
            "Clear" when writable && parameters.Count == 0 && result.MetadataType == MetadataType.Void =>
                new OtherMemory($"(.spanFill {width} true)"),
            "Fill" when writable && parameters.Count == 1 && OwnerElement(parameters[0].ParameterType) &&
                result.MetadataType == MetadataType.Void => new OtherMemory($"(.spanFill {width} false)"),
            "CopyTo" or "TryCopyTo" when parameters.Count == 1 &&
                DeclaredSpan(parameters[0].ParameterType, "System.Span`1") &&
                result.MetadataType == (method.Name == "CopyTo" ? MetadataType.Void : MetadataType.Boolean) =>
                new OtherMemory($"(.spanCopy {width} {LeanText.Bool(method.Name == "TryCopyTo")})"),
            "get_Item" when parameters is [{ ParameterType.MetadataType: MetadataType.Int32 }] &&
                ElementReference(result, writable) => new SpanItem(width),
            "get_Length" when parameters.Count == 0 && result.MetadataType == MetadataType.Int32 => new SpanLength(),
            "Slice" when parameters.Count is 1 or 2 && DeclaredSpan(result, name) &&
                parameters.All(parameter => parameter.ParameterType.MetadataType == MetadataType.Int32) =>
                new SpanSlice(parameters.Count == 2),
            "get_IsEmpty" when parameters.Count == 0 && result.MetadataType == MetadataType.Boolean =>
                new ObserveView(ViewQuery.SpanEmpty),
            "GetPinnableReference" when parameters.Count == 0 && ElementReference(result, writable) =>
                new ObserveView(ViewQuery.SpanPinnable),
            "get_Empty" when parameters.Count == 0 && DeclaredSpan(result, name) => new SpanEmpty(width, writable),
            "op_Implicit" when parameters is [{ ParameterType: ArrayType { IsVector: true } array }] &&
                OwnerElement(array.ElementType) && DeclaredSpan(result, name) &&
                Arrays.Storage(element, architecture) is { } storage =>
                new ArraySpan(storage, writable, ArrayRange.Whole),
            _ => null
        };
        if (operation is null && !(method.Name == "op_Implicit" && writable && parameters.Count == 1 &&
            DeclaredSpan(parameters[0].ParameterType, name) && DeclaredSpan(result, "System.ReadOnlySpan`1")))
            return null;
        RuntimeModels.ValidateSignature(method, architecture);
        return operation is null ? MemoryOperation.Other(".spanReadOnly") : MemoryOperation.Of(operation);
    }

    private sealed class Architectures
    {
        internal readonly Dictionary<string, Analysis> Results = new(StringComparer.Ordinal);
    }

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodDefinition, Architectures> cache = new();

    internal static Analysis Analyze(MethodDefinition method, FeatureProfile profile)
    {
        var results = cache.GetValue(method, static _ => new()).Results;
        if (!results.TryGetValue(profile.Architecture, out var analysis))
        {
            analysis = Compute(method, profile);
            results.Add(profile.Architecture, analysis);
        }
        return analysis;
    }

    static bool Address(Instruction i) => i.OpCode.Code is Code.Ldloca or Code.Ldloca_S;
    static bool Load(Instruction i) => i.OpCode.Code is Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3;
    static bool Push(Instruction? i) => i is not null && (Load(i) || i.OpCode.Code is Code.Ldarg or Code.Ldarg_S or
        Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or Code.Ldarg_3 or Code.Ldc_I4 or Code.Ldc_I4_S or Code.Ldc_I4_M1 ||
        i.OpCode.Code is >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8);

    static Analysis Compute(MethodDefinition method, FeatureProfile profile)
    {
        var analysis = new Analysis([], [], []);
        foreach (var i in method.Body.Instructions)
        {
            if (!Address(i) ||
                !Is(method.Body.Variables[FeatureConstants.Local(i)].VariableType) ||
                analysis.Operands.Contains(i))
                continue;
            var local = FeatureConstants.Local(i);
            if (Constructor(i, method.Body.Variables[local].VariableType, profile) is { } constructor)
            {
                analysis.Operands.Add(i);
                for (var interior = i.Next; interior is not null; interior = interior.Next)
                {
                    analysis.Interior.Add(interior);
                    if (interior != constructor.Call) continue;
                    analysis.Constructors.Add(interior, new InitializeSpanLocal(local, constructor.Source));
                    break;
                }
            }
        }
        return analysis;
    }

    // The local address cannot escape: only bounded single-value pushes precede its exact constructor.
    static (Instruction Call, SpanSource Source)? Constructor(Instruction address, TypeReference localType,
        FeatureProfile profile)
    {
        if (address.Next is { OpCode.Code: Code.Initobj, Operand: TypeReference initialized } reset)
        {
            if (StructuralSignatures.Current.Type(initialized) != StructuralSignatures.Current.Type(localType))
                throw new InvalidDataException("Span default type does not match its local");
            return Width(localType, profile.Architecture) is int width
                ? (reset, new SpanEmpty(width, Writable(localType))) : null;
        }
        var call = address.Next;
        var count = 0;
        while (count < 3 && (Push(call) || call?.OpCode.Code == Code.Ldnull))
        {
            count++;
            call = call!.Next;
        }
        if (call is not { OpCode.Code: Code.Call, Operand: MethodReference reference } ||
            reference.Name != ".ctor" || reference.DeclaringType.FullName != localType.FullName ||
            reference.Parameters.Count != count)
            return null;
        return RuntimeModels.Translate(reference, profile) is Memory { Operation: var model }
            ? model switch
        {
            SpanCreate => (call, new SpanFromReference(1, false)),
            SpanSource source => (call, source),
            _ => null
        } : null;
    }
}
