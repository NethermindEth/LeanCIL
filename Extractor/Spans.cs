using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Span types, their element widths and the span members and constructors the runtime models cover.
internal static class Spans
{
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
        return new ArraySpan(element, true, range);
    }

    static bool OwnerElement(TypeReference type) =>
        type is GenericParameter { Type: GenericParameterType.Type, Position: 0 };

    /// <summary>
    /// The constructor consumes only its explicit arguments and produces a span value. With
    /// <paramref name="staticData"/> a read-only byte span over a pointer must lie in extracted static data.
    /// </summary>
    internal static SpanSource? ConstructorOperation(MethodReference method, string architecture,
        bool staticData = true)
    {
        if (method.Name != ".ctor" || !method.HasThis || method.ExplicitThis || method.HasGenericParameters ||
            method is GenericInstanceMethod || method.CallingConvention != MethodCallingConvention.Default ||
            method.ReturnType.MetadataType != MetadataType.Void ||
            method.DeclaringType is not GenericInstanceType { GenericArguments.Count: 1 } owner ||
            owner.ElementType.FullName is not ("System.Span`1" or "System.ReadOnlySpan`1") ||
            !RuntimeModels.ExactScope(owner.ElementType, PlatformAssemblies.SystemRuntime)) return null;
        var element = owner.GenericArguments[0];
        if (ElementWidth(element, architecture) is not int width) return null;
        var writable = Writable(owner);
        var parameters = method.Parameters;
        SpanSource? operation = parameters switch
        {
            [{ ParameterType: ByReferenceType byref }] when OwnerElement(byref.ElementType) =>
                new SpanSingleReference(width, writable),
            [{ ParameterType: PointerType { ElementType.MetadataType: MetadataType.Void } },
                { ParameterType.MetadataType: MetadataType.Int32 }] =>
                staticData && !writable && element.MetadataType == MetadataType.Byte
                    ? new SpanCreate() : new SpanFromReference(width, writable),
            _ when parameters.Count is 1 or 3 && parameters[0].ParameterType is ArrayType { IsVector: true } array &&
                OwnerElement(array.ElementType) &&
                parameters.Skip(1).All(parameter => parameter.ParameterType.MetadataType == MetadataType.Int32) &&
                Arrays.Storage(element, architecture) is { } storage =>
                new ArraySpan(storage, writable, parameters.Count == 1 ? ArrayRange.Whole : ArrayRange.Counted),
            _ => null
        };
        if (operation is not null) RuntimeModels.ValidateSignature(method, architecture);
        return operation;
    }

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
        Operation? operation = method.Name switch
        {
            "Clear" when writable && parameters.Count == 0 && result.MetadataType == MetadataType.Void =>
                Unoutlined.Site,
            "Fill" when writable && parameters.Count == 1 && OwnerElement(parameters[0].ParameterType) &&
                result.MetadataType == MetadataType.Void => Unoutlined.Site,
            "CopyTo" or "TryCopyTo" when parameters.Count == 1 &&
                DeclaredSpan(parameters[0].ParameterType, "System.Span`1") &&
                result.MetadataType == (method.Name == "CopyTo" ? MetadataType.Void : MetadataType.Boolean) =>
                Unoutlined.Site,
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
        return operation ?? Unoutlined.Site;
    }

    /// <summary>The model of a span constructor that a call runs on a span home; null for any other method.</summary>
    internal static Operation? InPlaceConstructor(MethodReference reference, string architecture) =>
        ConstructorOperation(reference, architecture, staticData: false) is SpanSource source
            ? new SpanInPlace(source) : null;

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodDefinition, HashSet<Instruction>>
        windows = new();

    /// <summary>
    /// The span constructor calls whose receiver is a span home: the address of a local or parameter of the
    /// constructed type, then one simple push per parameter, at most three, and no branch target after the address.
    /// </summary>
    internal static HashSet<Instruction> ConstructorCalls(MethodDefinition method) =>
        windows.GetValue(method, static method => Windows(method));

    static bool Push(Instruction i) => i.OpCode.Code is Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or
        Code.Ldloc_2 or Code.Ldloc_3 or Code.Ldarg or Code.Ldarg_S or Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or
        Code.Ldarg_3 or Code.Ldc_I4 or Code.Ldc_I4_S or Code.Ldc_I4_M1 or Code.Ldnull ||
        i.OpCode.Code is >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8;

    /// <summary>The declared type of the local or parameter whose home <paramref name="address"/> pushes.</summary>
    internal static TypeReference? AddressedType(Instruction? address) => address switch
    {
        { OpCode.Code: Code.Ldloca or Code.Ldloca_S, Operand: VariableDefinition local } => local.VariableType,
        { OpCode.Code: Code.Ldarga or Code.Ldarga_S, Operand: ParameterDefinition parameter } =>
            parameter.ParameterType,
        _ => null
    };

    static HashSet<Instruction> Windows(MethodDefinition method)
    {
        var instructions = new InstructionIndex(method);
        HashSet<Instruction> calls = [];
        foreach (var call in method.Body.Instructions)
        {
            if (call is not { OpCode.Code: Code.Call, Operand: MethodReference { Name: ".ctor" } reference } ||
                !Is(reference.DeclaringType) || reference.Parameters.Count > 3 || instructions.IsTarget(call))
                continue;
            var address = call.Previous;
            var pushes = 0;
            while (pushes < reference.Parameters.Count && address is not null && Push(address) &&
                !instructions.IsTarget(address))
            {
                pushes++;
                address = address.Previous;
            }
            var signatures = StructuralSignatures.Current;
            if (pushes == reference.Parameters.Count && AddressedType(address) is { } addressed &&
                signatures.Type(addressed) == signatures.Type(reference.DeclaringType))
                calls.Add(call);
        }
        return calls;
    }
}
