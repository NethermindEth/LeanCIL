using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Array identity and physical element shape remain distinct throughout extraction.
internal static class Arrays
{
    /// <summary>
    /// An array element shape. <paramref name="Compound"/> marks a vector, aggregate or enumeration element, whose
    /// Lean term takes arguments and so is parenthesized where it is an argument itself.
    /// </summary>
    internal sealed record Element(string Lean, int Width, bool Signed, NativeOperands.Kind Kind,
        bool Compound = false)
    {
        internal string Expression => Compound ? $"(.{Lean})" : $".{Lean}";
    }

    static readonly Dictionary<string, Element> elements = new(StringComparer.Ordinal)
    {
        ["System.SByte"] = new("signed8", 1, true, NativeOperands.Kind.ArraySigned8),
        ["System.Byte"] = new("unsigned8", 1, false, NativeOperands.Kind.ArrayUnsigned8),
        ["System.Int16"] = new("signed16", 2, true, NativeOperands.Kind.ArraySigned16),
        ["System.UInt16"] = new("unsigned16", 2, false, NativeOperands.Kind.ArrayUnsigned16),
        ["System.Int32"] = new("signed32", 4, false, NativeOperands.Kind.ArraySigned32),
        ["System.UInt32"] = new("unsigned32", 4, false, NativeOperands.Kind.ArrayUnsigned32),
        ["System.Int64"] = new("signed64", 8, false, NativeOperands.Kind.ArraySigned64),
        ["System.UInt64"] = new("unsigned64", 8, false, NativeOperands.Kind.ArrayUnsigned64),
        ["System.IntPtr"] = new("nativeInt", 8, false, NativeOperands.Kind.ArrayNativeInt),
        ["System.UIntPtr"] = new("nativeUInt", 8, false, NativeOperands.Kind.ArrayNativeUInt),
        ["System.Boolean"] = new("boolean", 1, false, NativeOperands.Kind.ArrayBoolean),
        ["System.Char"] = new("character", 2, false, NativeOperands.Kind.ArrayCharacter)
    };

    internal static Element? Primitive(string name) => elements.GetValueOrDefault(name);

    internal static Element? Primitive(TypeReference type) =>
        type is not TypeSpecification ? Primitive(type.FullName) : null;

    internal static Element? Storage(TypeReference type, string? architecture = null)
    {
        if (MetadataValidation.IntegerVectorWidth(type) is { } vectorWidth)
            return new($"vector {IdentityText.Quote(type.FullName)} {vectorWidth}",
                vectorWidth, false, NativeOperands.Kind.ArrayComposite, Compound: true);
        if (MetadataValidation.IsAggregate(type, type.Module))
        {
            if (MetadataValidation.IsByRefLike(type)) return null;
            var width = architecture is null ? 0 : Spans.ElementWidth(type, architecture)!.Value;
            return new($"aggregate {IdentityText.Quote(LayoutEvidence.Identity(type))} {width}",
                width, false, NativeOperands.Kind.ArrayComposite, Compound: true);
        }
        if (!EnumTypes.IsEnum(type)) return Primitive(type);
        return EnumTypes.Cached(type, EnumStorage);
    }

    static Element EnumStorage(TypeReference type)
    {
        var underlying = Primitive(EnumTypes.Storage(type))!;
        var identity = IdentityText.Quote(LayoutEvidence.Identity(type));
        return underlying with { Lean = $"enumeration {identity} .{underlying.Lean}", Compound = true };
    }

    /// <summary>Array.Fill accepts primitive and enum storage with an optional int32 range.</summary>
    internal static Operation? Fill(MethodReference method, string architecture)
    {
        if (method.Name != "Fill" || method.DeclaringType.FullName != "System.Array" || method.HasThis ||
            method.ExplicitThis || method.CallingConvention != MethodCallingConvention.Generic ||
            method is not GenericInstanceMethod { GenericArguments.Count: 1 } generic ||
            generic.ElementMethod.GenericParameters.Count != 1 || method.ReturnType.MetadataType != MetadataType.Void ||
            !RuntimeModels.ExactScope(method.DeclaringType, PlatformAssemblies.SystemRuntime)) return null;

        var parameters = method.Parameters;
        var counted = parameters.Count == 4;
        if (parameters.Count is not (2 or 4) ||
            parameters[0].ParameterType is not ArrayType { IsVector: true } array ||
            !MethodElement(array.ElementType) || !MethodElement(parameters[1].ParameterType) ||
            counted && (parameters[2].ParameterType.MetadataType != MetadataType.Int32 ||
                parameters[3].ParameterType.MetadataType != MetadataType.Int32)) return null;

        var element = generic.GenericArguments[0];
        if (Primitive(element) is null && !EnumTypes.IsEnum(element)) return null;
        RuntimeModels.ValidateSignature(method, architecture);
        return Storage(element, architecture) is null ? null : Unoutlined.Site;

        static bool MethodElement(TypeReference type) =>
            type is GenericParameter { Type: GenericParameterType.Method, Position: 0 };
    }

    internal static Element? Of(TypeReference type, string? architecture = null) =>
        type is ArrayType { IsVector: true } array ? Storage(array.ElementType, architecture) : null;

    internal static LocalKind.Array? StackKind(NativeOperands.Kind kind) =>
        elements.Values.FirstOrDefault(element => element.Kind == kind) is { } element
            ? new LocalKind.Array(element) : null;

    internal static Operation? Translate(Instruction instruction, string architecture) =>
        instruction.OpCode.Code switch
    {
        Code.Newarr when Storage((TypeReference)instruction.Operand, architecture) is
            { Width: > 0 and <= ushort.MaxValue } => new NewArray(null),
        Code.Ldlen => new StackOperation(instruction.OpCode.Code),
        Code.Ldelema => new ElementAddress(ElementStorage(instruction, architecture),
            instruction.Previous?.OpCode.Code == Code.Readonly),
        _ when NumericElement(instruction.OpCode.Code).HasValue => new StackOperation(instruction.OpCode.Code),
        Code.Ldelem_Any => Typed(instruction, false, architecture),
        Code.Stelem_Any => Typed(instruction, true, architecture),
        _ => null
    };

    /// <summary>
    /// A numeric element load or store: its width, whether a load sign-extends, and the step lemma a proof outline
    /// cites for it. <paramref name="Kind"/> is the opcode's suffix, or null for a typed access naming its element
    /// by token, which steps from <paramref name="Shape"/>, the shape fact of its element type.
    /// </summary>
    internal sealed record NumericAccess(int Width, bool Signed, bool Store, NumericKind? Kind, string? Shape = null)
    {
        /// <summary>The lemma stepping a load of an element whose address and load succeed.</summary>
        internal string LoadLemma =>
            Kind is { } kind ? $"step_ldelem_of_element {kind.Term()}" : $"step_ldelem_any_of_element {Typed} rfl";

        /// <summary>The lemma stepping a store into an element whose write succeeds.</summary>
        internal string StoreLemma => (Kind, Width) switch
        {
            ({ } kind, 8) => $"step_stelem_wide_of_write {kind.Term()}",
            ({ } kind, _) => $"step_stelem_narrow_of_write {kind.Term()}",
            (null, 8) => $"step_stelem_any_of_wide_write {Typed} rfl",
            _ => $"step_stelem_any_of_write {Typed} rfl"
        };

        string Typed => Shape ?? throw new InvalidOperationException("A typed element access has no shape fact");
    }

    /// <summary>The integer kind and access direction encoded by a numeric array opcode.</summary>
    static (NumericKind Kind, bool Store)? NumericElement(Code code) => code switch
    {
        Code.Ldelem_I1 => (NumericKind.I1, false),
        Code.Ldelem_U1 => (NumericKind.U1, false),
        Code.Ldelem_I2 => (NumericKind.I2, false),
        Code.Ldelem_U2 => (NumericKind.U2, false),
        Code.Ldelem_I4 => (NumericKind.I4, false),
        Code.Ldelem_U4 => (NumericKind.U4, false),
        Code.Ldelem_I8 => (NumericKind.I8, false),
        Code.Ldelem_I => (NumericKind.I, false),
        Code.Stelem_I1 => (NumericKind.I1, true),
        Code.Stelem_I2 => (NumericKind.I2, true),
        Code.Stelem_I4 => (NumericKind.I4, true),
        Code.Stelem_I8 => (NumericKind.I8, true),
        Code.Stelem_I => (NumericKind.I, true),
        _ => null
    };

    /// <summary>A numeric access uses the method's checked shape for its closed element type.</summary>
    internal static NumericAccess? Numeric(Operation op, int pc, int method = 0) => op switch
    {
        StackOperation raw when NumericElement(raw.Kind) is { } access =>
            new(access.Kind.Width(), access.Kind.Signed(), access.Store, access.Kind),
        TypedElementAccess { Storage: { Kind: not NativeOperands.Kind.ArrayComposite } storage } typed =>
            new(storage.Width, storage.Signed, typed.Store, null,
                $"(cil_element_shape% Extracted.method{method} {pc})"),
        _ => null
    };

    static TypedElementAccess Typed(Instruction instruction, bool store, string architecture) =>
        new(store, ElementStorage(instruction, architecture));

    internal static Element ElementStorage(Instruction instruction, string architecture)
    {
        var element = (TypeReference)instruction.Operand;
        if (ObjectTypes.Candidate(element) || ReferenceArrays.Element(element))
        {
            var operand = $"{instruction.OpCode.Name} {element.FullName}";
            throw new InvalidDataException($"""
                Unsupported typed element access on an array of class references: {operand}
                  Element addresses would expose a reference slot; only ldelem.ref and stelem.ref are modelled.
                """.ReplaceLineEndings("\n"));
        }
        return Storage(element, architecture) ??
            throw new InvalidDataException($"Unsupported array element token: {element}");
    }
}
