using Mono.Cecil;
using Mono.Cecil.Cil;
using System.Text.Json;

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
            return new($"vector {JsonSerializer.Serialize(type.FullName)} {vectorWidth}",
                vectorWidth, false, NativeOperands.Kind.ArrayComposite, Compound: true);
        if (MetadataValidation.IsAggregate(type, type.Module))
        {
            if (MetadataValidation.IsByRefLike(type)) return null;
            var width = architecture is null ? 0 : Spans.ElementWidth(type, architecture)!.Value;
            return new($"aggregate {JsonSerializer.Serialize(LayoutEvidence.Identity(type))} {width}",
                width, false, NativeOperands.Kind.ArrayComposite, Compound: true);
        }
        if (!EnumTypes.IsEnum(type)) return Primitive(type);
        return EnumTypes.Cached(type, EnumStorage);
    }

    static Element EnumStorage(TypeReference type)
    {
        var underlying = Primitive(EnumTypes.Storage(type))!;
        var identity = JsonSerializer.Serialize(LayoutEvidence.Identity(type));
        return underlying with { Lean = $"enumeration {identity} .{underlying.Lean}", Compound = true };
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
        Code.Ldlen => new ArrayLength(),
        Code.Ldelema => MemoryOperation.Of(new ArrayAddress(
            Storage((TypeReference)instruction.Operand, architecture) ??
                throw new InvalidDataException("Unsupported array element token: " + instruction.Operand),
            instruction.Previous?.OpCode.Code == Code.Readonly)),
        Code.Ldelem_I1 => new ArrayElementAccess(NumericKind.I1, false),
        Code.Ldelem_U1 => new ArrayElementAccess(NumericKind.U1, false),
        Code.Ldelem_I2 => new ArrayElementAccess(NumericKind.I2, false),
        Code.Ldelem_U2 => new ArrayElementAccess(NumericKind.U2, false),
        Code.Ldelem_I4 => new ArrayElementAccess(NumericKind.I4, false),
        Code.Ldelem_U4 => new ArrayElementAccess(NumericKind.U4, false),
        Code.Ldelem_I8 => new ArrayElementAccess(NumericKind.I8, false),
        Code.Ldelem_I => new ArrayElementAccess(NumericKind.I, false),
        Code.Stelem_I1 => new ArrayElementAccess(NumericKind.I1, true),
        Code.Stelem_I2 => new ArrayElementAccess(NumericKind.I2, true),
        Code.Stelem_I4 => new ArrayElementAccess(NumericKind.I4, true),
        Code.Stelem_I8 => new ArrayElementAccess(NumericKind.I8, true),
        Code.Stelem_I => new ArrayElementAccess(NumericKind.I, true),
        Code.Ldelem_Any => Typed(instruction, false, architecture),
        Code.Stelem_Any => Typed(instruction, true, architecture),
        _ => null
    };

    /// <summary>
    /// A numeric element load or store: its width, whether a load sign-extends, and the step lemma a proof outline
    /// cites for it. <paramref name="Kind"/> is the opcode's suffix, or null for a typed access naming its element
    /// by token.
    /// </summary>
    internal sealed record NumericAccess(int Width, bool Signed, bool Store, NumericKind? Kind)
    {
        /// <summary>The lemma stepping a load of an element whose address and load succeed.</summary>
        internal string LoadLemma =>
            Kind is { } kind ? $"step_ldelem_of_element {kind.Term()}" : "arrayLoad_of_element";

        /// <summary>The lemma stepping a store into an element whose write succeeds.</summary>
        internal string StoreLemma => (Kind, Width) switch
        {
            ({ } kind, 8) => $"step_stelem_wide_of_write {kind.Term()}",
            ({ } kind, _) => $"step_stelem_narrow_of_write {kind.Term()}",
            (null, 8) => "arrayStore_i64_of_write",
            _ => "arrayStore_of_write"
        };
    }

    /// <summary>The numeric element access <paramref name="op"/> performs, or null when it performs none.</summary>
    internal static NumericAccess? Numeric(Operation op) => op switch
    {
        ArrayElementAccess access => new(access.Width, access.Signed, access.Store, access.Kind),
        TypedElementAccess { Storage: { Kind: not NativeOperands.Kind.ArrayComposite } storage } typed =>
            new(storage.Width, storage.Signed, typed.Store, null),
        _ => null
    };

    internal static void ValidateReadOnly(InstructionIndex instructions, Instruction prefix)
    {
        if (prefix.Next is not { OpCode.Code: Code.Ldelema } address || prefix.Operand is not null)
            throw new InvalidDataException("Readonly prefix requires an immediate array element address");
        if (instructions.IsTarget(address))
            throw new InvalidDataException("Branch enters an array address after its readonly prefix");
    }

    static TypedElementAccess Typed(Instruction instruction, bool store, string architecture) =>
        new(store, Storage((TypeReference)instruction.Operand, architecture) ??
            throw new InvalidDataException("Unsupported array element token: " + instruction.Operand));
}
