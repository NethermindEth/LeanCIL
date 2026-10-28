using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Array identity and physical integer width are kept together throughout extraction.
internal static class Arrays
{
    internal sealed record Element(string Lean, int Width, bool Signed, NativeOperands.Kind Kind);

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

    internal static Element? Of(TypeReference type) =>
        type is ArrayType { IsVector: true } array ? Primitive(array.ElementType) : null;

    internal static string? StackKind(NativeOperands.Kind kind) =>
        elements.Values.FirstOrDefault(element => element.Kind == kind) is { } element
            ? $".array .{element.Lean}" : null;

    internal static string? Translate(Instruction instruction) => instruction.OpCode.Code switch
    {
        Code.Ldlen => ".memory .arrayLength",
        Code.Ldelema => $".memory (.arrayAddress .{(Primitive((TypeReference)instruction.Operand) ??
            throw new InvalidDataException("Unsupported array element token: " + instruction.Operand)).Lean}" +
            (instruction.Previous?.OpCode.Code == Code.Readonly ? " false)" : ")"),
        Code.Ldelem_I1 => ".memory (.arrayLoad 1 true)",
        Code.Ldelem_U1 => ".memory (.arrayLoad 1 false)",
        Code.Ldelem_I2 => ".memory (.arrayLoad 2 true)",
        Code.Ldelem_U2 => ".memory (.arrayLoad 2 false)",
        Code.Ldelem_I4 or Code.Ldelem_U4 => ".memory (.arrayLoad 4 false)",
        Code.Ldelem_I8 or Code.Ldelem_I => ".memory (.arrayLoad 8 false)",
        Code.Stelem_I1 => ".memory (.arrayStore 1)",
        Code.Stelem_I2 => ".memory (.arrayStore 2)",
        Code.Stelem_I4 => ".memory (.arrayStore 4)",
        Code.Stelem_I8 or Code.Stelem_I => ".memory (.arrayStore 8)",
        Code.Ldelem_Any => Typed(instruction, false),
        Code.Stelem_Any => Typed(instruction, true),
        _ => null
    };

    internal static void ValidateReadOnly(InstructionIndex instructions, Instruction prefix)
    {
        if (prefix.Next is not { OpCode.Code: Code.Ldelema } address || prefix.Operand is not null)
            throw new InvalidDataException("Readonly prefix requires an immediate array element address");
        if (instructions.IsTarget(address))
            throw new InvalidDataException("Branch enters an array address after its readonly prefix");
    }

    static string Typed(Instruction instruction, bool store)
    {
        var element = Primitive((TypeReference)instruction.Operand) ??
            throw new InvalidDataException("Unsupported array element token: " + instruction.Operand);
        return store ? $".memory (.arrayStore {element.Width})" :
            $".memory (.arrayLoad {element.Width} {element.Signed.ToString().ToLowerInvariant()})";
    }
}
