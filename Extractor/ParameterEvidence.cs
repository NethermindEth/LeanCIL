using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Serialize raw argument metadata and every argument opcode independently of
// ParameterStorage/MethodArguments and the translated instruction strings.
internal static class ParameterEvidence
{
    static string Type(TypeReference type, ModuleDefinition module, LayoutEvidence layouts)
    {
        if (ManagedPointers.Signature(type) is { } signature)
            return $".{(type is ArrayType ? "methodTable" : "methodPointer")} " +
                ManagedPointers.SignatureEvidence(signature);
        if (type is ByReferenceType or PointerType) return ".reference";
        if (Arrays.Of(type) is { } element) return $".array {element.Expression}";
        if (type is GenericInstanceType span && Spans.Is(type) &&
            MetadataValidation.IsAggregate(span.GenericArguments[0], module))
            return $".aggregateSpan {layouts.Index(span.GenericArguments[0])} {(Spans.Writable(type) ? "true" : "false")}";
        if (Spans.Width(type, layouts.Metadata.Architecture) is { } width)
            return $".span {width} {(Spans.Writable(type) ? "true" : "false")}";
        if (type is GenericInstanceType vector && !ValueTuples.Is(type))
            return vector.ElementType.FullName switch
            {
                "System.Runtime.Intrinsics.Vector128`1" => ".vector128",
                "System.Runtime.Intrinsics.Vector256`1" => ".vector256",
                "System.Runtime.Intrinsics.Vector512`1" => ".vector512",
                _ => throw new InvalidDataException("Unsupported raw argument/local type: " + type.FullName)
            };
        return $".field ({layouts.RawFieldType(type, module)})";
    }

    static int Index(MethodDefinition method, Instruction instruction)
    {
        var parameter = (ParameterDefinition)instruction.Operand;
        if (method.HasThis && ReferenceEquals(parameter, method.Body.ThisParameter)) return 0;
        return parameter.Index + (method.HasThis ? 1 : 0);
    }

    internal static void Emit(StringBuilder lean, MethodDefinition method, int number,
        HashSet<Instruction> reachable, LayoutEvidence layouts)
    {
        var dispatch = NativeDispatch.For(method);
        var arguments = new List<string>();
        if (method.HasThis) arguments.Add(".reference");
        arguments.AddRange(method.Parameters.Select(parameter => dispatch.Kind(parameter.ParameterType) ??
            Type(parameter.ParameterType, method.Module, layouts)));
        var locals = method.Body.Variables.Select(local => dispatch.Kind(local.VariableType, local.Index) ??
            Type(local.VariableType, method.Module, layouts));
        var code = method.Body.Instructions.Select(instruction => instruction.OpCode.Code switch
        {
            Code.Ldarg_0 => ".load 0", Code.Ldarg_1 => ".load 1", Code.Ldarg_2 => ".load 2", Code.Ldarg_3 => ".load 3",
            Code.Ldarg or Code.Ldarg_S => $".load {Index(method, instruction)}",
            Code.Starg or Code.Starg_S => $".store {Index(method, instruction)}",
            Code.Ldarga or Code.Ldarga_S => $".address {Index(method, instruction)}",
            _ => ".other"
        });
        lean.AppendLine($"def method{number}RawArguments : Extraction.RawArguments := {{ arguments := [{string.Join(", ", arguments)}], locals := [{string.Join(", ", locals)}], code := [{string.Join(", ", code)}] }}");
        lean.AppendLine($"def method{number}Reachable : List Bool := [{string.Join(", ", method.Body.Instructions.Select(instruction => reachable.Contains(instruction).ToString().ToLowerInvariant()))}]");
        lean.AppendLine($"theorem method{number}_parameters_validated : Extraction.ParameterHomesValid computedLayouts method{number}RawArguments method{number}Reachable method{number} := {LeanEmitter.Decide}");
    }
}
