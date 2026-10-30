using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// A readonly by-reference span parameter carries the referenced view itself, as a span local's
// address does. The callee can neither rebind, address nor store to that home, so the caller's
// span cannot change during the call and reading through the reference equals reading a copy.
internal static class SpanReferences
{
    const string IsReadOnly = "System.Runtime.CompilerServices.IsReadOnlyAttribute";
    const string RequiresLocation = "System.Runtime.CompilerServices.RequiresLocationAttribute";

    internal static bool Is(TypeReference type) => type is ByReferenceType byRef && Spans.Is(byRef.ElementType);

    // `in` and `ref readonly` parameters; `ref` and `out` spans may be replaced by the callee.
    static bool ReadOnly(ParameterDefinition parameter) =>
        parameter.IsIn && !parameter.IsOut && parameter.CustomAttributes.Count(attribute =>
            attribute.AttributeType.FullName is IsReadOnly or RequiresLocation &&
            RuntimeModels.ExactScope(attribute.AttributeType.Scope, "System.Runtime")) == 1;

    internal static void ValidateParameter(MethodDefinition method, ParameterDefinition parameter,
        ModuleDefinition module, string architecture)
    {
        if (!ReadOnly(parameter))
            throw new InvalidDataException("Unsupported writable by-reference span parameter: " +
                parameter.ParameterType.FullName + "\n  Only `in` and `ref readonly` span parameters are admitted: " +
                "a store through `ref` or `out` could replace the caller's span.");
        MetadataValidation.Type(((ByReferenceType)parameter.ParameterType).ElementType, module,
            architecture: architecture);
        if (!method.HasBody) return;
        // Pruned code is checked too: rebinding the reference would make later reads see another home.
        foreach (var instruction in method.Body.Instructions)
            if (instruction.OpCode.Code is Code.Starg or Code.Starg_S or Code.Ldarga or Code.Ldarga_S &&
                instruction.Operand is ParameterDefinition { Index: var index } && index == parameter.Index)
                throw new InvalidDataException("Unsupported store to or address of a readonly span reference: " +
                    instruction);
    }

    // The copied home must be the exact span the preceding instruction addresses.
    internal static void ValidateCopy(MethodDefinition method, Instruction copy, InstructionIndex instructions)
    {
        var type = (TypeReference)copy.Operand;
        var source = copy.Previous switch
        {
            { OpCode.Code: Code.Ldarg or Code.Ldarg_S or Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or
                Code.Ldarg_3 } load =>
                MethodArguments.Type(method, ArgumentIndex(method, load)),
            { OpCode.Code: Code.Ldarga or Code.Ldarga_S, Operand: ParameterDefinition parameter } =>
                new ByReferenceType(parameter.ParameterType),
            { OpCode.Code: Code.Ldloca or Code.Ldloca_S, Operand: VariableDefinition local } =>
                new ByReferenceType(local.VariableType),
            _ => null
        };
        if (source is not ByReferenceType { ElementType: var element } || !Spans.Is(element) ||
            MethodSpecialization.SignatureType(element) != MethodSpecialization.SignatureType(type) ||
            instructions.IsTarget(copy))
            throw new InvalidDataException("Unsupported span copy source: " + copy +
                "\n  The span must be loaded directly from its own argument, parameter or local address.");
    }

    static int ArgumentIndex(MethodDefinition method, Instruction load) => load.OpCode.Code switch
    {
        Code.Ldarg_0 => 0, Code.Ldarg_1 => 1, Code.Ldarg_2 => 2, Code.Ldarg_3 => 3,
        _ => MethodArguments.Index(method, (ParameterDefinition)load.Operand)
    };
}
