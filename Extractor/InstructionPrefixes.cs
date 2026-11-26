using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>The ECMA-335 instruction prefixes, each of which modifies the instruction after it.</summary>
internal static class InstructionPrefixes
{
    internal static bool IsPrefix(Code code) =>
        code is Code.Unaligned or Code.Volatile or Code.Tail or Code.Constrained or Code.No or Code.Readonly;

    internal static bool IsStaticVirtualSlot(MethodDefinition? method) =>
        method is { IsStatic: true, IsVirtual: true, DeclaringType.IsInterface: true };

    internal static void ValidatePrefix(MethodDefinition method, Instruction instruction)
    {
        var next = instruction.Next;
        switch (instruction.OpCode.Code)
        {
            case Code.Unaligned:
                if (instruction.Operand is not byte alignment || alignment is not (1 or 2 or 4) ||
                    next is null || !MemoryPrefixes.SupportedTarget(next))
                    throw new InvalidDataException("Unsupported or malformed unaligned prefix");
                break;
            case Code.Volatile or Code.No:
                throw new InvalidDataException($"Unsupported instruction: {instruction}");
            case Code.Tail:
                var result = next switch
                {
                    { OpCode.Code: Code.Call, Operand: MethodReference direct } => CallReturnType.Resolve(direct),
                    { OpCode.Code: Code.Callvirt, Operand: MethodReference { HasThis: true } instance } =>
                        CallReturnType.Resolve(instance),
                    { OpCode.Code: Code.Calli, Operand: CallSite signature } => signature.ReturnType,
                    _ => null
                };
                var returns = next?.Next is { OpCode.Code: Code.Ret, Operand: null };
                if (instruction.Operand is not null || result is null || !returns)
                    throw new InvalidDataException("Unsupported tail prefix: requires an adjacent call and return");
                if (StructuralSignatures.Current.Type(InitAccessors.Return(result)) !=
                    StructuralSignatures.Current.Type(InitAccessors.Return(method.ReturnType)))
                    throw new InvalidDataException("Unsupported tail prefix: mismatched return type");
                break;
            case Code.Constrained:
                if (instruction.Operand is not TypeReference || next?.Operand is not MethodReference target ||
                    next.OpCode.Code is not (Code.Call or Code.Callvirt))
                    throw new InvalidDataException("Constrained prefix requires an adjacent constrained call");
                // An instance slot is called with callvirt and a static virtual slot with call.
                if (next.OpCode.Code != (target.HasThis ? Code.Callvirt : Code.Call) ||
                    !target.HasThis && !IsStaticVirtualSlot(target.Resolve()))
                    throw new InvalidDataException("Unsupported constrained method slot");
                break;
            case Code.Readonly:
                if (instruction.Operand is not null ||
                    next is not { OpCode.Code: Code.Ldelema, Operand: TypeReference })
                    throw new InvalidDataException("Readonly prefix requires an immediate array element address");
                break;
        }
    }

    /// <summary>
    /// Checks every prefix and rejects branch or switch entry into its taker, including in unreachable code.
    /// </summary>
    internal static void Validate(MethodDefinition method)
    {
        foreach (var instruction in method.Body.Instructions)
        {
            ValidatePrefix(method, instruction);
            Instruction?[] targets = instruction.Operand switch
            {
                Instruction target => [target],
                Instruction[] arms => arms,
                _ => []
            };
            foreach (var target in targets)
                if (target?.Previous is { } prefix && IsPrefix(prefix.OpCode.Code))
                    throw new InvalidDataException($"""
                        Branch enters the instruction after a prefix
                          {instruction} enters {target}, which {prefix.OpCode.Name} modifies.
                        """);
        }
    }
}
