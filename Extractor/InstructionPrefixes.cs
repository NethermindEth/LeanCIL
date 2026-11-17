using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>The ECMA-335 instruction prefixes, each of which modifies the instruction after it.</summary>
internal static class InstructionPrefixes
{
    internal static bool IsPrefix(Code code) =>
        code is Code.Unaligned or Code.Volatile or Code.Tail or Code.Constrained or Code.No or Code.Readonly;

    /// <summary>
    /// Refuses an instruction after <c>readonly.</c> other than the <c>ldelema</c> that alone takes it, and a
    /// <c>readonly.</c> that ends the body, which Lean's decoding and scalar check refuse.
    /// </summary>
    internal static void ValidateTaker(Instruction instruction)
    {
        if (instruction.Previous is { OpCode.Code: Code.Readonly } prefix && instruction.OpCode.Code != Code.Ldelema)
            throw new InvalidDataException("Readonly prefix requires an immediate array element address\n  " +
                $"{instruction} follows {prefix}.");
        if (instruction.OpCode.Code == Code.Readonly && instruction.Next is null)
            throw new InvalidDataException("Readonly prefix requires an immediate array element address\n  " +
                $"{instruction} ends the body.");
    }

    /// <summary>
    /// Refuses a body in which a branch or switch, reachable or not, enters the instruction after a prefix, the
    /// bodies Lean's <c>PrefixEntryFree</c> refuses. A branch to the prefix itself stays allowed.
    /// </summary>
    internal static void ValidateEntry(MethodDefinition method)
    {
        foreach (var instruction in method.Body.Instructions)
        {
            Instruction?[] targets = instruction.Operand switch
            {
                Instruction target => [target],
                Instruction[] arms => arms,
                _ => []
            };
            foreach (var target in targets)
                if (target?.Previous is { } prefix && IsPrefix(prefix.OpCode.Code))
                    throw new InvalidDataException("Branch enters the instruction after a prefix\n  " +
                        $"{instruction} enters {target}, which {prefix.OpCode.Name} modifies.");
        }
    }
}
