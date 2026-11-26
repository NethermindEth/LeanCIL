using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

/// <summary>
/// The exception clauses of a method body in instruction positions, and the structural rules
/// <c>CIL.Extraction.checkRegions</c> decides on them. Lean re-decodes the section and refuses a body that breaks
/// a rule; this check names the rule first.
/// </summary>
internal static class ExceptionClauses
{
    /// <summary>The protected range or handler of one clause, as the half-open positions [Start, Stop).</summary>
    internal sealed record Region(int Start, int Stop, int Clause, bool Handler, bool Finally)
    {
        internal bool Holds(int pc) => Start <= pc && pc < Stop;
    }

    /// <summary>One clause in instruction positions, with its catch class or null for a finally.</summary>
    internal sealed record Clause(int TryStart, int TryEnd, int HandlerStart, int HandlerEnd, TypeReference? CatchType);

    /// <summary>
    /// The clauses of <paramref name="method"/> in table order, with the code end as the stop of a final range.
    /// </summary>
    internal static Clause[] Of(MethodDefinition method)
    {
        var body = method.Body;
        if (!body.HasExceptionHandlers) return [];
        var positions = new InstructionIndex(method);
        int Position(Instruction? instruction) =>
            instruction is null ? body.Instructions.Count : positions.Position(instruction);
        return [.. body.ExceptionHandlers.Select(handler => new Clause(Position(handler.TryStart),
            Position(handler.TryEnd), Position(handler.HandlerStart), Position(handler.HandlerEnd),
            handler.HandlerType == ExceptionHandlerType.Catch ? handler.CatchType : null))];
    }

    /// <summary>
    /// Refuse filter and fault clauses and any body that breaks a rule of <c>checkRegions</c>: misnested clauses, a
    /// return inside a region, a branch that crosses a region boundary, a misplaced <c>endfinally</c> or a
    /// <c>leave</c> out of a finally handler.
    /// </summary>
    internal static void Validate(MethodDefinition method)
    {
        var body = method.Body;
        if (!body.HasExceptionHandlers) return;
        foreach (var handler in body.ExceptionHandlers)
        {
            if (handler.HandlerType is ExceptionHandlerType.Filter or ExceptionHandlerType.Fault)
                throw new InvalidDataException($"""
                    Unsupported exception clause: {handler.HandlerType.ToString().ToLowerInvariant()}
                      Only typed catch and finally clauses are admitted.
                    """.ReplaceLineEndings("\n"));
            if (handler.HandlerType == ExceptionHandlerType.Catch && handler.CatchType is null)
                throw new InvalidDataException("Unsupported exception clause: a catch without a class");
            Instruction?[] boundaries = [handler.TryStart, handler.TryEnd, handler.HandlerStart, handler.HandlerEnd];
            foreach (var boundary in boundaries)
                if (boundary?.Previous is { OpCode.OpCodeType: OpCodeType.Prefix })
                    throw new InvalidDataException("Unsupported exception clause: a boundary after a prefix");
        }
        var clauses = Of(method);
        foreach (var clause in clauses)
            if (clause.TryStart >= clause.TryEnd || clause.HandlerStart >= clause.HandlerEnd ||
                clause.TryEnd > clause.HandlerStart && clause.HandlerEnd > clause.TryStart)
                throw new InvalidDataException("Unsupported exception clause: an empty or overlapping range");
        var regions = Sorted(clauses);
        if (!Nest(regions))
            throw Refusal(method, "the clauses are not disjoint or nested with the inner clause first");
        var code = body.Instructions;
        var positions = new InstructionIndex(method);
        for (var pc = 0; pc < code.Count; pc++)
            if (InstructionError(regions, code.Count, pc, code[pc], positions) is { } error)
                throw Refusal(method, $"IL_{code[pc].Offset:x4} {error}");
    }

    static InvalidDataException Refusal(MethodDefinition method, string reason) => new($"""
        Unsupported exception regions in {method.FullName}: {reason}
        """.ReplaceLineEndings("\n"));

    // Start ascending, then stop descending, then region number descending: every region follows those holding it.
    static Region[] Sorted(Clause[] clauses) => [.. clauses
        .SelectMany((clause, index) => new[]
        {
            new Region(clause.TryStart, clause.TryEnd, index, false, clause.CatchType is null),
            new Region(clause.HandlerStart, clause.HandlerEnd, index, true, clause.CatchType is null)
        })
        .OrderBy(region => region.Start).ThenByDescending(region => region.Stop)
        .ThenByDescending(region => 2 * region.Clause + (region.Handler ? 1 : 0))];

    // Two regions coincide only as the protected range two catch clauses share.
    static bool NestsIn(Region inner, Region outer) =>
        inner.Stop <= outer.Stop && inner.Clause < outer.Clause &&
        (inner.Start != outer.Start || inner.Stop != outer.Stop ||
            !inner.Handler && !outer.Handler && !inner.Finally && !outer.Finally);

    static bool Nest(Region[] regions)
    {
        var enclosing = new Stack<Region>();
        foreach (var region in regions)
        {
            while (enclosing.TryPeek(out var top) && top.Stop <= region.Start) enclosing.Pop();
            if (enclosing.TryPeek(out var holder) && !NestsIn(region, holder)) return false;
            enclosing.Push(region);
        }
        return true;
    }

    static bool EndsFlow(Code code) => code is Code.Jmp or Code.Ret or Code.Br or Code.Br_S or Code.Throw or
        Code.Endfinally or Code.Leave or Code.Leave_S or Code.Endfilter or Code.Rethrow;

    // A transfer from pc to target enters only protected ranges that start at the target.
    static bool EntersAtTry(Region[] regions, int pc, int target) => regions
        .Where(region => region.Holds(target) && !(region.Start == target && !region.Handler))
        .All(region => region.Holds(pc));

    // A transfer from pc to target exits no region.
    static bool StaysIn(Region[] regions, int pc, int target) =>
        regions.Where(region => region.Holds(pc)).All(region => region.Holds(target));

    static Region? Innermost(Region[] regions, int pc) => regions.LastOrDefault(region => region.Holds(pc));

    static string? InstructionError(Region[] regions, int count, int pc, Instruction instruction,
        InstructionIndex positions)
    {
        var code = instruction.OpCode.Code;
        var leave = code is Code.Leave or Code.Leave_S;
        var inner = Innermost(regions, pc);
        int[] targets = instruction.Operand switch
        {
            Instruction target => [positions.Position(target)],
            Instruction[] cases => [.. cases.Select(positions.Position)],
            _ => []
        };
        var inHandler = regions.Any(region => region.Handler && region.Holds(pc));
        if (inner is not null && code is Code.Jmp or Code.Ret or Code.Tail || inHandler && code == Code.Localloc)
            return $"{instruction.OpCode.Name} inside an exception region";
        if (code == Code.Endfinally && inner is not { Handler: true, Finally: true })
            return "endfinally outside a finally handler";
        var finallyHandler = regions.LastOrDefault(region => region.Handler && region.Finally && region.Holds(pc));
        if (leave && finallyHandler is not null && targets.Any(target => !finallyHandler.Holds(target)))
            return "leave out of a finally handler";
        var branches = targets.All(target =>
            EntersAtTry(regions, pc, target) && (leave || StaysIn(regions, pc, target)));
        var falls = EndsFlow(code) || (pc + 1 < count
            ? EntersAtTry(regions, pc, pc + 1) && StaysIn(regions, pc, pc + 1)
            : inner is null);
        return branches && falls ? null : "control crosses a region boundary other than by leave or a try start";
    }
}
