using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Folds `stloc s; ldloca s` over a primitive ReadOnlySpan<T> local so the span stays on the stack
// as the receiver of the next span call. Reused locals retain their typed span storage.
internal static class Spans
{
    internal sealed record Analysis(HashSet<Instruction> Operands, HashSet<Instruction> Interior);

    // Primitive span element width; scopes are checked by ValidateTypeIdentity.
    internal static int? Width(TypeReference type) =>
        type is GenericInstanceType span && span.ElementType.FullName is "System.Span`1" or "System.ReadOnlySpan`1" &&
            span.GenericArguments.Count == 1
            ? Arrays.Primitive(span.GenericArguments[0])?.Width
            : null;

    internal static bool Writable(TypeReference type) =>
        type is GenericInstanceType { ElementType.FullName: "System.Span`1" };

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodDefinition, Analysis> cache = new();

    internal static Analysis Analyze(MethodDefinition method) => cache.GetValue(method, Compute);

    static bool Store(Instruction i) => i.OpCode.Code is Code.Stloc or Code.Stloc_S or Code.Stloc_0 or Code.Stloc_1 or Code.Stloc_2 or Code.Stloc_3;
    static bool Address(Instruction i) => i.OpCode.Code is Code.Ldloca or Code.Ldloca_S;
    static bool Load(Instruction i) => i.OpCode.Code is Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3;
    static bool Push(Instruction? i) => i is not null && (Load(i) || i.OpCode.Code is Code.Ldarg or Code.Ldarg_S or
        Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or Code.Ldarg_3 or Code.Ldc_I4 or Code.Ldc_I4_S or Code.Ldc_I4_M1 ||
        i.OpCode.Code is >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8);
    static bool Member(Instruction? i, string name) => i is { OpCode.Code: Code.Call, Operand: MethodReference callee } &&
        callee.HasThis && callee.Name == name && Width(callee.DeclaringType) is not null;

    static Analysis Compute(MethodDefinition method)
    {
        var analysis = new Analysis([], []);
        var uses = new int[method.Body.Variables.Count];
        foreach (var instruction in method.Body.Instructions)
            if (Store(instruction) || Address(instruction) || Load(instruction))
                uses[FeatureConstants.Local(instruction)]++;
        foreach (var i in method.Body.Instructions)
        {
            if (!(Store(i) || Address(i) || Load(i)) || Width(method.Body.Variables[FeatureConstants.Local(i)].VariableType) is null ||
                analysis.Operands.Contains(i))
                continue;
            var local = FeatureConstants.Local(i);
            if (uses[local] != 2)
                continue;
            // The receiver is read once: by get_Length, or by get_Item after one index push.
            if (!Store(i) || i.Next is not { } address || !Address(address) || FeatureConstants.Local(address) != FeatureConstants.Local(i) ||
                !(Member(address.Next, "get_Length") || (Push(address.Next) && Member(address.Next!.Next, "get_Item"))))
                continue;
            analysis.Operands.Add(i);
            analysis.Operands.Add(address);
            analysis.Interior.Add(address);
        }
        return analysis;
    }
}
