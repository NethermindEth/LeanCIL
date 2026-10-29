using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Folds `stloc s; ldloca s` over a ReadOnlySpan<T> local so the span stays on the stack
// as the receiver of the next span call. Reused locals retain their typed span storage.
internal static class Spans
{
    internal sealed record Analysis(HashSet<Instruction> Operands, HashSet<Instruction> Interior,
        Dictionary<Instruction, string> Constructors);

    // Shape checks do not select an architecture or recompute aggregate layouts.
    internal static bool Is(TypeReference type) =>
        type is GenericInstanceType span && span.ElementType.FullName is "System.Span`1" or "System.ReadOnlySpan`1" &&
        span.GenericArguments.Count == 1 &&
        (Arrays.Storage(span.GenericArguments[0]) is not null ||
            MetadataValidation.IntegerVectorWidth(span.GenericArguments[0]) is not null ||
            MetadataValidation.IsAggregate(span.GenericArguments[0], type.Module));

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

    private sealed class Architectures
    {
        internal readonly Dictionary<string, Analysis> Results = new(StringComparer.Ordinal);
    }

    static readonly System.Runtime.CompilerServices.ConditionalWeakTable<MethodDefinition, Architectures> cache = new();

    internal static Analysis Analyze(MethodDefinition method, FeatureProfile profile)
    {
        var results = cache.GetValue(method, static _ => new()).Results;
        if (!results.TryGetValue(profile.Architecture, out var analysis))
        {
            analysis = Compute(method, profile);
            results.Add(profile.Architecture, analysis);
        }
        return analysis;
    }

    static bool Store(Instruction i) => i.OpCode.Code is Code.Stloc or Code.Stloc_S or Code.Stloc_0 or Code.Stloc_1 or Code.Stloc_2 or Code.Stloc_3;
    static bool Address(Instruction i) => i.OpCode.Code is Code.Ldloca or Code.Ldloca_S;
    static bool Load(Instruction i) => i.OpCode.Code is Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3;
    static bool Push(Instruction? i) => i is not null && (Load(i) || i.OpCode.Code is Code.Ldarg or Code.Ldarg_S or
        Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or Code.Ldarg_3 or Code.Ldc_I4 or Code.Ldc_I4_S or Code.Ldc_I4_M1 ||
        i.OpCode.Code is >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8);
    static bool Member(Instruction? i, string name) => i is { OpCode.Code: Code.Call, Operand: MethodReference callee } &&
        callee.HasThis && callee.Name == name && Is(callee.DeclaringType);

    static Analysis Compute(MethodDefinition method, FeatureProfile profile)
    {
        var analysis = new Analysis([], [], []);
        var uses = new int[method.Body.Variables.Count];
        foreach (var instruction in method.Body.Instructions)
            if (Store(instruction) || Address(instruction) || Load(instruction))
                uses[FeatureConstants.Local(instruction)]++;
        foreach (var i in method.Body.Instructions)
        {
            if (!(Store(i) || Address(i) || Load(i)) ||
                !Is(method.Body.Variables[FeatureConstants.Local(i)].VariableType) ||
                analysis.Operands.Contains(i))
                continue;
            var local = FeatureConstants.Local(i);
            if (Address(i) && Constructor(i, method.Body.Variables[local].VariableType, profile) is { } constructor)
            {
                analysis.Operands.Add(i);
                for (var interior = i.Next; interior is not null; interior = interior.Next)
                {
                    analysis.Interior.Add(interior);
                    if (interior != constructor.Call) continue;
                    analysis.Constructors.Add(interior, $".initializeSpanLocal {local} ({constructor.Descriptor})");
                    break;
                }
                continue;
            }
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

    // The local address cannot escape: only bounded single-value pushes precede its exact constructor.
    static (Instruction Call, string Descriptor)? Constructor(Instruction address, TypeReference localType,
        FeatureProfile profile)
    {
        var call = address.Next;
        var count = 0;
        while (count < 3 && (Push(call) || call?.OpCode.Code == Code.Ldnull))
        {
            count++;
            call = call!.Next;
        }
        if (call is not { OpCode.Code: Code.Call, Operand: MethodReference reference } ||
            reference.Name != ".ctor" || reference.DeclaringType.FullName != localType.FullName ||
            reference.Parameters.Count != count)
            return null;
        var operation = InstructionTranslation.RuntimeModel(reference, profile);
        if (operation == ".memory .spanCreate") return (call, ".reference 1 false");
        const string array = ".memory (.arraySpan ";
        const string pointer = ".memory (.spanFromReference ";
        const string single = ".memory (.spanSingleReference ";
        if (operation?.StartsWith(array, StringComparison.Ordinal) == true)
            return (call, ".array " + operation[array.Length..^1]);
        if (operation?.StartsWith(pointer, StringComparison.Ordinal) == true)
            return (call, ".reference " + operation[pointer.Length..^1]);
        if (operation?.StartsWith(single, StringComparison.Ordinal) == true)
            return (call, ".singleReference " + operation[single.Length..^1]);
        return null;
    }
}
