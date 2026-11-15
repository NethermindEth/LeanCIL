using Mono.Cecil;
using Mono.Cecil.Cil;

namespace Nethermind.LeanCIL;

// Span constructors initialize typed local storage without exposing a byte address.
internal static class Spans
{
    internal sealed record Analysis(HashSet<Instruction> Operands, HashSet<Instruction> Interior,
        Dictionary<Instruction, Operation> Constructors);

    // Shape checks do not select an architecture or recompute aggregate layouts.
    internal static bool Is(TypeReference type) =>
        type is GenericInstanceType span && span.ElementType.FullName is "System.Span`1" or "System.ReadOnlySpan`1" &&
        span.GenericArguments.Count == 1 &&
        Arrays.Storage(span.GenericArguments[0]) is not null;

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

    static bool Address(Instruction i) => i.OpCode.Code is Code.Ldloca or Code.Ldloca_S;
    static bool Load(Instruction i) => i.OpCode.Code is Code.Ldloc or Code.Ldloc_S or Code.Ldloc_0 or Code.Ldloc_1 or Code.Ldloc_2 or Code.Ldloc_3;
    static bool Push(Instruction? i) => i is not null && (Load(i) || i.OpCode.Code is Code.Ldarg or Code.Ldarg_S or
        Code.Ldarg_0 or Code.Ldarg_1 or Code.Ldarg_2 or Code.Ldarg_3 or Code.Ldc_I4 or Code.Ldc_I4_S or Code.Ldc_I4_M1 ||
        i.OpCode.Code is >= Code.Ldc_I4_0 and <= Code.Ldc_I4_8);

    static Analysis Compute(MethodDefinition method, FeatureProfile profile)
    {
        var analysis = new Analysis([], [], []);
        foreach (var i in method.Body.Instructions)
        {
            if (!Address(i) ||
                !Is(method.Body.Variables[FeatureConstants.Local(i)].VariableType) ||
                analysis.Operands.Contains(i))
                continue;
            var local = FeatureConstants.Local(i);
            if (Constructor(i, method.Body.Variables[local].VariableType, profile) is { } constructor)
            {
                analysis.Operands.Add(i);
                for (var interior = i.Next; interior is not null; interior = interior.Next)
                {
                    analysis.Interior.Add(interior);
                    if (interior != constructor.Call) continue;
                    analysis.Constructors.Add(interior, new InitializeSpanLocal(local, constructor.Source));
                    break;
                }
            }
        }
        return analysis;
    }

    // The local address cannot escape: only bounded single-value pushes precede its exact constructor.
    static (Instruction Call, SpanSource Source)? Constructor(Instruction address, TypeReference localType,
        FeatureProfile profile)
    {
        if (address.Next is { OpCode.Code: Code.Initobj, Operand: TypeReference initialized } reset)
        {
            if (StructuralSignatures.Current.Type(initialized) != StructuralSignatures.Current.Type(localType))
                throw new InvalidDataException("Span default type does not match its local");
            return Width(localType, profile.Architecture) is int width
                ? (reset, new SpanEmpty(width, Writable(localType))) : null;
        }
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
        return InstructionTranslation.RuntimeModel(reference, profile) is Memory { Operation: var model }
            ? model switch
        {
            SpanCreate => (call, new SpanFromReference(1, false)),
            SpanSource source and not SpanEmpty => (call, source),
            _ => null
        } : null;
    }
}
