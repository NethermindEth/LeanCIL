using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class StaticData
{
    internal static FieldDefinition Validate(FieldReference reference, ModuleDefinition module)
    {
        FieldDefinition field = reference.Resolve() ?? throw new InvalidDataException($"Unresolved static data: {reference.FullName}");
        if (field.IsStatic && field.IsInitOnly && (field.Attributes & FieldAttributes.HasFieldRVA) == 0)
            throw new InvalidDataException($"Unsupported static field address: {reference.FullName}\n  A static readonly field set by its static constructor can be loaded with ldsfld, but its address is not admitted.");
        TypeDefinition layout = field.FieldType.Resolve() ?? throw new InvalidDataException("Unresolved static-data layout");
        if (reference.DeclaringType.Scope != module || reference.DeclaringType is TypeSpecification ||
            reference.DeclaringType.IsValueType != field.DeclaringType.IsValueType ||
            reference.DeclaringType.Resolve() != field.DeclaringType ||
            reference.FieldType.Scope != module || reference.FieldType is TypeSpecification ||
            reference.FieldType.IsValueType != layout.IsValueType || reference.FieldType.Resolve() != layout ||
            field.Module != module || layout.Module != module || !field.IsStatic || !field.IsInitOnly ||
            field.DeclaringType.Fields.Count(candidate => candidate.FullName == field.FullName) != 1 ||
            module.GetTypes().Count(candidate => candidate.FullName == field.DeclaringType.FullName) != 1 ||
            (field.Attributes & FieldAttributes.HasFieldRVA) == 0 || field.InitialValue.Length == 0 ||
            field.RVA == 0 || !layout.IsValueType || !RuntimeModels.HasRuntimeValueTypeBase(layout) || layout.HasGenericParameters ||
            !layout.IsExplicitLayout || layout.PackingSize is not (1 or 2 or 4 or 8) || layout.ClassSize != field.InitialValue.Length ||
            layout.Fields.Any(f => !f.IsStatic) ||
            field.DeclaringType.Methods.Any(m => m.IsConstructor && m.IsStatic) ||
            layout.Methods.Any(m => m.IsConstructor && m.IsStatic))
            throw new InvalidDataException($"Unsupported static data or initialisation: {reference.FullName}");
        // Image bases, section RVAs and file offsets are 512-byte multiples, so RVA alignment survives
        // both mapped and flat loads; CreateSpan<T> throws on data misaligned for sizeof(T).
        if (field.RVA % layout.PackingSize != 0)
            throw new InvalidDataException($"""
                Misaligned static data: {reference.FullName}
                  RVA 0x{field.RVA:X} is not a multiple of its declared packing {layout.PackingSize}.
                """);
        return field;
    }

    /// <summary>The guaranteed alignment of validated static data: its declared packing.</summary>
    internal static int Alignment(FieldDefinition field) => field.FieldType.Resolve().PackingSize;

    internal static string LeanBytes(FieldDefinition field) => LeanBytes(field.InitialValue);

    internal static string LeanBytes(byte[] bytes) =>
        "[" + string.Join(", ", bytes.Select(b => $"(BitVec.ofNat 8 {b})")) + "]";
}
