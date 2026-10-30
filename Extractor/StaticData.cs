using System.Reflection.PortableExecutable;
using System.Runtime.CompilerServices;
using Mono.Cecil;

namespace Nethermind.LeanCIL;

internal static class StaticData
{
    /// <summary>The largest admitted packing, and so the widest alignment static data may promise.</summary>
    const uint MaximumPacking = 8;

    static readonly ConditionalWeakTable<ModuleDefinition, SectionHeader[]> sections = new();

    /// <summary>
    /// Reads a module from its image and records the image's section headers, which <see cref="Validate"/>
    /// requires to admit any static data of that module.
    /// </summary>
    internal static ModuleDefinition ReadModule(byte[] assembly)
    {
        SectionHeader[] headers;
        using (PEReader image = new(new MemoryStream(assembly, writable: false)))
            headers = [.. image.PEHeaders.SectionHeaders];
        ModuleDefinition module = ModuleDefinition.ReadModule(new MemoryStream(assembly, writable: false));
        sections.AddOrUpdate(module, headers);
        return module;
    }

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
        // CreateSpan<T> throws on data misaligned for sizeof(T): the RVA must be a multiple of the packing,
        // and its section must keep that residue at the file offset a flat layout reads it from.
        if (field.RVA % layout.PackingSize != 0)
            throw new InvalidDataException($"""
                Misaligned static data: {reference.FullName}
                  RVA 0x{field.RVA:X} is not a multiple of its declared packing {layout.PackingSize}.
                """);
        RequireSectionAligned(reference, field, module);
        return field;
    }

    /// <summary>
    /// Requires the field's data to lie within one section's raw data and mapped extent, in a section whose
    /// virtual address and file offset agree modulo <see cref="MaximumPacking"/>.
    /// </summary>
    static void RequireSectionAligned(FieldReference reference, FieldDefinition field, ModuleDefinition module)
    {
        if (!sections.TryGetValue(module, out SectionHeader[]? headers))
            throw new InvalidDataException($"Static data without a recorded image: {reference.FullName}");
        long start = (uint)field.RVA, end = start + field.InitialValue.Length;
        SectionHeader[] containing = [.. headers.Where(header => header.VirtualAddress <= start &&
            start < (long)header.VirtualAddress + Math.Max(header.VirtualSize, header.SizeOfRawData))];
        if (containing.Length != 1)
            throw new InvalidDataException($"""
                Static data outside any section: {reference.FullName}
                  RVA 0x{start:X} lies in {containing.Length} sections of the image.
                """);
        SectionHeader section = containing[0];
        long rawEnd = (long)section.VirtualAddress + section.SizeOfRawData;
        long mappedEnd = section.VirtualSize == 0 ? rawEnd : (long)section.VirtualAddress + section.VirtualSize;
        if (end > Math.Min(rawEnd, mappedEnd))
            throw new InvalidDataException($"""
                Static data beyond its section's raw data: {reference.FullName}
                  RVA 0x{start:X}..0x{end:X} exceeds section {section.Name}, which holds raw data to 0x{rawEnd:X}
                  and maps to 0x{mappedEnd:X}.
                """);
        string fileOffset = $"0x{section.PointerToRawData:X}";
        if (((long)section.VirtualAddress - section.PointerToRawData) % MaximumPacking != 0)
            throw new InvalidDataException($"""
                Static data section misaligned: {reference.FullName}
                  Section {section.Name} has virtual address 0x{section.VirtualAddress:X} and file offset {fileOffset},
                  which differ by a non-multiple of {MaximumPacking}; a flat image layout would misalign the data.
                """);
    }

    /// <summary>The guaranteed alignment of validated static data: its declared packing.</summary>
    internal static int Alignment(FieldDefinition field) => field.FieldType.Resolve().PackingSize;

    internal static string LeanBytes(FieldDefinition field) => LeanBytes(field.InitialValue);

    internal static string LeanBytes(byte[] bytes) =>
        "[" + string.Join(", ", bytes.Select(b => $"(BitVec.ofNat 8 {b})")) + "]";
}
