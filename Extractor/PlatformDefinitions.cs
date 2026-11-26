using System.Collections.Immutable;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Text;
using Mono.Cecil;
using ModuleDefinition = Mono.Cecil.ModuleDefinition;
using TypeDefinition = Mono.Cecil.TypeDefinition;
using TypeReference = Mono.Cecil.TypeReference;

namespace Nethermind.LeanCIL;

/// <summary>What Lean's metadata checks rely on about a platform type: <c>CIL.Extraction.PlatformKind</c>.</summary>
internal enum PlatformKind
{
    ClassType,
    InterfaceType,
    ValueType,
    EnumType,
    ObjectRoot,
    ValueTypeRoot,
    EnumRoot,
    ValuePair,
    ByteOrder,
}

/// <summary>
/// One platform type as Lean reads its reference: the typed assembly the reference scopes it to, the namespace and
/// name of each enclosing type and of the type, outermost first, and its kind, with the element type code of an enum.
/// </summary>
internal sealed record PlatformDefinition<TAssembly>(
    TAssembly Assembly, ImmutableArray<string> Parts, PlatformKind Kind, int Underlying, int Arity)
{
    /// <summary>The Lean <c>CIL.Extraction.PlatformDefinition</c>, with the assembly written by
    /// <paramref name="assembly"/> and byte lists by <paramref name="bytes"/>.</summary>
    internal string Lean(Func<TAssembly, string> assembly, Func<IEnumerable<byte>, string> bytes)
    {
        var parts = string.Join(", ", Parts.Select(part => bytes(Encoding.UTF8.GetBytes(part))));
        return $$"""{ assembly := {{assembly(Assembly)}}, parts := [{{parts}}], kind := {{LeanKind}} }""";
    }

    string LeanKind => Kind switch
    {
        PlatformKind.ClassType when Arity != 0 => $".genericClass {Arity}",
        PlatformKind.InterfaceType when Arity != 0 => $".genericInterface {Arity}",
        PlatformKind.ValueType when Arity != 0 => $".genericValue {Arity}",
        PlatformKind.ClassType => ".classType",
        PlatformKind.InterfaceType => ".interfaceType",
        PlatformKind.ValueType => ".valueType",
        PlatformKind.EnumType when Arity != 0 => $".enumType {Underlying} {Arity}",
        PlatformKind.EnumType => $".enumType {Underlying}",
        PlatformKind.ObjectRoot => ".objectRoot",
        PlatformKind.ValueTypeRoot => ".valueTypeRoot",
        PlatformKind.EnumRoot => ".enumRoot",
        PlatformKind.ValuePair => ".valuePair",
        PlatformKind.ByteOrder => ".byteOrder",
        _ => throw new ArgumentOutOfRangeException(nameof(Kind), Kind, null),
    };
}

/// <summary>What every platform table shares: its recursion depth and how a type's name parts are read.</summary>
internal static class PlatformDefinitions
{
    // Compiling the table literal recurses about 16 levels per definition: 1,024 need more than 12,288.
    const int RecursionDepthPerDefinition = 32;
    const int MinimumRecursionDepth = 4096;

    /// <summary>The <c>maxRecDepth</c> under which Lean compiles a table of <paramref name="count"/>
    /// definitions.</summary>
    internal static int RecursionDepth(int count) =>
        Math.Max(MinimumRecursionDepth, RecursionDepthPerDefinition * count);

    /// <summary>The namespace and simple name of every enclosing type, outermost first.</summary>
    internal static IEnumerable<string> NameParts(TypeReference type)
    {
        var parts = new Stack<string>();
        for (var level = type; level is not null; level = level.DeclaringType)
        {
            parts.Push(level.Name);
            parts.Push(level.Namespace);
        }
        return parts;
    }

    // The element type code of an enum's instance field, as Lean reads it from the field's signature.
    internal static int Underlying(TypeDefinition type) =>
        (int)type.Fields.First(field => !field.IsStatic).FieldType.MetadataType;
}

/// <summary>
/// The platform definitions an extraction states: one for each platform type a carried <c>TypeRef</c> row or a
/// stated type argument names, the only places Lean's checks read a platform type's scope and name parts from.
/// Lean refuses a type outside the carried slices whose definition is missing or of another kind, so a type left
/// out is a refusal, never an acceptance. The roots, the value pair and the byte-order class are those of
/// <paramref name="coreLibrary"/>, the module that defines the run's <c>System.Object</c>. <paramref name="assembly"/>
/// reads the typed assembly of a reference row of a module, equal for equal columns.
/// </summary>
internal sealed class PlatformDefinitions<TAssembly>(
    ModuleDefinition coreLibrary, Func<AssemblyNameReference, ModuleDefinition, TAssembly> assembly)
    where TAssembly : notnull
{
    // Keyed by the typed assembly and the parts, as Lean compares them, so a type named by several modules is stated
    // once.
    readonly Dictionary<(TAssembly Assembly, string Parts), PlatformDefinition<TAssembly>> definitions = [];

    /// <summary>The <c>maxRecDepth</c> under which Lean compiles these definitions.</summary>
    internal int Depth => PlatformDefinitions.RecursionDepth(definitions.Count);

    /// <summary>Adds the definition of each type the <paramref name="references"/> of <paramref name="module"/> name
    /// in an assembly that <paramref name="platform"/> holds a platform assembly. A type of another assembly, or one
    /// Cecil cannot resolve, gets none, so a check that relies on it refuses.</summary>
    internal void Add(ModuleDefinition module, MetadataReader reader, IEnumerable<TypeReferenceHandle> references,
        Func<AssemblyNameReference, bool> platform)
    {
        foreach (var handle in references)
            if (Definition(module, reader, handle, platform) is { } definition)
                Add(definition);
    }

    /// <summary>Adds the definition of <paramref name="type"/> when it is a type of a platform assembly, named as a
    /// stated type argument names it.</summary>
    internal void Add(TypeReference type, Func<AssemblyNameReference, bool> platform)
    {
        if (type.Scope is not AssemblyNameReference reference || !platform(reference)) return;
        var parts = PlatformDefinitions.NameParts(type);
        if (type.Resolve() is not { } definition) return;
        var kind = Kind(definition);
        Add(new(assembly(reference, type.Module), [.. parts], kind,
            kind == PlatformKind.EnumType ? PlatformDefinitions.Underlying(definition) : 0,
            definition.GenericParameters.Count));
    }

    void Add(PlatformDefinition<TAssembly> definition) =>
        definitions.TryAdd((definition.Assembly, string.Join('\0', definition.Parts)), definition);

    /// <summary>The Lean list of the definitions, ordered by their text, with assemblies written by
    /// <paramref name="writeAssembly"/> and byte lists by <paramref name="bytes"/>.</summary>
    internal string Lean(Func<TAssembly, string> writeAssembly, Func<IEnumerable<byte>, string> bytes) =>
        $"""[{string.Join(",\n  ", definitions.Values.Select(definition => definition.Lean(writeAssembly, bytes))
            .Order(StringComparer.Ordinal))}]""";

    PlatformDefinition<TAssembly>? Definition(ModuleDefinition module, MetadataReader reader,
        TypeReferenceHandle handle, Func<AssemblyNameReference, bool> platform)
    {
        var parts = new Stack<string>();
        EntityHandle scope = handle;
        while (scope.Kind == HandleKind.TypeReference)
        {
            var row = reader.GetTypeReference((TypeReferenceHandle)scope);
            parts.Push(reader.GetString(row.Name));
            parts.Push(reader.GetString(row.Namespace));
            scope = row.ResolutionScope;
        }
        if (scope.Kind != HandleKind.AssemblyReference) return null;
        var reference = module.AssemblyReferences[MetadataTokens.GetRowNumber(scope) - 1];
        if (!platform(reference)) return null;
        var named = (TypeReference)module.LookupToken(MetadataTokens.GetToken(handle));
        if (named.Resolve() is not { } type) return null;
        var kind = Kind(type);
        return new(assembly(reference, module), [.. parts], kind,
            kind == PlatformKind.EnumType ? PlatformDefinitions.Underlying(type) : 0, type.GenericParameters.Count);
    }

    // The roots, the value pair and the byte-order class by their core-library definitions, any other type by what
    // it is; the same names defined elsewhere are ordinary types.
    PlatformKind Kind(TypeDefinition type) => (type.Module.Mvid == coreLibrary.Mvid ? type.FullName : null) switch
    {
        _ when type.IsInterface => PlatformKind.InterfaceType,
        "System.Object" when !type.HasGenericParameters => PlatformKind.ObjectRoot,
        "System.ValueType" when !type.HasGenericParameters => PlatformKind.ValueTypeRoot,
        "System.Enum" when !type.HasGenericParameters => PlatformKind.EnumRoot,
        "System.ValueTuple`2" when type.GenericParameters.Count == 2 => PlatformKind.ValuePair,
        "System.BitConverter" when !type.HasGenericParameters => PlatformKind.ByteOrder,
        _ when type.IsEnum => PlatformKind.EnumType,
        _ when type.IsValueType => PlatformKind.ValueType,
        _ => PlatformKind.ClassType,
    };
}
