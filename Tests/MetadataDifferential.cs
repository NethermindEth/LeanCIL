#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:package Mono.Cecil

using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Text;
using System.Text.Json;
using Mono.Cecil;

// Differential check of the Lean metadata decoder against System.Reflection.Metadata and Mono.Cecil: every row of the
// reference, type, signature and instantiation tables of an assembly and the heap entries they name are written to
// Lean, together with the full name Cecil spells for each method reference. Lean must decode the rows to the same
// names, from the bytes alone. Member references whose owner or signature mentions a generic parameter are spelled by
// the extractor's own owner rule and are covered by the extraction suites, so they are counted and skipped here.
var assembly = args.Length > 0 ? args[0] : At("Examples/Assembly/bin/Examples.dll");
var name = Path.GetFileNameWithoutExtension(assembly);
var output = At("artifacts/MetadataDifferential");
Directory.CreateDirectory(output);
using var pe = new PEReader(File.OpenRead(assembly));
var reader = pe.GetMetadataReader();
var meta = pe.GetMetadata().GetContent();
using var module = ModuleDefinition.ReadModule(assembly);

var rows = new SortedDictionary<int, byte[]>();
var strings = new SortedDictionary<int, byte[]>();
var blobs = new SortedDictionary<int, byte[]>();
string Bytes(IEnumerable<byte> values) => "[" + string.Join(", ", values) + "]";
string Entries<TKey>(SortedDictionary<TKey, byte[]> entries) where TKey : notnull =>
    "[" + string.Join(", ", entries.Select(entry => $"({entry.Key}, {Bytes(entry.Value)})")) + "]";
void Row(TableIndex table, int row)
{
    var size = reader.GetTableRowSize(table);
    var at = reader.GetTableMetadataOffset(table) + (row - 1) * size;
    rows[((int)table << 24) + row] = meta.AsSpan(at, size).ToArray();
}
void Text(StringHandle handle)
{
    var offset = reader.GetHeapOffset(handle);
    var start = reader.GetHeapMetadataOffset(HeapIndex.String) + offset;
    var end = start;
    while (meta[end] != 0) end++;
    strings[offset] = meta.AsSpan(start, end - start + 1).ToArray();
}
void Blob(BlobHandle handle)
{
    var offset = reader.GetHeapOffset(handle);
    var start = reader.GetHeapMetadataOffset(HeapIndex.Blob) + offset;
    var first = meta[start];
    var (header, length) = first < 0x80 ? (1, (int)first) : first < 0xC0 ? (2, ((first & 0x3F) << 8) | meta[start + 1]) :
        (4, ((first & 0x1F) << 24) | (meta[start + 1] << 16) | (meta[start + 2] << 8) | meta[start + 3]);
    blobs[offset] = meta.AsSpan(start, header + length).ToArray();
}

foreach (var handle in reader.TypeReferences)
{
    Row(TableIndex.TypeRef, MetadataTokens.GetRowNumber(handle));
    var reference = reader.GetTypeReference(handle);
    Text(reference.Name);
    Text(reference.Namespace);
}
foreach (var handle in reader.AssemblyReferences)
{
    Row(TableIndex.AssemblyRef, MetadataTokens.GetRowNumber(handle));
    var reference = reader.GetAssemblyReference(handle);
    Text(reference.Name);
    Text(reference.Culture);
    Blob(reference.PublicKeyOrToken);
}
foreach (var handle in reader.GetTypeSpecifications())
{
    Row(TableIndex.TypeSpec, MetadataTokens.GetRowNumber(handle));
    Blob(reader.GetTypeSpecification(handle).Signature);
}
foreach (var handle in reader.GetMethodSpecifications())
{
    Row(TableIndex.MethodSpec, MetadataTokens.GetRowNumber(handle));
    Blob(reader.GetMethodSpecification(handle).Signature);
}
var expected = new List<(int Token, string Name)>();
var skipped = 0;
foreach (var handle in reader.MemberReferences)
{
    var member = reader.GetMemberReference(handle);
    Row(TableIndex.MemberRef, MetadataTokens.GetRowNumber(handle));
    Text(member.Name);
    Blob(member.Signature);
    var token = MetadataTokens.GetToken(handle);
    if (module.LookupToken(token) is not MethodReference method) continue;
    var owner = method.DeclaringType;
    // The extractor spells owners and signatures that mention generic parameters by position; only closed ones are compared.
    if (owner.ContainsGenericParameter || method.ReturnType.ContainsGenericParameter ||
        method.Parameters.Any(parameter => parameter.ParameterType.ContainsGenericParameter) ||
        method.FullName.Contains("modreq", StringComparison.Ordinal) ||
        method.CallingConvention is MethodCallingConvention.VarArg)
    {
        skipped++;
        continue;
    }
    var scope = owner.Scope is AssemblyNameReference reference ? reference.FullName : module.Assembly.Name.FullName;
    expected.Add((token, scope + "::" + method.FullName));
}
// The tables above refer to each other through coded indices, so every table row that a row names is carried too.
var core = (module.TypeSystem.CoreLibrary as AssemblyNameReference)!;
var corlib = module.AssemblyReferences.ToList().FindIndex(reference => reference.FullName == core.FullName) + 1;
var header = DifferentialHeader(reader, meta);
var assemblyDefinition = reader.GetAssemblyDefinition();
Text(assemblyDefinition.Name);
Text(assemblyDefinition.Culture);
Blob(assemblyDefinition.PublicKey);
var assemblyRowAt = reader.GetTableMetadataOffset(TableIndex.Assembly);
var assemblyRow = meta.AsSpan(assemblyRowAt, reader.GetTableRowSize(TableIndex.Assembly)).ToArray();
var lean = $$"""
    import CIL.Extraction.MetadataBinding

    namespace Differential
    open CIL CIL.Extraction

    def slice : MetadataSlice :=
      { assembly := { identity := {{JsonSerializer.Serialize(module.Assembly.Name.FullName)}}, tableHeader := {{Bytes(header)}},
          assemblyRow := {{Bytes(assemblyRow)}}, strings := {{Entries(strings)}}, blobs := {{Entries(blobs)}} },
        rows := {{Entries(rows)}}, strings := {{Entries(strings)}}, blobs := {{Entries(blobs)}}, corlib := {{corlib}} }

    def expected : List (Nat × String) := [{{string.Join(", ", expected.Select(entry =>
        $"({(uint)entry.Token}, {JsonSerializer.Serialize(entry.Name)})"))}}]

    /-- The names Lean spells for the method references of the assembly, as Cecil's `FullName` spells them. -/
    def mismatches : List Nat :=
      match slice.index with
      | .error _ => [0]
      | .ok index =>
        let env : MetadataEnv := { slices := [index] }
        expected.filterMap fun (token, name) =>
          match env.methodSite token with
          | .ok site => if site.externalName == some (bytesOf name) then none else some token
          | .error _ => some token

    theorem names_agree : mismatches = [] := by decide +kernel
    #print axioms names_agree
    end Differential
    """;
var path = Path.Combine(output, name + ".lean");
File.WriteAllText(path, lean.ReplaceLineEndings("\n"));
Console.WriteLine($"{name}: {expected.Count} method references compared with Cecil, {skipped} open or modified ones skipped");
Run(["lake", "env", "lean", path], cwd: FixturePackage());
Console.WriteLine($"PASS Lean spells every compared method reference of {name} as Cecil does");

// The table stream header: the bytes from the reserved word through the last row count.
static byte[] DifferentialHeader(MetadataReader reader, System.Collections.Immutable.ImmutableArray<byte> meta)
{
    var tables = Enumerable.Range(0, 64).Where(table => reader.GetTableRowCount((TableIndex)table) > 0).ToArray();
    var length = 24 + 4 * tables.Length;
    var start = tables.Min(table => reader.GetTableMetadataOffset((TableIndex)table)) - length;
    return meta.AsSpan(start, length).ToArray();
}
