#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../Extractor/MetadataFieldPrefix.cs
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;
using Nethermind.LeanCIL;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using TypeAttributes = Mono.Cecil.TypeAttributes;

foreach (var count in new[] { 64, 512, 4096 })
{
    uint[] fields = [.. Enumerable.Range(0, count).Select(index => 0x04000001u + (uint)index * 3)];
    foreach (var order in new[] { fields, fields.Reverse().ToArray(),
                 fields.OrderBy(token => token % 17).ToArray() })
    {
        var visited = 0;
        var disposed = false;
        IEnumerable<uint> Enumerate()
        {
            try
            {
                foreach (var field in fields)
                {
                    visited++;
                    yield return field;
                }
            }
            finally { disposed = true; }
        }
        var prefix = new MetadataFieldPrefix(Enumerate());
        var carried = new List<uint>();
        var length = 0;
        foreach (var token in order.Concat(order))
        {
            prefix.Through(token, carried.Add);
            length = Math.Max(length, (int)((token - fields[0]) / 3) + 1);
            Require(visited == length && carried.Count == length, "A field prefix was traversed again.");
        }
        prefix.All(carried.Add);
        prefix.All(carried.Add);
        Require(disposed && visited == count && carried.SequenceEqual(fields), "Full field coverage differs.");
        try
        {
            prefix.Through(0x04000002, carried.Add);
            throw new InvalidOperationException("An absent field was accepted.");
        }
        catch (InvalidDataException) { }
    }
    Console.WriteLine($"PASS {count} fields: ascending, descending and shuffled requests visit each field once");
}

// The collector is internal; calling it directly isolates metadata evidence from admission and Lean builds.
var extractor = Assembly.LoadFrom(ExtractorPath);
const BindingFlags Internal = BindingFlags.Instance | BindingFlags.NonPublic | BindingFlags.Public;
var pinnedType = extractor.GetType("Nethermind.LeanCIL.PinnedAssemblies", throwOnError: true)!;
var sourceType = pinnedType.GetNestedType("Source", BindingFlags.NonPublic | BindingFlags.Public)!;
var sources = Array.CreateInstance(sourceType, 0);
using var assembly = AssemblyDefinition.CreateAssembly(new AssemblyNameDefinition("FieldPrefixes", new(1, 0)),
    "FieldPrefixes", ModuleKind.Dll);
var module = assembly.MainModule;
var valueType = new TypeReference("System", "ValueType", module, module.TypeSystem.CoreLibrary);
var owner = new TypeDefinition("Fixture", "Cells", TypeAttributes.Public | TypeAttributes.Sealed, valueType);
module.Types.Add(owner);
foreach (var index in Enumerable.Range(0, 4))
    owner.Fields.Add(new("Field" + index, FieldAttributes.Public |
        (index == 1 ? FieldAttributes.Static : 0), index == 3 ? module.TypeSystem.Int64 : module.TypeSystem.Int32));
var entry = new TypeDefinition("Fixture", "Entry", TypeAttributes.Public, module.TypeSystem.Object);
module.Types.Add(entry);
var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Void);
method.Body.Instructions.Add(Mono.Cecil.Cil.Instruction.Create(Mono.Cecil.Cil.OpCodes.Ret));
entry.Methods.Add(method);
var baseType = new TypeDefinition("Fixture", "Base", TypeAttributes.Public, module.TypeSystem.Object);
baseType.Fields.Add(new("BaseField", FieldAttributes.Public, module.TypeSystem.Int32));
module.Types.Add(baseType);
var derived = new TypeDefinition("Fixture", "Derived", TypeAttributes.Public, baseType);
derived.Fields.Add(new("First", FieldAttributes.Public, module.TypeSystem.Int32));
derived.Fields.Add(new("Last", FieldAttributes.Public, module.TypeSystem.Int64));
module.Types.Add(derived);
var enumType = new TypeDefinition("Fixture", "Choice", TypeAttributes.Public | TypeAttributes.Sealed,
    new TypeReference("System", "Enum", module, module.TypeSystem.CoreLibrary));
enumType.Fields.Add(new("value__", FieldAttributes.Public | FieldAttributes.SpecialName |
    FieldAttributes.RTSpecialName, module.TypeSystem.Int32));
enumType.Fields.Add(new("Item", FieldAttributes.Public | FieldAttributes.Static | FieldAttributes.Literal,
    enumType) { Constant = 0 });
module.Types.Add(enumType);
using var stream = new MemoryStream();
assembly.Write(stream);
using var pinned = (IDisposable)Activator.CreateInstance(pinnedType, Internal, null,
    [stream.ToArray(), "fixture", sources, null], null)!;
var selected = (ModuleDefinition)pinnedType.GetProperty("Selected", Internal)!.GetValue(pinned)!;
var original = (ModuleDefinition)pinnedType.GetMethod("Original", Internal)!.Invoke(pinned, [selected])!;
var run = original.GetType("Fixture.Entry").Methods.Single();
var cells = original.GetType("Fixture.Cells").Fields.Select(field => field.MetadataToken.ToUInt32()).ToArray();
var baseField = original.GetType("Fixture.Base").Fields.Single().MetadataToken.ToUInt32();
var derivedFields = original.GetType("Fixture.Derived").Fields
    .Select(field => field.MetadataToken.ToUInt32()).ToArray();
var choice = original.GetType("Fixture.Choice");
var sliceType = extractor.GetType("Nethermind.LeanCIL.MetadataSlices", throwOnError: true)!;
var collector = Activator.CreateInstance(sliceType, pinned)!;
var collect = sliceType.GetMethod("Method", Internal)!;
(string Metadata, string Tables, int[] Assemblies) Collect(params uint[] tokens) =>
    ((string, string, int[]))collect.Invoke(collector, [run, tokens, false])!;

uint[] FieldRows(string metadata)
{
    var start = metadata.IndexOf("rows := [", StringComparison.Ordinal) + "rows := [".Length;
    var stop = metadata.IndexOf("], strings :=", start, StringComparison.Ordinal);
    return [.. FieldRowPattern().Matches(metadata[start..stop])
        .Select(match => uint.Parse(match.Groups[1].Value, System.Globalization.CultureInfo.InvariantCulture))
        .Where(token => token >> 24 == 4)];
}

var partial = Collect(cells[2]);
Require(FieldRows(partial.Metadata).SequenceEqual(cells[..3]), "Partial field evidence includes the wrong rows.");
static string Bytes(IEnumerable<byte> values) => "[" + string.Join(", ", values) + "]";
static bool HasName(string metadata, string name) =>
    metadata.Contains(Bytes([.. System.Text.Encoding.UTF8.GetBytes(name), 0]), StringComparison.Ordinal);
Require(HasName(partial.Metadata, "Field2") && !HasName(partial.Metadata, "Field0") &&
    !HasName(partial.Metadata, "Field1") && !HasName(partial.Metadata, "Field3"),
    "Prefix-only field rows must not carry unrequested names.");
Require(partial.Metadata.Contains("[2, 6, 8]", StringComparison.Ordinal) &&
    !partial.Metadata.Contains("[2, 6, 10]", StringComparison.Ordinal),
    "Prefix-only field rows must not carry unrequested signatures.");
var repeated = Collect(cells[2], cells[0], cells[2]);
Require(FieldRows(repeated.Metadata).SequenceEqual(cells[..3]), "Repeated fields extend the carried prefix.");
var forward = Collect(cells);
var reverse = Collect(cells.Reverse().ToArray());
Require(forward.Metadata == reverse.Metadata && forward.Tables == reverse.Tables,
    "Field order changes emitted rows, signatures, names or links.");
var inherited = Collect(derivedFields[0]);
Require(FieldRows(inherited.Metadata).SequenceEqual(new[] { baseField, derivedFields[0] }),
    "A derived field must carry all base fields and only its own prefix.");
Require(!HasName(inherited.Metadata, "BaseField") && !HasName(inherited.Metadata, "Last"),
    "Inherited row coverage must not carry unrequested names.");
var inheritedAll = Collect([.. derivedFields, baseField]);
var inheritedReverse = Collect([baseField, .. derivedFields.Reverse()]);
Require(inheritedAll.Metadata == inheritedReverse.Metadata && inheritedAll.Tables == inheritedReverse.Tables,
    "Repeated ancestors change emitted evidence.");
var enumEvidence = Collect(choice.MetadataToken.ToUInt32());
Require(FieldRows(enumEvidence.Metadata).SequenceEqual(choice.Fields.Select(field => field.MetadataToken.ToUInt32())),
    "Enum evidence omits field rows.");
Require(enumEvidence.Metadata.Contains("[2, 6, 8]", StringComparison.Ordinal) &&
    enumEvidence.Metadata.Contains(Bytes([3, 6, 17, (byte)(choice.MetadataToken.RID << 2)]),
        StringComparison.Ordinal) && !HasName(enumEvidence.Metadata, "value__") &&
    !HasName(enumEvidence.Metadata, "Item"),
    "Enum field coverage must carry signatures without unrequested names.");
Console.WriteLine("PASS partial prefixes, repeated fields, inheritance, enums and order-independent evidence");
var evidence = string.Join("\n", new[] { partial, repeated, forward, reverse, inherited,
    inheritedAll, inheritedReverse, enumEvidence }.Select(item => item.Metadata + "\n" + item.Tables));
Console.WriteLine("Evidence SHA256 " + Convert.ToHexString(System.Security.Cryptography.SHA256.HashData(
    System.Text.Encoding.UTF8.GetBytes(evidence))));

foreach (var count in new[] { 256, 1024, 4096 })
{
    using var input = AssemblyDefinition.CreateAssembly(new("FieldCount", new(1, 0)), "FieldCount", ModuleKind.Dll);
    var inputModule = input.MainModule;
    var inputType = new TypeDefinition("Fixture", "Fields", TypeAttributes.Public,
        new TypeReference("System", "ValueType", inputModule, inputModule.TypeSystem.CoreLibrary));
    inputModule.Types.Add(inputType);
    for (var index = 0; index < count; index++)
        inputType.Fields.Add(new("Field" + index, FieldAttributes.Public, inputModule.TypeSystem.Int32));
    var inputMethod = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
        inputModule.TypeSystem.Void);
    inputMethod.Body.Instructions.Add(Mono.Cecil.Cil.Instruction.Create(Mono.Cecil.Cil.OpCodes.Ret));
    inputType.Methods.Add(inputMethod);
    using var image = new MemoryStream();
    input.Write(image);
    using var inputPinned = (IDisposable)Activator.CreateInstance(pinnedType, Internal, null,
        [image.ToArray(), "fixture", sources, null], null)!;
    var inputSelected = (ModuleDefinition)pinnedType.GetProperty("Selected", Internal)!.GetValue(inputPinned)!;
    var inputOriginal = (ModuleDefinition)pinnedType.GetMethod("Original", Internal)!.Invoke(inputPinned,
        [inputSelected])!;
    var fieldsType = inputOriginal.GetType("Fixture.Fields");
    var inputCollector = Activator.CreateInstance(sliceType, inputPinned)!;
    uint[] tokens = [.. fieldsType.Fields.Select(field => field.MetadataToken.ToUInt32())];
    var watch = System.Diagnostics.Stopwatch.StartNew();
    var result = ((string Metadata, string Tables, int[] Assemblies))collect.Invoke(inputCollector,
        [fieldsType.Methods.Single(), tokens, false])!;
    watch.Stop();
    Require(FieldRows(result.Metadata).SequenceEqual(tokens), "Field collection lost a row.");
    Console.WriteLine($"Collected {count} fields in {watch.Elapsed.TotalMilliseconds:F1} ms");
}

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

partial class Program
{
    [System.Text.RegularExpressions.GeneratedRegex(@"\((\d+), \[")]
    private static partial System.Text.RegularExpressions.Regex FieldRowPattern();
}
