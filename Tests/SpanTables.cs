#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/SpanTables");
Directory.CreateDirectory(root);
var rejected = new RejectedEvidence(root);
var queue = new GeneratedQueue(verification, assembly);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.SpanTables")!;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.Safety.Execution");

string Scalar(object value) => value switch
{
    int v => $".scalar (.i32 {unchecked((uint)v)})", uint v => $".scalar (.i32 {v})", ulong v => $".scalar (.i64 {v})",
    _ => throw new InvalidOperationException("Unexpected result type")
};
string Claim(string dll, string name, int[] input, string outcome) =>
    $"(CIL.Safety.invoke Extracted.program 64 0 [{string.Join(", ", input.Select(v => Scalar(v)))}] Examples.empty).map Prod.snd = {outcome}";
void Prove(string dll, string selector, string folder, IReadOnlyList<string> claims, Action passed,
    string control = "")
{
    var proof = Path.Combine(root, folder + ".lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  and_intros <;> rfl\nend ExampleProof\n" + control);
    queue.Add(new(selector, proof, Path.Combine(root, folder), Assembly: dll), passed);
}

// Reads agree with .NET, and an out-of-range index faults at get_Item with the type .NET raises.
foreach (var (name, selector, inputs) in new (string, string, int[][])[]
{
    ("Word", "SpanTables::Word(int)", [[0], [7], [8], [-1], [int.MinValue]]),
    ("Power", "SpanTables::Power(int)", [[0], [3], [4], [-1]]),
    ("Count", "SpanTables::Count()", [[]]),
    ("First", "SpanTables::First()", [[]])
})
{
    var folder = Path.Combine(root, name);
    Run(Extract("extract", assembly, "Examples", selector, folder));
    var source = File.ReadAllText(Path.Combine(folder, "Extracted.lean"));
    var site = Regex.Match(source, @"(?m)^@\[cil_code ↓\] theorem method(\d+)_instruction(\d+) : method\d+\.code\[\d+\]\? = some \(\.memory \(\.spanItem \d\) : Op\) := rfl\r?$");
    var claims = inputs.Select(input =>
    {
        try { return Claim(assembly, name, input, $".ok [{Scalar(runtime.GetMethod(name)!.Invoke(null, [.. input.Cast<object>()])!)}]"); }
        catch (TargetInvocationException error) when (site.Success)
        {
            return Claim(assembly, name, input, $".error ⟨{site.Groups[1].Value}, {site.Groups[2].Value}, .thrown \"{error.InnerException!.GetType().FullName}\"⟩");
        }
    }).ToList();
    // The RVA descriptor carries the declared packing Roslyn aligned the table to.
    var packing = name is "Word" or "Count" ? 4 : 8;
    if (!source.Contains($"alignment := {packing} }})", StringComparison.Ordinal))
        throw new InvalidOperationException($"{name}: missing static data alignment {packing}");
    var folded = Regex.Match(source,
        @"theorem method(\d+)_instruction\d+ : [^\r\n]*some \(\.nop : Op\)");
    if (source.Contains("(.nop : Op)", StringComparison.Ordinal) && !folded.Success)
        throw new InvalidOperationException("Missing instruction theorem for a folded span receiver");
    var obligation = $"method{folded.Groups[1].Value}_features_validated";
    var control = folded.Success
        ? CheckedEvidenceControl(source, NarrowEvidence(source, obligation), [obligation], 0) : "";
    Prove(assembly, selector, name + "-Verified", claims,
        () => Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons"), control);

    // The receiver fold is bound by the feature certificate, independently of the instruction lemmas.
    if (!folded.Success) continue;
    var forged = Path.Combine(root, name + "-forged.lean");
    File.WriteAllText(forged, NarrowEvidence(source.Replace(".nop", ".localAddr 0"), obligation));
    rejected.Add(forged, $"PASS {name}: forged span receiver rejected by the feature certificate",
        diagnostic => Regex.IsMatch(diagnostic,
            @"Extraction\.FeatureFlowValid rawLayouts\.toArray method\d+Closed"), "is false");
}

// The proved value comes from the assembly's RVA blob through ldtoken.
var tampered = Path.Combine(root, "Tampered", "Examples.dll");
Directory.CreateDirectory(Path.GetDirectoryName(tampered)!);
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var getter = module.GetType("Examples.SpanTables").Methods.Single(m => m.Name == "get_Words");
    var blob = ((FieldReference)getter.Body.Instructions[0].Operand).Resolve();
    var bytes = blob.InitialValue.ToArray();
    bytes[0] = 0x63;
    blob.InitialValue = bytes;
    module.Write(tampered);
}
Prove(tampered, "SpanTables::Word(int)", "Tampered",
    [Claim(tampered, "Word", [0], ".ok [.scalar (.i32 1891)]")],
    () => Console.WriteLine("PASS tampered RVA blob changes the proved word"));
// Reused locals and computed indexes retain storage; entering an erased receiver is invalid.
foreach (var (mutation, marker) in new[]
{
    ("second-read", ""),
    ("computed-index", ""),
    ("interior-branch", "Branch into a folded span receiver")
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var body = module.GetType("Examples.SpanTables").Methods.Single(m => m.Name == "Word").Body;
        var code = body.Instructions;
        var il = body.GetILProcessor();
        if (code.Count != 7 || code[1].OpCode.Code != Code.Stloc_0 || code[2].OpCode.Code != Code.Ldloca_S || code[6].OpCode.Code != Code.Ret)
            throw new InvalidOperationException("Unexpected compiled span read");
        switch (mutation)
        {
            case "second-read":
                il.InsertBefore(code[6], il.Create(OpCodes.Ldloc_0));
                il.InsertBefore(code[7], il.Create(OpCodes.Pop));
                break;
            case "computed-index":
                il.InsertAfter(code[3], il.Create(OpCodes.Ldc_I4_0));
                il.InsertAfter(code[4], il.Create(OpCodes.Add));
                break;
            case "interior-branch":
                il.InsertBefore(code[1], il.Create(OpCodes.Br, code[2]));
                break;
        }
        module.Write(dll);
    }
    if (marker.Length == 0)
    {
        var expected = Scalar(runtime.GetMethod("Word")!.Invoke(null, [0])!);
        Prove(dll, "SpanTables::Word(int)", "Supported-" + mutation,
            [Claim(dll, "Word", [0], $".ok [{expected}]")],
            () => Console.WriteLine("PASS stored static span: " + mutation));
        continue;
    }
    var result = Execute(Extract("extract", dll, "Examples", "SpanTables::Word(int)", output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect span rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}
// CoreCLR's CreateSpan<uint> throws on data not 4-byte aligned; packing 2 promises only 2 bytes.
const string misalignedSpan = "Typed span element width does not divide the field alignment";
var narrowFolder = Path.Combine(root, "Narrow-packing");
var narrowDll = Path.Combine(narrowFolder, "Examples.dll");
Directory.CreateDirectory(narrowFolder);
string wordsField;
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var getter = module.GetType("Examples.SpanTables").Methods.Single(m => m.Name == "get_Words");
    var blob = ((FieldReference)getter.Body.Instructions[0].Operand).Resolve();
    wordsField = blob.Name;
    var layout = (TypeDefinition)blob.FieldType;
    // Cecil resolves packing and class size together; setting one first would lose the other.
    var classSize = layout.ClassSize;
    layout.PackingSize = 2;
    layout.ClassSize = classSize;
    module.Write(narrowDll);
}
Run(Extract("extract", narrowDll, "Examples", "SpanTables::Word(int)", narrowFolder));
var narrowSource = File.ReadAllText(Path.Combine(narrowFolder, "Extracted.lean"));
var createSite = Regex.Match(narrowSource,
    @"theorem method(\d+)_instruction(\d+) : [^\r\n]*some \(\.memory \(\.createSpan 4\) : Op\)");
if (!createSite.Success || !narrowSource.Contains("alignment := 2 })", StringComparison.Ordinal))
    throw new InvalidOperationException("Narrow packing did not reach the extracted CreateSpan site");
Prove(narrowDll, "SpanTables::Word(int)", "Narrow-packing-Verified",
    [Claim(narrowDll, "Word", [0], $".error ⟨{createSite.Groups[1].Value}, {createSite.Groups[2].Value}, " +
        $".unsupported \"{misalignedSpan}\"⟩")],
    () => Console.WriteLine("PASS CreateSpan over a narrower packing is unsupported, never a success"));

// An RVA off its declared packing is rejected before extraction; Cecil re-aligns, so patch the table.
var shiftedFolder = Path.Combine(root, "Reject-misaligned-rva");
var shiftedDll = Path.Combine(shiftedFolder, "Examples.dll");
Directory.CreateDirectory(shiftedFolder);
File.Delete(Path.Combine(shiftedFolder, "Extracted.lean"));
File.Copy(assembly, shiftedDll, true);
ShiftFieldRva(shiftedDll, wordsField, 2);
var shifted = Execute(Extract("extract", shiftedDll, "Examples", "SpanTables::Word(int)", shiftedFolder));
if (shifted.Code == 0 || File.Exists(Path.Combine(shiftedFolder, "Extracted.lean")) ||
    !shifted.Output.Contains("Misaligned static data", StringComparison.Ordinal) ||
    !shifted.Output.Contains("is not a multiple of its declared packing 4", StringComparison.Ordinal))
    throw new InvalidOperationException("Misaligned RVA was not rejected:\n" + shifted.Output);
Console.WriteLine("PASS rejection: static data RVA off its declared packing");

// A section whose file offset and virtual address differ by 4 keeps the RVA aligned but not a flat layout;
// Roslyn's own output, extracted above, is the positive control.
const string sectionMisaligned = "Static data section misaligned";
var offsetFolder = Path.Combine(root, "Reject-section-file-offset");
var offsetDll = Path.Combine(offsetFolder, "Examples.dll");
Directory.CreateDirectory(offsetFolder);
File.Delete(Path.Combine(offsetFolder, "Extracted.lean"));
var wordsRva = ShiftSectionRawData(assembly, offsetDll, wordsField);
using (var original = ModuleDefinition.ReadModule(assembly))
using (var moved = ModuleDefinition.ReadModule(offsetDll))
{
    byte[] Words(ModuleDefinition module) => module.GetTypes().SelectMany(type => type.Fields)
        .Single(field => field.Name == wordsField).InitialValue;
    if (!Words(original).AsSpan().SequenceEqual(Words(moved)) || wordsRva % 8 != 0)
        throw new InvalidOperationException("Shifted section no longer holds the table at an 8-aligned RVA");
}
var offset = Execute(Extract("extract", offsetDll, "Examples", "SpanTables::Word(int)", offsetFolder));
if (offset.Code == 0 || File.Exists(Path.Combine(offsetFolder, "Extracted.lean")) ||
    !offset.Output.Contains(sectionMisaligned, StringComparison.Ordinal) ||
    offset.Output.Contains("Misaligned static data", StringComparison.Ordinal))
    throw new InvalidOperationException($"""
        Section file offset off its virtual address was not rejected:
        {offset.Output}
        """);
Console.WriteLine("PASS rejection: static data section whose file offset breaks RVA alignment");

queue.Flush();
rejected.Check();
Console.WriteLine("PASS typed static spans, bounds faults, reused locals, computed indexes and forged receivers");

// Adds `delta` to the FieldRVA row of the named field in a written PE image.
static void ShiftFieldRva(string path, string fieldName, uint delta)
{
    const System.Reflection.Metadata.Ecma335.TableIndex fieldRva =
        System.Reflection.Metadata.Ecma335.TableIndex.FieldRva;
    var image = File.ReadAllBytes(path);
    using var pe = new System.Reflection.PortableExecutable.PEReader(new MemoryStream(image));
    var reader = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
    var field = reader.FieldDefinitions.Single(handle =>
        reader.GetString(reader.GetFieldDefinition(handle).Name) == fieldName);
    var fieldRow = System.Reflection.Metadata.Ecma335.MetadataTokens.GetRowNumber(field);
    var table = pe.PEHeaders.MetadataStartOffset +
        System.Reflection.Metadata.Ecma335.MetadataReaderExtensions.GetTableMetadataOffset(reader, fieldRva);
    var rowSize = System.Reflection.Metadata.Ecma335.MetadataReaderExtensions.GetTableRowSize(reader, fieldRva);
    var rowCount = System.Reflection.Metadata.Ecma335.MetadataReaderExtensions.GetTableRowCount(reader, fieldRva);
    // Each row is a 4-byte RVA followed by a 2- or 4-byte Field index.
    var entry = -1;
    for (var index = 0; index < rowCount && entry < 0; index++)
    {
        var start = table + index * rowSize;
        var owner = rowSize == 6 ? BitConverter.ToUInt16(image, start + 4) : BitConverter.ToInt32(image, start + 4);
        if (owner == fieldRow) entry = start;
    }
    if (entry < 0) throw new InvalidOperationException("Missing FieldRVA row: " + fieldName);
    var rva = System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(image.AsSpan(entry));
    System.Buffers.Binary.BinaryPrimitives.WriteUInt32LittleEndian(image.AsSpan(entry), rva + delta);
    File.WriteAllBytes(path, image);
}

// Writes a copy whose section raw data starts 4 bytes later in the file; returns the named field's RVA.
static uint ShiftSectionRawData(string source, string target, string fieldName)
{
    const int shift = 4, sectionHeaderSize = 40, sectionPointerToRawData = 20;
    const int debugEntrySize = 28, debugPointerToRawData = 24;
    var original = File.ReadAllBytes(source);
    using var pe = new System.Reflection.PortableExecutable.PEReader(new MemoryStream(original));
    var headers = pe.PEHeaders;
    var reader = System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(pe);
    var field = reader.GetFieldDefinition(reader.FieldDefinitions.Single(handle =>
        reader.GetString(reader.GetFieldDefinition(handle).Name) == fieldName));
    var rva = field.GetRelativeVirtualAddress();
    var firstRaw = headers.SectionHeaders.Min(section => section.PointerToRawData);
    if (headers.PEHeader!.SizeOfHeaders > firstRaw)
        throw new InvalidOperationException("Section raw data overlaps the PE headers");
    // Inserting before the first section moves every file offset at or past it, and no RVA.
    var image = new byte[original.Length + shift];
    original.AsSpan(0, firstRaw).CopyTo(image);
    original.AsSpan(firstRaw).CopyTo(image.AsSpan(firstRaw + shift));
    void Bump(int at)
    {
        var value = System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(image.AsSpan(at));
        System.Buffers.Binary.BinaryPrimitives.WriteUInt32LittleEndian(image.AsSpan(at), value + shift);
    }
    var table = headers.PEHeaderStartOffset + headers.CoffHeader.SizeOfOptionalHeader;
    for (var index = 0; index < headers.SectionHeaders.Length; index++)
        Bump(table + index * sectionHeaderSize + sectionPointerToRawData);
    // Cecil reads debug entry data by file offset, so those offsets move with the sections.
    var debugTable = headers.PEHeader.DebugTableDirectory;
    if (headers.TryGetDirectoryOffset(debugTable, out var debug))
        for (var index = 0; index < debugTable.Size / debugEntrySize; index++)
        {
            var entry = debug + shift + index * debugEntrySize + debugPointerToRawData;
            if (System.Buffers.Binary.BinaryPrimitives.ReadUInt32LittleEndian(image.AsSpan(entry)) >= firstRaw)
                Bump(entry);
        }
    File.WriteAllBytes(target, image);
    using var shifted = new System.Reflection.PortableExecutable.PEReader(new MemoryStream(image));
    var section = shifted.PEHeaders.SectionHeaders[shifted.PEHeaders.GetContainingSectionIndex(rva)];
    if (shifted.PEHeaders.SectionHeaders.Any(other => other.PointerToRawData < firstRaw + shift) ||
        (section.VirtualAddress - section.PointerToRawData) % 8 != 8 - shift)
        throw new InvalidOperationException("Shifted section still agrees with its virtual address modulo 8");
    return (uint)rva;
}
