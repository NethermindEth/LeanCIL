#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using Mono.Cecil;
using AssemblyDefinition = Mono.Cecil.AssemblyDefinition;
using CustomAttribute = Mono.Cecil.CustomAttribute;
using FieldAttributes = Mono.Cecil.FieldAttributes;
using MethodDefinition = Mono.Cecil.MethodDefinition;
using MethodAttributes = Mono.Cecil.MethodAttributes;
using ModuleDefinition = Mono.Cecil.ModuleDefinition;
using TypeDefinition = Mono.Cecil.TypeDefinition;
using TypeReference = Mono.Cecil.TypeReference;
using TypeAttributes = Mono.Cecil.TypeAttributes;

var extractor = Assembly.LoadFrom(ExtractorPath);
const BindingFlags Internal = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
var pinnedType = extractor.GetType("Nethermind.LeanCIL.PinnedAssemblies", throwOnError: true)!;
var sourceType = pinnedType.GetNestedType("Source", BindingFlags.Public | BindingFlags.NonPublic)!;
var collectionType = extractor.GetType("Nethermind.LeanCIL.MetadataSlices+Collection", throwOnError: true)!;
var sources = Array.CreateInstance(sourceType, 0);
var proofs = new System.Text.StringBuilder("import CIL.Extraction.MetadataBytes\nopen CIL.Extraction\n");
var proofCount = 0;

foreach (var wide in new[] { false, true })
    Check(Image(4, wide), wide ? 4 : 2);
Check(SmallWideImage(), 4);

var slicesType = extractor.GetType("Nethermind.LeanCIL.MetadataSlices", throwOnError: true)!;
var requireRank = slicesType.GetMethod("RequireHeapRank", BindingFlags.Static | BindingFlags.NonPublic)!;
foreach (var width in new[] { 2, 4 })
{
    var marker = width == 2 ? ushort.MaxValue : uint.MaxValue;
    foreach (var heap in new[] { "#Strings", "#Blob" })
    {
        requireRank.Invoke(null, [marker - 1, width, heap]);
        try
        {
            requireRank.Invoke(null, [marker, width, heap]);
            throw new InvalidOperationException("A reserved rank was accepted.");
        }
        catch (TargetInvocationException error) when (error.InnerException is InvalidDataException) { }
    }
}
Console.WriteLine("PASS rank boundaries for both heaps and widths");

double previous = 0;
foreach (var count in new[] { 256, 1024, 4096 })
{
    var image = Image(count, false);
    var timings = Enumerable.Range(0, 7).Select(_ => Check(image, 2, false)).Order().ToArray();
    var elapsed = timings[0];
    Require(previous == 0 || elapsed <= previous * 8 + 2,
        "Position-only row canonicalization grows faster than its row count allows.");
    Console.WriteLine($"Canonicalized {count} position-only field rows in {elapsed:F3} ms minimum");
    previous = elapsed;
}

var lean = At("artifacts/MetadataHeapOmissions.lean");
File.WriteAllText(lean, proofs.ToString());
Run(["lake", "build", "CIL.Extraction.MetadataBytes"]);
Console.WriteLine(Run(["lake", "env", "lean", lean]));

byte[] SmallWideImage()
{
    var bytes = Image(4, true);
    using var pe = new PEReader(new MemoryStream(bytes));
    var reader = pe.GetMetadataReader();
    var metadata = pe.PEHeaders.MetadataStartOffset;
    var paddingType = reader.TypeDefinitions.Last();
    var paddingName = reader.GetHeapOffset(reader.GetTypeDefinition(paddingType).Name);
    var attribute = reader.CustomAttributes.Single();
    var paddingBlob = reader.GetHeapOffset(reader.GetCustomAttribute(attribute).Value);
    Require(paddingName < ushort.MaxValue && paddingBlob < ushort.MaxValue,
        "Padding must follow all meaningful heap entries.");
    var typeRow = metadata + reader.GetTableMetadataOffset(TableIndex.TypeDef) +
        (MetadataTokens.GetRowNumber(paddingType) - 1) * reader.GetTableRowSize(TableIndex.TypeDef);
    bytes.AsSpan(typeRow + 4, 4).Clear();
    var attributeRow = metadata + reader.GetTableMetadataOffset(TableIndex.CustomAttribute);
    bytes.AsSpan(attributeRow + reader.GetTableRowSize(TableIndex.CustomAttribute) - 4, 4).Clear();
    var versionLength = BitConverter.ToInt32(bytes, metadata + 12);
    var at = metadata + 16 + versionLength;
    var streams = BitConverter.ToUInt16(bytes, at + 2);
    at += 4;
    for (var index = 0; index < streams; index++)
    {
        var end = Array.IndexOf(bytes, (byte)0, at + 8);
        var name = System.Text.Encoding.ASCII.GetString(bytes, at + 8, end - at - 8);
        var length = name switch { "#Strings" => paddingName, "#Blob" => paddingBlob, _ => -1 };
        if (length >= 0) BitConverter.GetBytes(length).CopyTo(bytes, at + 4);
        at = (end + 4) & ~3;
    }
    using var narrowed = new PEReader(new MemoryStream(bytes));
    var small = narrowed.GetMetadataReader();
    Require(small.GetHeapSize(HeapIndex.String) < ushort.MaxValue &&
        small.GetHeapSize(HeapIndex.Blob) < ushort.MaxValue, "Both declared heaps must be small.");
    Require(small.GetTableRowSize(TableIndex.Field) == 10, "Small heap indexes must remain four bytes.");
    foreach (var field in small.FieldDefinitions)
    {
        Require(small.GetString(small.GetFieldDefinition(field).Name) ==
            reader.GetString(reader.GetFieldDefinition(field).Name), "Shrinking changed a field name.");
        Require(small.GetBlobBytes(small.GetFieldDefinition(field).Signature).SequenceEqual(
            reader.GetBlobBytes(reader.GetFieldDefinition(field).Signature)), "Shrinking changed a signature.");
    }
    Console.WriteLine("PASS SRM small heaps retain wide rows and exact field names/signatures");
    return bytes;
}

byte[] Image(int count, bool wide)
{
    using var assembly = AssemblyDefinition.CreateAssembly(new("OmittedHeaps", new(1, 0)),
        "OmittedHeaps", ModuleKind.Dll);
    var module = assembly.MainModule;
    ((AssemblyNameReference)module.TypeSystem.CoreLibrary).PublicKeyToken = [];
    var owner = new TypeDefinition("", "Fields", TypeAttributes.Public | TypeAttributes.Sealed,
        new TypeReference("System", "ValueType", module, module.TypeSystem.CoreLibrary));
    module.Types.Add(owner);
    for (var index = 0; index < count; index++)
        owner.Fields.Add(new("Field" + index, FieldAttributes.Public,
            index == count - 1 ? module.TypeSystem.Int32 : module.TypeSystem.Int64));
    var method = new MethodDefinition("Run", MethodAttributes.Public | MethodAttributes.Static,
        module.TypeSystem.Void);
    method.Body.Instructions.Add(Mono.Cecil.Cil.Instruction.Create(Mono.Cecil.Cil.OpCodes.Ret));
    owner.Methods.Add(method);
    if (wide)
    {
        module.Types.Add(new("", new string('z', 70000), TypeAttributes.Public, module.TypeSystem.Object));
        var attribute = new TypeReference("Fixture", "PaddingAttribute", module, module.TypeSystem.CoreLibrary);
        var constructor = new MethodReference(".ctor", module.TypeSystem.Void, attribute) { HasThis = true };
        constructor.Parameters.Add(new(module.TypeSystem.String));
        var padding = new CustomAttribute(constructor);
        padding.ConstructorArguments.Add(new(module.TypeSystem.String, new string('z', 70000)));
        assembly.CustomAttributes.Add(padding);
    }
    using var stream = new MemoryStream();
    assembly.Write(stream);
    return stream.ToArray();
}

double Check(byte[] bytes, int width, bool proof = true)
{
    using var pinned = (IDisposable)Activator.CreateInstance(pinnedType, Internal, null,
        [bytes, "fixture", sources, null], null)!;
    var selected = (ModuleDefinition)pinnedType.GetProperty("Selected", Internal)!.GetValue(pinned)!;
    var original = (ModuleDefinition)pinnedType.GetMethod("Original", Internal)!.Invoke(pinned, [selected])!;
    var owner = original.GetType("Fields");
    var collection = Activator.CreateInstance(collectionType, Internal, null,
        [pinned, new HashSet<(ModuleDefinition, uint)>()], null)!;
    var slice = collectionType.GetMethod("SliceOf", Internal)!.Invoke(collection, [original])!;
    var sliceType = slice.GetType();
    sliceType.GetMethod("Method", Internal)!.Invoke(slice, [owner.Methods.Single(), false]);
    sliceType.GetMethod("Token", Internal)!.Invoke(slice, [owner.Fields.Last().MetadataToken.ToUInt32(), false]);
    sliceType.GetMethod("Finish", Internal)!.Invoke(slice, null);
    var rows = (SortedDictionary<uint, byte[]>)sliceType.GetField("rows", Internal)!.GetValue(slice)!;
    var strings = (SortedDictionary<int, byte[]>)sliceType.GetField("strings", Internal)!.GetValue(slice)!;
    var blobs = (SortedDictionary<int, byte[]>)sliceType.GetField("blobs", Internal)!.GetValue(slice)!;
    var row = rows[owner.Fields[0].MetadataToken.ToUInt32()];
    uint Read(int at) => width == 2 ? BitConverter.ToUInt16(row, at) : BitConverter.ToUInt32(row, at);
    var name = Read(2);
    var signature = Read(2 + width);
    Require(name != 0 && !strings.ContainsKey((int)name), "Position-only name was carried.");
    Require(signature != 0 && !blobs.ContainsKey((int)signature), "Position-only signature was carried.");
    Require(strings[0].SequenceEqual(new byte[] { 0 }) && blobs[0].SequenceEqual(new byte[] { 0 }),
        "The fixture must carry both legitimate empty entries.");
    var flags = BitConverter.ToUInt16(row);
    var ownerRow = rows[owner.MetadataToken.ToUInt32()];
    var namespaceOffset = 4 + width;
    Require(ownerRow.AsSpan(namespaceOffset, width).IndexOfAnyExcept((byte)0) < 0,
        "The fixture must use the legitimate empty namespace.");
    var watch = System.Diagnostics.Stopwatch.StartNew();
    sliceType.GetMethod("Canonicalize", Internal)!.Invoke(slice, null);
    watch.Stop();
    var marker = width == 2 ? ushort.MaxValue : uint.MaxValue;
    Require(Read(2) == marker && Read(2 + width) == marker,
        $"Omitted heap columns must use {marker}, observed {Read(2)} and {Read(2 + width)}.");
    Require(BitConverter.ToUInt16(row) == flags, "Position-only field flags changed.");
    Require(ownerRow.AsSpan(namespaceOffset, width).IndexOfAnyExcept((byte)0) < 0,
        "The legitimate empty namespace offset changed.");
    Require(!strings.ContainsKey(unchecked((int)marker)) && !blobs.ContainsKey(unchecked((int)marker)),
        "An omitted heap marker was emitted as an entry.");
    foreach (var field in owner.Fields.Take(owner.Fields.Count - 1))
    {
        var prefixRow = rows[field.MetadataToken.ToUInt32()];
        var prefixName = width == 2 ? BitConverter.ToUInt16(prefixRow, 2) : BitConverter.ToUInt32(prefixRow, 2);
        var prefixSignature = width == 2 ? BitConverter.ToUInt16(prefixRow, 2 + width)
            : BitConverter.ToUInt32(prefixRow, 2 + width);
        Require(prefixName == marker && prefixSignature == marker, "A position-only field became readable.");
    }
    if (proof)
    {
        var metadataType = extractor.GetType("Nethermind.LeanCIL.MetadataSlices", throwOnError: true)!;
        var metadata = Activator.CreateInstance(metadataType, pinned)!;
        var assemblyBlock = (string)metadataType.GetMethod("AssemblyBlock", Internal)!.Invoke(metadata, [original])!;
        Require(assemblyBlock.Contains("assemblyRow :=", StringComparison.Ordinal), "Assembly row was not emitted.");
        foreach (var (heap, read, offset, heapNumber) in new[]
                 { (strings, "stringBytes", Read(2), 0), (blobs, "blobBytes", Read(2 + width), 1) })
        {
            var entries = string.Join(", ", heap.Select(entry =>
                $"({entry.Key}, [{string.Join(", ", entry.Value)}])"));
            var namePrefix = "heap" + proofCount++;
            proofs.AppendLine($"/-- Carried heap entries from a position-only field fixture. -/");
            proofs.AppendLine($"def {namePrefix} : SearchTree (List Nat) := SearchTree.ofSorted [{entries}]");
            proofs.AppendLine($"/-- An omitted field column cannot read the carried empty entry. -/");
            proofs.AppendLine($"theorem {namePrefix}_missing : {read} {namePrefix} {offset} =");
            proofs.AppendLine($"    .error (.missingHeap {heapNumber} {offset}) := by rfl");
            proofs.AppendLine($"#print axioms {namePrefix}_missing");
            proofs.AppendLine($"/-- A genuine zero column still reads the empty entry. -/");
            proofs.AppendLine($"theorem {namePrefix}_empty : {read} {namePrefix} 0 = .ok [] := by rfl");
            proofs.AppendLine($"#print axioms {namePrefix}_empty");
        }
        Console.WriteLine($"PASS {width}-byte omitted name and signature with carried empty entries");
    }
    return watch.Elapsed.TotalMilliseconds;
}

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}
