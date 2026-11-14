#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AssemblyName=LeanCIL.IdentityTests
#:project ../Extractor/Extractor.csproj
#:package Mono.Cecil

extern alias IdentityExtractor;

using System.Buffers.Binary;
using System.Diagnostics;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using Mono.Cecil;
using Mono.Cecil.Cil;
using IdentityExtractor::Nethermind.LeanCIL;

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

static byte[] Image(int padding)
{
    using var module = ModuleDefinition.CreateModule("ExactRows", ModuleKind.Dll);
    var type = new TypeDefinition("Fixture", "Methods", TypeAttributes.Public, module.TypeSystem.Object);
    module.Types.Add(type);
    foreach (string name in new[] { "First", "Later" })
    {
        var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static,
            module.TypeSystem.Void);
        type.Methods.Add(method);
        if (name == "First")
            for (int index = 0; index < padding; index++) method.Body.Instructions.Add(Instruction.Create(OpCodes.Nop));
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    }
    using var output = new MemoryStream();
    module.Write(output);
    return output.ToArray();
}

static (int Offset, int Size) TableStream(byte[] metadata)
{
    int at = 20 + BitConverter.ToInt32(metadata, 12);
    int streams = BitConverter.ToUInt16(metadata, at - 2);
    for (int stream = 0; stream < streams; stream++)
    {
        int offset = BitConverter.ToInt32(metadata, at);
        int size = BitConverter.ToInt32(metadata, at + 4);
        int nameEnd = Array.IndexOf(metadata, (byte)0, at + 8);
        if (metadata[at + 8] == '#' && metadata[at + 9] == '~') return (offset, size);
        at = (nameEnd + 4) & ~3;
    }
    throw new InvalidOperationException("Fixture has no table stream");
}

byte[] original = Image(0);
using var pe = new PEReader(new MemoryStream(original));
var metadata = new MetadataImage(pe);
byte[] root = pe.GetMetadata().GetContent().ToArray();
var (tableOffset, tableSize) = TableStream(root);
byte[] header = metadata.TableHeader();
Require(root.AsSpan(tableOffset, header.Length).SequenceEqual(header), "Header differs from original bytes");
// A carried MethodDef row has its RVA column zeroed: an earlier body's length moves the image's own RVA of a
// later method, and that method's evidence must not change with it.
byte[] later = metadata.Row(0x06000002);
int rowOffset = metadata.Reader.GetTableMetadataOffset(TableIndex.MethodDef) +
    metadata.Reader.GetTableRowSize(TableIndex.MethodDef);
uint imageRva = BitConverter.ToUInt32(root, rowOffset);
Require(imageRva != 0, "The fixture's MethodDef row has no RVA, so masking it tests nothing");
Require(BitConverter.ToUInt32(later) == 0, "The carried MethodDef row kept its RVA column");
Require(root.AsSpan(rowOffset + 4, later.Length - 4).SequenceEqual(later.AsSpan(4)),
    "The carried MethodDef row differs from the image's row outside its RVA column");
using var longerPe = new PEReader(new MemoryStream(Image(100)));
var longer = new MetadataImage(longerPe);
byte[] longerRoot = longerPe.GetMetadata().GetContent().ToArray();
Require(BitConverter.ToUInt32(longerRoot, rowOffset) != imageRva, "A longer earlier body did not move the RVA");
Require(longer.Row(0x06000002).AsSpan().SequenceEqual(later),
    "A longer earlier body changed the carried row of a later method");
int typeOffset = metadata.Reader.GetTableMetadataOffset(TableIndex.TypeDef) +
    metadata.Reader.GetTableRowSize(TableIndex.TypeDef);
Require(metadata.Row(0x02000002).AsSpan().SequenceEqual(
    root.AsSpan(typeOffset, metadata.Reader.GetTableRowSize(TableIndex.TypeDef))), "TypeDef row differs from image");

// The last present table has no later rows whose positions depend on its count.
byte[] zeroImage = (byte[])original.Clone();
int metadataFileOffset = pe.PEHeaders.MetadataStartOffset;
int lastCount = tableOffset + header.Length - sizeof(uint);
BinaryPrimitives.WriteUInt32LittleEndian(zeroImage.AsSpan(metadataFileOffset + lastCount), 0);
using var zeroPe = new PEReader(new MemoryStream(zeroImage));
var zero = new MetadataImage(zeroPe);
ulong valid = BitConverter.ToUInt64(header, 8);
int lastTable = 63 - System.Numerics.BitOperations.LeadingZeroCount(valid);
Require(zero.Count(lastTable) == 0, "Present-zero fixture has rows");
Require(zero.TableHeader().Length == header.Length, "Present-zero count omitted from header");
Require(zero.DecodedHeader().Contains($"({lastTable}, 0)", StringComparison.Ordinal),
    "Present-zero table omitted from decoded header");
var expectedCounts = Enumerable.Range(0, 64).Where(table => (valid & (1UL << table)) != 0)
    .Select(table => $"({table}, {zero.Count(table)})");
Require(zero.DecodedHeader() == $".ofCounts {header[6]} [{string.Join(", ", expectedCounts)}]",
    "Decoded header differs from the image table counts");
Require(ReferenceEquals(zero.DecodedHeader(), zero.DecodedHeader()), "Decoded header was not cached");
Require(zero.TableHeader().AsSpan().SequenceEqual(
    zeroImage.AsSpan(metadataFileOffset + tableOffset, header.Length)), "Present-zero header is reconstructed");

// Test truncation at every prefix, including row counts and the stream directory.
for (int length = 0; length < root.Length; length++)
{
    if (length >= tableOffset + tableSize) break;
    try
    {
        MetadataImage.ReadTableHeader(root.AsSpan(0, length));
        throw new InvalidOperationException($"Truncated metadata accepted at {length}");
    }
    catch (BadImageFormatException) { }
}
foreach (int offset in new[] { tableOffset + 4, tableOffset + 5, tableOffset + 6 })
{
    byte[] malformed = (byte[])root.Clone();
    malformed[offset] = 0x40;
    try
    {
        MetadataImage.ReadTableHeader(malformed);
        throw new InvalidOperationException($"Unsupported header accepted at {offset}");
    }
    catch (BadImageFormatException) { }
}
header[0] ^= 0xff;
Require(metadata.TableHeader()[0] == root[tableOffset], "Caller changed cached header");
Console.WriteLine("PASS masked MethodDef RVA, exact rows, present-zero table, truncations and unsupported headers");

// Warm the immutable header cache before measuring repeated row/header requests.
_ = metadata.DecodedHeader();
foreach (int count in new[] { 64, 256, 1024 })
{
    long allocated = GC.GetAllocatedBytesForCurrentThread();
    var elapsed = Stopwatch.StartNew();
    long bytes = 0;
    for (int index = 0; index < count; index++)
    {
        bytes += metadata.Row(0x06000002).Length;
        bytes += metadata.TableHeader().Length;
        bytes += metadata.DecodedHeader().Length;
    }
    elapsed.Stop();
    allocated = GC.GetAllocatedBytesForCurrentThread() - allocated;
    Console.WriteLine($"accesses={count} bytes={bytes} allocated={allocated} ticks={elapsed.ElapsedTicks}");
}
