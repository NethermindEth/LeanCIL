#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AssemblyName=LeanCIL.IdentityTests
#:project ../Extractor/Extractor.csproj
#:package Mono.Cecil

extern alias IdentityExtractor;

using System.Buffers.Binary;
using System.Collections.Immutable;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;
using IdentityExtractor::Nethermind.LeanCIL;
using MetadataReaderProvider = System.Reflection.Metadata.MetadataReaderProvider;

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
            for (int index = 0; index < padding; index++)
                method.Body.Instructions.Add(Instruction.Create(OpCodes.Nop));
        method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    }
    using var output = new MemoryStream();
    module.Write(output);
    return output.ToArray();
}

// The stream directory of a metadata root: each header's position, the stream's offset and size, and its name.
static List<(int At, int Offset, int Size, string Name)> Streams(byte[] metadata)
{
    int at = 20 + BitConverter.ToInt32(metadata, 12);
    int count = BitConverter.ToUInt16(metadata, at - 2);
    var streams = new List<(int, int, int, string)>();
    for (int stream = 0; stream < count; stream++)
    {
        int nameEnd = Array.IndexOf(metadata, (byte)0, at + 8);
        streams.Add((at, BitConverter.ToInt32(metadata, at), BitConverter.ToInt32(metadata, at + 4),
            Encoding.ASCII.GetString(metadata, at + 8, nameEnd - at - 8)));
        at = (nameEnd + 4) & ~3;
    }
    return streams;
}

// A root whose version field holds the table stream header at offset 16 and which ends after its directory.
static byte[] Synthetic(byte[] table, ushort? count, params (uint Offset, uint Size, byte[] Name)[] streams)
{
    using var root = new MemoryStream();
    using var writer = new BinaryWriter(root);
    int versionLength = (table.Length + 3) & ~3;
    writer.Write(0x424A5342u); writer.Write(0x00010001u); writer.Write(0u); writer.Write(versionLength);
    writer.Write(table); writer.Write(new byte[versionLength - table.Length]);
    writer.Write((ushort)0); writer.Write(count ?? (ushort)streams.Length);
    foreach (var (offset, size, name) in streams)
    {
        writer.Write(offset); writer.Write(size);
        writer.Write(name); writer.Write(new byte[((name.Length + 3) & ~3) - name.Length]);
    }
    writer.Flush();
    return root.ToArray();
}

// A root rebuilt with a version field of versionLength bytes and each stream header on a four-byte boundary
// of the root, which is how System.Reflection.Metadata walks the directory.
static byte[] Realigned(byte[] metadata, int versionLength)
{
    var streams = Streams(metadata);
    int directory = 16 + versionLength + 4;
    int dataAt = directory;
    foreach (var stream in streams) dataAt = (dataAt + 8 + stream.Name.Length + 4) & ~3;
    var root = new byte[dataAt + streams.Sum(stream => (stream.Size + 3) & ~3)];
    metadata.AsSpan(0, 12).CopyTo(root);
    BinaryPrimitives.WriteInt32LittleEndian(root.AsSpan(12), versionLength);
    metadata.AsSpan(16, Math.Min(versionLength, BitConverter.ToInt32(metadata, 12))).CopyTo(root.AsSpan(16));
    BinaryPrimitives.WriteUInt16LittleEndian(root.AsSpan(directory - 2), (ushort)streams.Count);
    int at = directory;
    foreach (var stream in streams)
    {
        BinaryPrimitives.WriteInt32LittleEndian(root.AsSpan(at), dataAt);
        BinaryPrimitives.WriteInt32LittleEndian(root.AsSpan(at + 4), stream.Size);
        Encoding.ASCII.GetBytes(stream.Name).CopyTo(root, at + 8);
        metadata.AsSpan(stream.Offset, stream.Size).CopyTo(root.AsSpan(dataAt));
        dataAt += (stream.Size + 3) & ~3;
        at = (at + 8 + stream.Name.Length + 4) & ~3;
    }
    return root;
}

static bool ReaderAccepts(byte[] metadata)
{
    try { MetadataReaderProvider.FromMetadataImage(ImmutableArray.Create(metadata)).GetMetadataReader(); }
    catch (BadImageFormatException) { return false; }
    return true;
}

static void Refused<TException>(string label, string reason, Action read) where TException : Exception
{
    try { read(); }
    catch (TException error) when (error.Message.Contains(reason, StringComparison.Ordinal)) { return; }
    catch (Exception error)
    {
        throw new InvalidOperationException($"{label}: expected \"{reason}\", got {error.GetType().Name}: " +
            error.Message);
    }
    throw new InvalidOperationException($"{label}: accepted");
}

static void Bad(string label, string reason, byte[] metadata) =>
    Refused<BadImageFormatException>(label, reason, () => MetadataImage.ReadTableHeader(metadata));

static byte[] Patched(byte[] source, Action<byte[]> patch)
{
    var copy = (byte[])source.Clone();
    patch(copy);
    return copy;
}

byte[] original = Image(0);
using var pe = new PEReader(new MemoryStream(original));
var metadata = new MetadataImage(pe);
byte[] root = pe.GetMetadata().GetContent().ToArray();
var tableEntry = Streams(root).Single(stream => stream.Name == "#~");
var (tableOffset, tableSize) = (tableEntry.Offset, tableEntry.Size);
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
header[0] ^= 0xff;
Require(metadata.TableHeader()[0] == root[tableOffset], "Caller changed cached header");
header[0] ^= 0xff;
Console.WriteLine("PASS carried MethodDef rows mask the RVA, other rows are exact, present-zero tables are kept");

// Truncation at every prefix of the root up to the end of the table stream.
for (int length = 0; length < tableOffset + tableSize; length++)
{
    try
    {
        MetadataImage.ReadTableHeader(root.AsSpan(0, length));
        throw new InvalidOperationException($"Truncated metadata accepted at {length}");
    }
    catch (BadImageFormatException) { }
}
foreach (int offset in new[] { tableOffset + 4, tableOffset + 5, tableOffset + 6 })
    Bad($"header byte {offset}", "Unsupported metadata table stream header",
        Patched(root, copy => copy[offset] = 0x40));

// One rejection per bound, each with its own reason.
byte[] tableName = "#~\0"u8.ToArray();
uint size = (uint)header.Length;
Require(MetadataImage.ReadTableHeader(Synthetic(header, null, (16, size, tableName))).AsSpan().SequenceEqual(header),
    "The synthetic root does not read back its header");
Bad("short root", "shorter than its fixed fields", root[..15]);
Bad("signature", "Invalid metadata root signature", Patched(root, copy => copy[0] ^= 1));
byte[] unpadded = Realigned(root, 13);
Require(ReaderAccepts(unpadded), "System.Reflection.Metadata refuses the unpadded version length fixture");
Bad("unpadded version", "not a multiple of 4", unpadded);
Bad("long version", "not a multiple of 4", Realigned(root, 260));
Bad("directory", "stream directory crosses", root[..30]);
Bad("no stream", "names no #~ stream", Synthetic(header, 0, (16, size, tableName)));
Bad("stream count", "stream header crosses", Synthetic(header, 2, (16, size, tableName)));
Bad("long name", "no terminator within 32 bytes",
    Synthetic(header, null, (0, 0, Encoding.ASCII.GetBytes(new string('A', 32) + "\0")), (16, size, tableName)));
Bad("name padding", "name padding crosses", Synthetic(header, null, (16, size, tableName))[..^1]);
Bad("offset", "table stream crosses", Synthetic(header, null, (0xFFFFFFF0, 0x20, tableName)));
Bad("size", "table stream crosses", Synthetic(header, null, (16, 0x80000000, tableName)));
Bad("end", "table stream crosses", Synthetic(header, null, (16, 0x1000, tableName)));
Bad("fixed header", "shorter than its fixed header", Synthetic(header, null, (16, 23, tableName)));
Bad("row counts", "ends inside its row counts", Synthetic(header, null, (16, size - 1, tableName)));
Bad("two streams", "two #~ streams", Synthetic(header, null, (16, size, tableName), (16, size, tableName)));
Refused<NotSupportedException>("uncompressed", "#- is not supported",
    () => MetadataImage.ReadTableHeader(Synthetic(header, null, (16, size, "#-\0"u8.ToArray()))));

// System.Reflection.Metadata reads both images below, so the refusal is this reader's.
var blob = Streams(root).Single(stream => stream.Name == "#Blob");
byte[] twoTables = Patched(original, image =>
{
    var at = metadataFileOffset + blob.At;
    BinaryPrimitives.WriteInt32LittleEndian(image.AsSpan(at), tableOffset);
    BinaryPrimitives.WriteInt32LittleEndian(image.AsSpan(at + 4), tableSize);
    "#~\0\0\0\0\0\0"u8.CopyTo(image.AsSpan(at + 8));
});
byte[] uncompressed = Patched(original, image => image[metadataFileOffset + tableEntry.At + 9] = (byte)'-');
foreach (var (label, image) in new[] { ("two #~", twoTables), ("#-", uncompressed) })
{
    using var patched = new PEReader(new MemoryStream(image));
    System.Reflection.Metadata.PEReaderExtensions.GetMetadataReader(patched);
    if (label == "#-")
        Refused<NotSupportedException>(label, "#- is not supported", () => new MetadataImage(patched));
    else Refused<BadImageFormatException>(label, "two #~ streams", () => new MetadataImage(patched));
}
Console.WriteLine("PASS truncations, each header bound, two table streams and the #- stream are refused");

// Per request, a row and a header copy: allocation is constant per request and linear in the present tables.
_ = metadata.DecodedHeader();
double perRequest = 0;
foreach (int count in new[] { 64, 256, 1024 })
{
    long allocated = GC.GetAllocatedBytesForCurrentThread();
    long bytes = 0;
    for (int index = 0; index < count; index++)
    {
        bytes += metadata.Row(0x06000002).Length;
        bytes += metadata.TableHeader().Length;
        bytes += metadata.DecodedHeader().Length;
    }
    allocated = GC.GetAllocatedBytesForCurrentThread() - allocated;
    Console.WriteLine($"requests={count} bytes={bytes} allocated={allocated} perRequest={allocated / count}");
    if (perRequest == 0) perRequest = (double)allocated / count;
    else Require((double)allocated / count <= perRequest * 1.25, "Allocation per request grows with requests");
}
foreach (int tables in new[] { 1, 16, 45 })
{
    byte[] wide = new byte[24 + 4 * tables];
    header.AsSpan(0, 8).CopyTo(wide);
    BinaryPrimitives.WriteUInt64LittleEndian(wide.AsSpan(8), (1UL << tables) - 1);
    byte[] wideRoot = Synthetic(wide, null, (16, (uint)wide.Length, tableName));
    _ = MetadataImage.ReadTableHeader(wideRoot);
    const int Reads = 256;
    long allocated = GC.GetAllocatedBytesForCurrentThread();
    for (int index = 0; index < Reads; index++) _ = MetadataImage.ReadTableHeader(wideRoot);
    allocated = (GC.GetAllocatedBytesForCurrentThread() - allocated) / Reads;
    Console.WriteLine($"tables={tables} headerBytes={wide.Length} allocatedPerRead={allocated}");
    Require(allocated <= wide.Length + 40, "Reading the header allocates more than one copy of it");
}
