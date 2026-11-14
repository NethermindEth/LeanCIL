#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../Extractor/Identities.cs
#:include ../Extractor/MetadataImage.cs

using System.Diagnostics;
using System.Globalization;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using System.Text;
using Mono.Cecil;
using Mono.Cecil.Cil;
using Nethermind.LeanCIL;
using Srm = System.Reflection.Metadata;

// Every identity of the corpus is rendered with ToLean(), elaborated by Lean, and shown by CIL/Identity.lean's
// display; that text must equal ToDisplay(). Each record is first checked against the raw metadata rows it reads.
var clock = Stopwatch.StartNew();
if (args.Contains("--assembly-cache-only", StringComparer.Ordinal))
{
    CheckAssemblyCache();
    return;
}
if (args.Contains("--heap-bounds-only", StringComparer.Ordinal))
{
    CheckHeapBounds();
    return;
}
if (args.Contains("--raw-names-only", StringComparer.Ordinal))
{
    CheckRawNames(At("artifacts/Identities/Unusual.dll"));
    return;
}
if (args.Contains("--code-cost", StringComparer.Ordinal))
{
    CheckCodeCost();
    return;
}
CheckScaling();
if (args.Contains("--scaling-only", StringComparer.Ordinal)) return;
CheckHeapBounds();
CheckAssemblyCache();
var directory = At("artifacts/Identities");
Directory.CreateDirectory(directory);
var examplesPath = At("Examples/Assembly/bin/Examples.dll");
var unusualPath = Path.Combine(directory, "Unusual.dll");
WriteUnusual(unusualPath);
var resolver = new DefaultAssemblyResolver();
var parameters = new ReaderParameters { AssemblyResolver = resolver };
using var examples = ModuleDefinition.ReadModule(examplesPath, parameters);
using var unusual = ModuleDefinition.ReadModule(unusualPath, parameters);
foreach (var (path, module) in new[] { (examplesPath, examples), (unusualPath, unusual) })
    CheckRows(path, module);
Console.WriteLine("PASS identity records equal the raw rows of Examples.dll and Unusual.dll");

var corpus = new IdentityCorpus();
corpus.Add(examples, resolve: true);
corpus.Add(unusual, resolve: false);
CheckTypedPredicates(examples, unusual);
CheckRawNames(unusualPath);
CheckEquality(examplesPath, parameters, corpus);
corpus.RequireCoverage();

var source = new StringBuilder("""
    import CIL.Identity
    open CIL

    /-- The UTF-8 bytes of a display in hexadecimal, so a display that spans lines prints on one. -/
    def hexOf (text : String) : String :=
      String.join (text.toUTF8.toList.map fun byte =>
        let digits := Nat.toDigits 16 byte.toNat
        String.ofList (List.replicate (2 - digits.length) '0' ++ digits))

    /-- Prints each numbered text on its own line. -/
    def emit (texts : List (Nat × String)) : IO Unit :=
      texts.forM fun (index, text) => IO.println s!"@{index}:{hexOf text}"

    #eval IO.println s!"@ranges:{invisibleRanges}"

    """);
var expected = new List<(string Kind, string Term, string Text)>();
const int ChunkSize = 64;
void Emit(string kind, IEnumerable<(string Term, string LeanText, string Text)> entries)
{
    foreach (var chunk in entries.Chunk(ChunkSize))
    {
        source.AppendLine("#eval emit [");
        source.AppendLine(string.Join(",\n", chunk.Select(entry =>
        {
            expected.Add((kind, entry.Term, entry.Text));
            return $"  ({expected.Count - 1}, {entry.LeanText})";
        })));
        source.AppendLine("]");
    }
}
static string Show(string term, string type, string function) => $"(({term} : {type}).{function})";
Emit("name", corpus.Names.SelectMany(name => new[]
{
    (name.ToLean(), Show(name.ToLean(), "MetadataName", "display"), name.ToDisplay()),
    (name.ToLean(), $"toString {Show(name.ToLean(), "MetadataName", "code")}",
        name.Code.ToString(CultureInfo.InvariantCulture))
}));
Emit("literal", corpus.Literals.SelectMany(literal => new[]
{
    (literal.ToLean(), Show(literal.ToLean(), "UserString", "display"), literal.ToDisplay()),
    (literal.ToLean(), $"toString {Show(literal.ToLean(), "UserString", "code")}",
        literal.Code.ToString(CultureInfo.InvariantCulture))
}));
Emit("version", corpus.Versions.Select(version =>
    (version.ToLean(), Show(version.ToLean(), "Version", "display"), version.ToDisplay())));
Emit("assembly", corpus.Assemblies.Select(assembly =>
    (assembly.ToLean(), Show(assembly.ToLean(), "AssemblyName", "display"), assembly.ToDisplay())));
Emit("level", corpus.Levels.Select(level =>
    (level.ToLean(), $"reprStr ({level.ToLean()} : TypeLevel)", level.ToDisplay())));
Emit("type", corpus.Types.Select(type =>
    (type.ToLean(), Show(type.ToLean(), "TypeIdentity", "display"), type.ToDisplay())));
Emit("primitive", PrimitiveType.All.SelectMany(primitive => new[]
{
    (primitive.ToLean(), Show(primitive.ToLean(), "PrimitiveType", "display"), primitive.ToDisplay()),
    (primitive.ToLean(), $"toString {Show(primitive.ToLean(), "PrimitiveType", "elementType")}",
        ((int)primitive.ElementType).ToString(CultureInfo.InvariantCulture))
}));
Emit("kind", corpus.Kinds.Select(kind =>
    (kind.ToLean(), $"reprStr ({kind.ToLean()} : TypeKind)", kind.ToDisplay())));
var leanPath = Path.Combine(directory, "Identities.lean");
File.WriteAllText(leanPath, source.ToString());
var leanClock = Stopwatch.StartNew();
var output = Run(["lake", "env", "lean", leanPath], cwd: FixturePackage());
leanClock.Stop();

var shown = new Dictionary<int, string>();
string? ranges = null;
foreach (var line in output.Split('\n').Select(line => line.TrimEnd('\r')))
{
    if (line.StartsWith("@ranges:", StringComparison.Ordinal)) ranges = line["@ranges:".Length..];
    else if (line.StartsWith('@') && line.IndexOf(':') is > 1 and var colon)
        shown.Add(int.Parse(line[1..colon], CultureInfo.InvariantCulture),
            Encoding.UTF8.GetString(Convert.FromHexString(line[(colon + 1)..])));
}
var tableText = "[" + string.Join(", ", IdentityText.InvisibleRanges.Select(range =>
    string.Create(CultureInfo.InvariantCulture, $"({range.Low}, {range.High})"))) + "]";
if (ranges != tableText)
    throw new InvalidOperationException(
        $"CIL.invisibleRanges is {ranges ?? "missing"}, the C# table {tableText}.\n" + output);
var mismatches = expected.Select((entry, index) => (entry, index))
    .Where(item => !shown.TryGetValue(item.index, out var text) || text != item.entry.Text).ToList();
if (mismatches.Count != 0)
    throw new InvalidOperationException(
        $"{mismatches.Count} of {expected.Count} Lean displays differ from ToDisplay():\n" +
        string.Join("\n", mismatches.Take(20).Select(item => $"{item.entry.Kind} {item.entry.Term}\n  Lean: " +
            $"{(shown.TryGetValue(item.index, out var text) ? text : "<none>")}\n  ToDisplay: {item.entry.Text}")) +
        "\n" + output[..Math.Min(output.Length, 4000)]);
Console.WriteLine($"PASS {expected.Count} Lean displays of {corpus.Summary()} equal ToDisplay()");
Console.WriteLine(string.Create(CultureInfo.InvariantCulture,
    $"PASS identity records cost {clock.Elapsed.TotalSeconds:F1} s, " +
    $"of which Lean took {leanClock.Elapsed.TotalSeconds:F1} s"));
CheckCodeCost();

// The rows of an image read with System.Reflection.Metadata, which shares no decoding with Cecil.
static void CheckRows(string path, ModuleDefinition module)
{
    using var image = new PEReader(File.OpenRead(path));
    var reader = Srm.PEReaderExtensions.GetMetadataReader(image);
    var metadata = image.GetMetadata().GetContent();
    int strings = reader.GetHeapMetadataOffset(Srm.Ecma335.HeapIndex.String);
    MetadataName Name(Srm.StringHandle handle)
    {
        int start = strings + MetadataTokens.GetHeapOffset(handle);
        return MetadataName.FromBytes(metadata.AsSpan()[start..metadata.IndexOf((byte)0, start)]);
    }
    void Require(bool holds, string row)
    {
        if (!holds) throw new InvalidOperationException($"{Path.GetFileName(path)}: record differs from row {row}");
    }
    foreach (var handle in reader.TypeDefinitions)
    {
        var row = reader.GetTypeDefinition(handle);
        var definition = (TypeDefinition)module.LookupToken(MetadataTokens.GetToken(handle));
        Require(TypeLevel.Of(definition, FixtureImages.For(module)) ==
            new TypeLevel(Name(row.Namespace), Name(row.Name)), definition.FullName);
    }
    foreach (var handle in reader.TypeReferences)
    {
        var row = reader.GetTypeReference(handle);
        var reference = (TypeReference)module.LookupToken(MetadataTokens.GetToken(handle));
        Require(IdentityRows.Level(FixtureImages.For(module), reference.MetadataToken) ==
            new TypeLevel(Name(row.Namespace), Name(row.Name)), reference.FullName);
    }
    AssemblyName Row(Srm.StringHandle name, Version version, Srm.StringHandle culture, bool hasKey,
        Srm.BlobHandle key)
    {
        var bytes = reader.GetBlobBytes(key);
        // ECMA-335 II.6.2.1.3: a token is the last eight bytes of the key's SHA-1 hash, reversed.
        var token = hasKey ? SHA1.HashData(bytes)[^8..].Reverse().ToArray() : bytes;
        return new(Name(name), AssemblyVersion.Of(version)!.Value, Name(culture),
            token.Length == 0 ? null : System.Buffers.Binary.BinaryPrimitives.ReadUInt64BigEndian(token));
    }
    var assembly = reader.GetAssemblyDefinition();
    Require(AssemblyName.Of(module.Assembly.Name, FixtureImages.For(module)) ==
        Row(assembly.Name, assembly.Version, assembly.Culture,
        !assembly.PublicKey.IsNil, assembly.PublicKey), "Assembly");
    var references = reader.AssemblyReferences.Select(reader.GetAssemblyReference).ToArray();
    Require(references.Length == module.AssemblyReferences.Count, "AssemblyRef count");
    for (int index = 0; index < references.Length; index++)
    {
        var row = references[index];
        Require(AssemblyName.Of(module.AssemblyReferences[index], FixtureImages.For(module)) ==
            Row(row.Name, row.Version, row.Culture,
            (row.Flags & System.Reflection.AssemblyFlags.PublicKey) != 0, row.PublicKeyOrToken),
            "AssemblyRef " + module.AssemblyReferences[index].FullName);
    }
    // ECMA-335 II.24.2.4: each #US entry is a compressed length, UTF-16 code units and one final byte.
    int userStrings = reader.GetHeapMetadataOffset(Srm.Ecma335.HeapIndex.UserString);
    var heap = new HashSet<UserString>();
    for (var handle = MetadataTokens.UserStringHandle(1); !handle.IsNil; handle = reader.GetNextHandle(handle))
    {
        int start = userStrings + MetadataTokens.GetHeapOffset(handle);
        var entry = metadata.AsSpan()[start..];
        int length = entry[0] < 0x80 ? entry[0] : entry[0] < 0xC0 ? ((entry[0] & 0x3F) << 8) | entry[1] :
            ((entry[0] & 0x1F) << 24) | (entry[1] << 16) | (entry[2] << 8) | entry[3];
        int prefix = entry[0] < 0x80 ? 1 : entry[0] < 0xC0 ? 2 : 4;
        var units = new char[(length - 1) / 2];
        for (int unit = 0; unit < units.Length; unit++)
            units[unit] = (char)(entry[prefix + 2 * unit] | (entry[prefix + 2 * unit + 1] << 8));
        heap.Add(UserString.OfLiteral(new string(units)));
    }
    foreach (var literal in Literals(module))
        Require(heap.Contains(UserString.OfLiteral(literal)), "#US " + literal);
}

static IEnumerable<string> Literals(ModuleDefinition module) => module.GetTypes().SelectMany(type => type.Methods)
    .Where(method => method.HasBody).SelectMany(method => method.Body.Instructions)
    .Where(instruction => instruction.OpCode.Code == Code.Ldstr).Select(instruction => (string)instruction.Operand);

static void CheckScaling()
{
    Measure("raw name payload", [512, 4096, 32768], size =>
    {
        var bytes = new byte[size];
        Array.Fill(bytes, (byte)0xFF);
        var name = MetadataName.FromBytes(bytes);
        return name.ToLean().Length + name.ToDisplay().Length + name.GetHashCode();
    });
    Measure("type nesting", [64, 512, 4096], size =>
    {
        var level = new TypeLevel(MetadataName.Empty, MetadataName.OfText("Nested.Name"));
        var type = new TypeIdentity(PlatformAssemblies.SystemRuntime, MetadataName.Empty,
            [.. Enumerable.Repeat(level, size)], MetadataName.OfText("Type"));
        return type.ToLean().Length + type.ToDisplay().Length + type.GetHashCode();
    });

    static void Measure(string label, int[] sizes, Func<int, int> operation)
    {
        const int Repetitions = 4;
        double previousMs = 0;
        long previousBytes = 0;
        foreach (int size in sizes)
        {
            _ = operation(size);
            double bestMs = double.MaxValue;
            long allocated = 0;
            for (int sample = 0; sample < 3; sample++)
            {
                long before = GC.GetAllocatedBytesForCurrentThread();
                var timer = Stopwatch.StartNew();
                for (int iteration = 0; iteration < Repetitions; iteration++) GC.KeepAlive(operation(size));
                timer.Stop();
                bestMs = Math.Min(bestMs, timer.Elapsed.TotalMilliseconds / Repetitions);
                allocated = (GC.GetAllocatedBytesForCurrentThread() - before) / Repetitions;
            }
            if (previousBytes != 0 && (allocated > previousBytes * 12 + 4096 || bestMs > previousMs * 16 + 10))
                throw new InvalidOperationException($"Identity {label} grows superlinearly at {size}: " +
                    $"{bestMs:F2} ms/{allocated} bytes after {previousMs:F2} ms/{previousBytes} bytes");
            Console.WriteLine($"PASS {label} {size}: {bestMs:F2} ms, {allocated} allocated bytes");
            previousMs = bestMs;
            previousBytes = allocated;
        }
    }
}

static void CheckCodeCost()
{
    double previousDecimalMs = 0;
    foreach (int size in new[] { 4096, 32768, 262144, 2097152 })
    {
        var bytes = new byte[size];
        Array.Fill(bytes, (byte)0xFF);
        var code = IdentityText.Code(bytes);
        Measure("construct", () => GC.KeepAlive(IdentityText.Code(bytes)));
        Measure("hex", () => GC.KeepAlive(code.ToString("x", CultureInfo.InvariantCulture)));
        double decimalMs = Measure("decimal", () => GC.KeepAlive(IdentityText.Decimal(code)));
        if (size == 2097152 && decimalMs > previousDecimalMs * 16 + 10)
            throw new InvalidOperationException($"Raw identity decimal display exceeds its payload scaling bound: " +
                $"{size} bytes took {decimalMs:F3} CPU ms after {previousDecimalMs:F3} CPU ms " +
                "for one eighth the payload");
        previousDecimalMs = decimalMs;

        double Measure(string label, Action action)
        {
            action();
            double best = double.MaxValue;
            double bestCpu = double.MaxValue;
            long allocated = 0;
            using var process = Process.GetCurrentProcess();
            for (int repeat = 0; repeat < 3; repeat++)
            {
                long before = GC.GetAllocatedBytesForCurrentThread();
                process.Refresh();
                TimeSpan cpuBefore = process.TotalProcessorTime;
                var timer = Stopwatch.StartNew();
                action();
                timer.Stop();
                process.Refresh();
                bestCpu = Math.Min(bestCpu, (process.TotalProcessorTime - cpuBefore).TotalMilliseconds);
                best = Math.Min(best, timer.Elapsed.TotalMilliseconds);
                allocated = GC.GetAllocatedBytesForCurrentThread() - before;
            }
            Console.WriteLine($"{label} {size}: {best:F3} ms, {bestCpu:F3} CPU ms, {allocated} allocated bytes");
            return bestCpu;
        }
    }
}

// The typed platform identity accepts only the exact System.Runtime row, and refuses without throwing a token
// that is not eight bytes; Cecil reads a type named System.Int32 in another assembly with Int32's element type.
static void CheckTypedPredicates(ModuleDefinition examples, ModuleDefinition unusual)
{
    var runtime = examples.AssemblyReferences.Single(reference =>
        AssemblyName.Of(reference, FixtureImages.For(examples)) == PlatformAssemblies.SystemRuntime);
    AssemblyNameReference Variant(Action<AssemblyNameReference> change)
    {
        var copy = new AssemblyNameReference(runtime.Name, runtime.Version)
        {
            Culture = runtime.Culture, PublicKeyToken = runtime.PublicKeyToken
        };
        change(copy);
        return copy;
    }
    var variants = new (string Name, AssemblyNameReference Reference)[]
    {
        ("version", Variant(reference => reference.Version = new Version(10, 0, 0, 0))),
        ("zero token", Variant(reference => reference.PublicKeyToken = new byte[8])),
        ("no token", Variant(reference => reference.PublicKeyToken = [])),
        ("culture", Variant(reference => reference.Culture = "en-US")),
        ("name", Variant(reference => reference.Name = "System.Runtime.Extra"))
    };
    foreach (var (name, reference) in variants)
        if (ReadVariant(reference) is not { } variant || variant == PlatformAssemblies.SystemRuntime)
            throw new InvalidOperationException("The platform identity accepts a changed " + name);
    if (ReadVariant(Variant(reference => reference.PublicKeyToken = [1, 2, 3, 4])) is not null)
        throw new InvalidOperationException("A four-byte public key token has an assembly name");
    if (ReadVariant(Variant(reference => reference.PublicKeyToken = new byte[8]))!.PublicKeyToken != 0 ||
        ReadVariant(Variant(reference => reference.PublicKeyToken = []))!.PublicKeyToken is not null)
        throw new InvalidOperationException("Eight zero token bytes and no token are not told apart");
    var forged = unusual.GetType("Odd.Holder").Fields.Single(field => field.Name == "Forged").FieldType;
    if (PrimitiveType.Of(forged, FixtureImages.For(unusual)) is not null)
        throw new InvalidOperationException($"{forged.FullName} [{forged.Scope}] reads as a primitive");
    Console.WriteLine($"PASS the typed platform identity refuses {variants.Length} changed rows, and " +
        $"[{forged.Scope.Name}]{forged.FullName}, which Cecil reads as {forged.MetadataType}, is no primitive");
}

static AssemblyName? ReadVariant(AssemblyNameReference reference)
{
    using var definition = ModuleDefinition.CreateModule("IdentityVariant", ModuleKind.Dll);
    definition.AssemblyReferences.Add(reference);
    using var stream = new MemoryStream();
    definition.Write(stream);
    byte[] bytes = stream.ToArray();
    using var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
    using var pe = new PEReader(new MemoryStream(bytes));
    return AssemblyName.Of(module.AssemblyReferences[0], new MetadataImage(pe));
}

// Distinct invalid UTF-8 bytes may decode to the same Cecil name; typed identities retain each byte.
static void CheckRawNames(string path)
{
    byte[] original = File.ReadAllBytes(path);
    using var pe = new PEReader(new MemoryStream(original));
    var reader = Srm.PEReaderExtensions.GetMetadataReader(pe);
    var typeHandle = reader.TypeDefinitions.Single(handle =>
        reader.GetString(reader.GetTypeDefinition(handle).Name) == "Dotted.Name");
    foreach (var handle in new[] { reader.GetTypeDefinition(typeHandle).Name, reader.GetAssemblyDefinition().Name })
    {
        int offset = pe.PEHeaders.MetadataStartOffset + reader.GetHeapMetadataOffset(Srm.Ecma335.HeapIndex.String) +
            MetadataTokens.GetHeapOffset(handle);
        (TypeIdentity Identity, string CecilName) Read(byte first)
        {
            byte[] changed = (byte[])original.Clone();
            changed[offset] = first;
            using var module = ModuleDefinition.ReadModule(new MemoryStream(changed));
            using var image = new PEReader(new MemoryStream(changed));
            var definition = (TypeDefinition)module.LookupToken(MetadataTokens.GetToken(typeHandle));
            return (TypeIdentity.Of(definition, new MetadataImage(image)),
                handle == reader.GetAssemblyDefinition().Name ? module.Assembly.Name.Name : definition.Name);
        }
        var first = Read(0xFE);
        var second = Read(0xFF);
        if (first.CecilName != second.CecilName || first.Identity == second.Identity)
            throw new InvalidOperationException("Raw metadata names were aliased by decoded text");
    }
    Console.WriteLine("PASS distinct malformed assembly and type names retain their raw identities");
}

// A second reading of an image gives equal records with equal hashes.
static void CheckEquality(string path, ReaderParameters parameters, IdentityCorpus corpus)
{
    using var again = ModuleDefinition.ReadModule(path, parameters);
    var types = again.GetTypes().Select(type => TypeIdentity.Of(type, FixtureImages.For(again))).ToHashSet();
    var first = corpus.Types.ToHashSet();
    if (!types.All(first.Contains) || again.GetTypes().Count() != types.Count)
        throw new InvalidOperationException("A second reading of Examples.dll gives other type identities");
    Console.WriteLine($"PASS {types.Count} type identities of a second reading equal the first");
}

static void CheckAssemblyCache()
{
    byte[] Create(int keyBytes, string name)
    {
        using var assembly = AssemblyDefinition.CreateAssembly(
            new AssemblyNameDefinition(name, new Version(1, 0)), name, ModuleKind.Dll);
        foreach (string referenceName in new[] { "First", "Second" })
            assembly.MainModule.AssemblyReferences.Add(new AssemblyNameReference(referenceName, new Version(1, 0))
                { PublicKey = new byte[keyBytes] });
        assembly.MainModule.AssemblyReferences.Add(new AssemblyNameReference("Invalid", new Version(1, 0))
            { PublicKeyToken = [1, 2, 3] });
        using var stream = new MemoryStream();
        assembly.Write(stream);
        return stream.ToArray();
    }

    foreach (int keyBytes in new[] { 4096, 32768, 262144 })
    {
        byte[] bytes = Create(keyBytes, "Cache");
        using var pe = new PEReader(new MemoryStream(bytes));
        using var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
        var image = new MetadataImage(pe);
        var references = module.AssemblyReferences;
        var first = AssemblyName.Of(references[0], image);
        var second = AssemblyName.Of(references[1], image);
        if (first is null || second is null || first == second)
            throw new InvalidOperationException("Distinct assembly rows aliased");
        if (AssemblyName.Of(references[2], image) is not null)
            throw new InvalidOperationException("Invalid token was admitted");
        long before = GC.GetAllocatedBytesForCurrentThread();
        var watch = Stopwatch.StartNew();
        for (int repeat = 0; repeat < 4096; repeat++)
        {
            if (!ReferenceEquals(first, AssemblyName.Of(references[0], image)) ||
                !ReferenceEquals(second, AssemblyName.Of(references[1], image)) ||
                AssemblyName.Of(references[2], image) is not null)
                throw new InvalidOperationException("Assembly row result was not retained by its image");
        }
        long allocated = GC.GetAllocatedBytesForCurrentThread() - before;
        if (allocated > 4096)
            throw new InvalidOperationException($"Repeated assembly rows allocated {allocated} bytes");
        Console.WriteLine($"PASS assembly key {keyBytes} bytes: 12288 lookups, {allocated} bytes, " +
            $"{watch.Elapsed.TotalMilliseconds:F3} ms");
        byte[] otherBytes = Create(keyBytes, "Other");
        using var otherPe = new PEReader(new MemoryStream(otherBytes));
        using var otherModule = ModuleDefinition.ReadModule(new MemoryStream(otherBytes));
        var otherImage = new MetadataImage(otherPe);
        if (AssemblyName.Of(module.Assembly.Name, image) == AssemblyName.Of(otherModule.Assembly.Name, otherImage) ||
            ReferenceEquals(first, AssemblyName.Of(otherModule.AssemblyReferences[0], otherImage)))
            throw new InvalidOperationException("Distinct metadata images shared a cached assembly row");
    }
}

static void CheckHeapBounds()
{
    using var assembly = AssemblyDefinition.CreateAssembly(
        new AssemblyNameDefinition("HeapBounds", new Version(1, 0)) { PublicKey = new byte[32768] },
        "HeapBounds", ModuleKind.Dll);
    var module = assembly.MainModule;
    var holder = new TypeDefinition("", "Holder", TypeAttributes.Public);
    module.Types.Add(holder);
    var method = new MethodDefinition("Literal", MethodAttributes.Public | MethodAttributes.Static,
        module.TypeSystem.Void);
    holder.Methods.Add(method);
    method.Body.Instructions.Add(Instruction.Create(OpCodes.Ldstr, new string('x', 32768)));
    method.Body.Instructions.Add(Instruction.Create(OpCodes.Pop));
    method.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    using var stream = new MemoryStream();
    assembly.Write(stream);
    byte[] original = stream.ToArray();
    using var pe = new PEReader(new MemoryStream(original));
    var metadata = new MetadataImage(pe);

    void Reject(Action action, string label)
    {
        try { action(); }
        catch (BadImageFormatException) { return; }
        throw new InvalidOperationException($"Accepted invalid heap entry: {label}");
    }

    void Check(HeapIndex heap, byte[] entry, bool valid)
    {
        int size = metadata.Reader.GetHeapSize(heap);
        int offset = size - entry.Length;
        if (heap == HeapIndex.String && !valid)
        {
            // SRM excludes trailing zero padding from the string heap's reported size.
            int physicalEnd = metadata.Reader.GetHeapMetadataOffset(HeapIndex.UserString) -
                metadata.Reader.GetHeapMetadataOffset(heap);
            entry = Enumerable.Repeat((byte)0xFF, physicalEnd - offset).ToArray();
        }
        byte[] changed = (byte[])original.Clone();
        int start = pe.PEHeaders.MetadataStartOffset + metadata.Reader.GetHeapMetadataOffset(heap) + offset;
        entry.CopyTo(changed, start);
        using var changedPe = new PEReader(new MemoryStream(changed));
        var changedMetadata = new MetadataImage(changedPe);
        byte[] Read() => heap == HeapIndex.String
            ? changedMetadata.StringEntry(offset) : changedMetadata.SizedEntry(heap, offset);
        if (valid)
        {
            if (!Read().AsSpan().SequenceEqual(entry))
                throw new InvalidOperationException($"Changed exact heap bytes: {heap}/{entry.Length}");
        }
        else Reject(() => Read(), $"{heap}/{Convert.ToHexString(entry)}");
    }

    Check(HeapIndex.String, [0], true);
    Check(HeapIndex.String, [0xFF], false);
    Reject(() => metadata.StringEntry(-1), "negative string offset");
    Reject(() => metadata.StringEntry(metadata.Reader.GetHeapSize(HeapIndex.String)), "string heap end");
    foreach (var heap in new[] { HeapIndex.Blob, HeapIndex.UserString })
    {
        Reject(() => metadata.SizedEntry(heap, -1), "negative sized offset");
        Reject(() => metadata.SizedEntry(heap, metadata.Reader.GetHeapSize(heap)), "sized heap end");
        foreach (byte[] entry in new byte[][]
            { [0x80], [0xC0], [0xC0, 0], [0xC0, 0, 0], [1], [0x80, 1], [0xC0, 0, 0, 1], [0xE0], [0xFF] })
            Check(heap, entry, false);
        foreach (int length in new[] { 0, 1, 127, 128, 16383, 16384 })
        {
            byte[] header = length < 128 ? [(byte)length] : length < 16384
                ? [(byte)(0x80 | (length >> 8)), (byte)length]
                : [(byte)(0xC0 | (length >> 24)), (byte)(length >> 16), (byte)(length >> 8), (byte)length];
            Check(heap, [.. header, .. new byte[length]], true);
        }
    }
    Reject(() => metadata.SizedEntry(HeapIndex.String, 0), "wrong sized heap");
    Console.WriteLine("PASS exact heap boundaries, malformed entries, and 1/2/4-byte lengths");
}

// The rows of an assembly hold what no example does: a culture, a zero token, names whose display falls back
// to their structure or escapes characters, a literal with an unpaired surrogate, and a forged System.Int32.
static void WriteUnusual(string path)
{
    var assemblyName = new AssemblyNameDefinition("Unusual", new Version(2, 1, 3, 4)) { Culture = "de-DE" };
    using var assembly = AssemblyDefinition.CreateAssembly(assemblyName, "Unusual", ModuleKind.Dll);
    var module = assembly.MainModule;
    var longName = string.Concat(Enumerable.Repeat("Segment", 12));
    AssemblyNameReference Reference(string name, string culture = "", byte[]? token = null)
    {
        var reference = new AssemblyNameReference(name, new Version(1, 0, 0, 0))
        {
            Culture = culture, PublicKeyToken = token ?? []
        };
        module.AssemblyReferences.Add(reference);
        return reference;
    }
    var other = Reference("Other", token: new byte[8]);
    Reference("Bracket]" + longName);
    Reference("Comma,Name");
    Reference("Spelled", "neutral");
    TypeDefinition Type(string space, string name, TypeDefinition? outer = null)
    {
        var type = new TypeDefinition(space, name, TypeAttributes.Abstract | TypeAttributes.Sealed |
            (outer is null ? TypeAttributes.Public : TypeAttributes.NestedPublic));
        if (outer is null) module.Types.Add(type);
        else outer.NestedTypes.Add(type);
        return type;
    }
    var holder = Type("Odd", "Holder");
    holder.Fields.Add(new FieldDefinition("Forged", FieldAttributes.Public | FieldAttributes.Static,
        new TypeReference("System", "Int32", module, other, true)));
    Type("Odd", "Dotted.Name");
    Type("Odd/Slashed", "Name");
    Type("Odd", "{Braced");
    Type("Odd", "Back\\slash\"quote");
    Type("Odd", "Zero\u200Bwidth");
    Type("Odd", "Tag\U000E0001");
    Type("Odd", "Größe\U0001D538");
    Type("", longName + "/" + longName, Type("", "Outer", Type("Odd", "Outermost")));
    var method = new MethodDefinition("Literals", MethodAttributes.Public | MethodAttributes.Static,
        module.TypeSystem.Void);
    holder.Methods.Add(method);
    var il = method.Body.GetILProcessor();
    foreach (var literal in new[] { "quote\" back\\ line\n", "\uD800unpaired", "\uDC00", "tag\U000E0001",
        "smile\U0001F600", "{brace" })
    {
        il.Emit(OpCodes.Ldstr, literal);
        il.Emit(OpCodes.Pop);
    }
    il.Emit(OpCodes.Ret);
    assembly.Write(path);
    byte[] bytes = File.ReadAllBytes(path);
    using (var image = new PEReader(new MemoryStream(bytes)))
    {
        var reader = Srm.PEReaderExtensions.GetMetadataReader(image);
        for (var handle = MetadataTokens.UserStringHandle(1); !handle.IsNil; handle = reader.GetNextHandle(handle))
        {
            if (reader.GetUserString(handle) != "{brace") continue;
            int start = image.PEHeaders.MetadataStartOffset +
                reader.GetHeapMetadataOffset(Srm.Ecma335.HeapIndex.UserString) + MetadataTokens.GetHeapOffset(handle);
            if (bytes[start] >= 0x80) throw new InvalidDataException("Unexpected fixture literal size");
            bytes[start + 1] = 0;
            bytes[start + 2] = 0xD8;
        }
    }
    File.WriteAllBytes(path, bytes);
}

/// <summary>Fixture image readers retained for the lifetime of this test process.</summary>
static class FixtureImages
{
    static readonly Dictionary<ModuleDefinition, (PEReader Reader, MetadataImage Image)> images = [];

    internal static MetadataImage For(ModuleDefinition module)
    {
        if (images.TryGetValue(module, out var entry)) return entry.Image;
        var reader = new PEReader(File.OpenRead(module.FileName));
        var image = new MetadataImage(reader);
        if (image.Reader.GetGuid(image.Reader.GetModuleDefinition().Mvid) != module.Mvid)
        {
            reader.Dispose();
            throw new InvalidDataException("Fixture module and image have different MVIDs");
        }
        images.Add(module, (reader, image));
        return image;
    }
}

/// <summary>The distinct identities of a corpus in the order they were found, and the cases they cover.</summary>
sealed class IdentityCorpus
{
    readonly List<MetadataName> names = [];
    readonly List<UserString> literals = [];
    readonly List<AssemblyVersion> versions = [];
    readonly List<AssemblyName> assemblies = [];
    readonly List<TypeLevel> levels = [];
    readonly List<TypeIdentity> types = [];
    readonly List<TypeKind> kinds = [];
    readonly HashSet<object> seen = [];
    readonly HashSet<PrimitiveType> primitives = [];

    internal IdentityCorpus()
    {
        Add(names, MetadataName.FromBytes([0xFE]));
        Add(names, MetadataName.FromBytes([0xC0, 0x80]));
        Add(literals, UserString.OfLiteral("\uD800"));
        Add(literals, UserString.OfLiteral("\uDC00"));
    }

    internal IReadOnlyList<MetadataName> Names => names;
    internal IReadOnlyList<UserString> Literals => literals;
    internal IReadOnlyList<AssemblyVersion> Versions => versions;
    internal IReadOnlyList<AssemblyName> Assemblies => assemblies;
    internal IReadOnlyList<TypeLevel> Levels => levels;
    internal IReadOnlyList<TypeIdentity> Types => types;
    internal IReadOnlyList<TypeKind> Kinds => kinds;

    void Add<T>(List<T> list, T item) where T : notnull
    {
        if (seen.Add(item)) list.Add(item);
    }

    /// <summary>Every identity a module's rows name; with <paramref name="resolve"/>, also the definitions its
    /// type references resolve to.</summary>
    internal void Add(ModuleDefinition module, bool resolve)
    {
        Add(AssemblyName.Of(module.Assembly.Name, FixtureImages.For(module))!);
        foreach (var reference in module.AssemblyReferences)
            Add(AssemblyName.Of(reference, FixtureImages.For(module))!);
        foreach (var definition in module.GetTypes()) Add(definition);
        if (resolve)
            foreach (var reference in module.GetTypeReferences())
                Add(reference.Resolve() ?? throw new InvalidOperationException("Unresolved " + reference.FullName));
        foreach (var field in module.GetTypes().SelectMany(type => type.Fields)) AddPrimitives(field.FieldType);
        foreach (var method in module.GetTypes().SelectMany(type => type.Methods))
        {
            foreach (var type in method.Parameters.Select(parameter => parameter.ParameterType)
                .Append(method.ReturnType).Concat(method.HasBody ? method.Body.Variables.Select(local =>
                    local.VariableType) : []))
                AddPrimitives(type);
            if (method.HasBody)
                foreach (var instruction in method.Body.Instructions.Where(item => item.OpCode.Code == Code.Ldstr))
                    Add(literals, UserString.OfLiteral((string)instruction.Operand));
        }
    }

    // The primitives a signature type names, in its element and generic argument types too.
    void AddPrimitives(TypeReference type)
    {
        if (type is GenericInstanceType generic)
            foreach (var argument in generic.GenericArguments) AddPrimitives(argument);
        // A function pointer type has no element type; its signature names the types.
        if (type is FunctionPointerType pointer)
            foreach (var part in pointer.Parameters.Select(parameter => parameter.ParameterType)
                .Append(pointer.ReturnType)) AddPrimitives(part);
        else if (type is TypeSpecification specification) AddPrimitives(specification.ElementType);
        else if (PrimitiveType.Of(type, FixtureImages.For(type.Module)) is { } primitive) primitives.Add(primitive);
    }

    void Add(AssemblyName assembly)
    {
        Add(assemblies, assembly);
        Add(versions, assembly.Version);
        Add(names, assembly.Name);
        Add(names, assembly.Culture);
    }

    void Add(TypeDefinition definition)
    {
        var type = TypeIdentity.Of(definition, FixtureImages.For(definition.Module));
        Add(types, type);
        Add(type.Assembly);
        foreach (var level in (TypeLevel[])[.. type.Enclosing, new TypeLevel(type.Namespace, type.Name)])
        {
            Add(levels, level);
            Add(names, level.Namespace);
            Add(names, level.Name);
        }
        Add(kinds, TypeKind.Of(definition, FixtureImages.For(definition.Module)));
    }

    /// <summary>Fails naming each case no identity of the corpus covers.</summary>
    internal void RequireCoverage()
    {
        (string Case, bool Covered)[] cases =
        [
            .. PrimitiveType.All.Select(primitive => ("primitive " + primitive.ToDisplay(),
                primitives.Contains(primitive))),
            ("value type", kinds.OfType<TypeKind.ValueType>().Any()),
            ("enumeration", kinds.OfType<TypeKind.EnumType>().Any()),
            ("class", kinds.OfType<TypeKind.ClassType>().Any()),
            ("interface", kinds.OfType<TypeKind.InterfaceType>().Any()),
            ("public key token", assemblies.Any(assembly => assembly.PublicKeyToken is > 0UL)),
            ("zero public key token", assemblies.Any(assembly => assembly.PublicKeyToken is 0UL)),
            ("no public key token", assemblies.Any(assembly => assembly.PublicKeyToken is null)),
            ("culture", assemblies.Any(assembly => assembly.Culture != MetadataName.Empty)),
            ("assembly shown as its structure", assemblies.Any(assembly => assembly.ToDisplay().StartsWith('{'))),
            ("nested type", types.Any(type => !type.Enclosing.IsEmpty)),
            ("type in the global namespace", types.Any(type => type.Namespace == MetadataName.Empty)),
            ("type shown as its structure", types.Any(type => type.ToDisplay().StartsWith('{'))),
            ("structure laid out on several lines", types.Any(type => type.ToDisplay().Contains('\n'))),
            ("escaped name", names.Any(name => name.ToDisplay().Contains("\\u", StringComparison.Ordinal))),
            ("name shown as its code",
                names.Any(name => name.ToDisplay().StartsWith("{ code", StringComparison.Ordinal))),
            ("literal shown as its code",
                literals.Any(literal => literal.ToDisplay().StartsWith("{ code", StringComparison.Ordinal)))
        ];
        var missing = cases.Where(item => !item.Covered).Select(item => item.Case).ToArray();
        if (missing.Length != 0)
            throw new InvalidOperationException("The identity corpus covers no " + string.Join(", ", missing));
    }

    /// <summary>The number of identities of each record.</summary>
    internal string Summary() => $"{names.Count} names, {literals.Count} literals, {versions.Count} versions, " +
        $"{assemblies.Count} assemblies, {levels.Count} levels, {types.Count} types, " +
        $"{PrimitiveType.All.Length} primitives and {kinds.Count} kinds";
}
