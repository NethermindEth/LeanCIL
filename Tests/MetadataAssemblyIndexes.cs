#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BindingAudit.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Reflection;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Security.Cryptography;
using Mono.Cecil;
using Srm = System.Reflection.Metadata;

// Direct calls isolate assembly lookup from extraction admission and proof compilation.
var extractor = Assembly.LoadFrom(ExtractorPath);
const BindingFlags Internal = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
var pinnedType = extractor.GetType("Nethermind.LeanCIL.PinnedAssemblies", throwOnError: true)!;
var sourceType = pinnedType.GetNestedType("Source", BindingFlags.Public | BindingFlags.NonPublic)!;
var collectionType = extractor.GetType("Nethermind.LeanCIL.MetadataSlices+Collection", throwOnError: true)!;
var directory = At("artifacts/MetadataAssemblyIndexes");
Directory.CreateDirectory(directory);

void CultureCollision()
{
    using var selectedAssembly = AssemblyDefinition.CreateAssembly(new("CultureSource", new(1, 0)),
        "CultureSource", ModuleKind.Dll);
    selectedAssembly.MainModule.AssemblyReferences.Add(new("CultureTarget", new(1, 0)) { Culture = "neutral" });
    using var target = AssemblyDefinition.CreateAssembly(new("CultureTarget", new(1, 0)),
        "CultureTarget", ModuleKind.Dll);
    var targetPath = Path.Combine(directory, "CultureTarget.dll");
    target.Write(targetPath);
    using var stream = new MemoryStream();
    selectedAssembly.Write(stream);
    var pins = Array.CreateInstance(sourceType, 1);
    pins.SetValue(Activator.CreateInstance(sourceType, Internal, null, [targetPath, null], null), 0);
    using var pinned = (IDisposable)Activator.CreateInstance(pinnedType, Internal, null,
        [stream.ToArray(), "test", pins, null], null)!;
    var module = (ModuleDefinition)pinnedType.GetProperty("Selected", Internal)!.GetValue(pinned)!;
    var reference = module.AssemblyReferences.Single();
    ExpectOutside(() => ((IAssemblyResolver)pinned).Resolve(reference));
    var reject = pinnedType.GetMethod("RejectMismatch", Internal)!
        .CreateDelegate<Action<AssemblyNameReference>>(pinned);
    ExpectOutside(() => reject(reference));
    var moduleOf = pinnedType.GetMethod("ModuleOf", Internal)!
        .CreateDelegate<Func<TypeReference, ModuleDefinition?>>(pinned);
    Require(moduleOf(new("Fixture", "Type", module, reference)) is null, "Mismatched culture acquired a type owner.");
    Console.WriteLine("PASS raw literal-neutral culture differs from absent culture");
}

CultureCollision();
if (args.Contains("--culture", StringComparer.Ordinal)) return;

byte[] Image(string name, int version = 1, int references = 0)
{
    using var assembly = AssemblyDefinition.CreateAssembly(new(name, new(version, 0)), name, ModuleKind.Dll);
    if (references > 0)
    {
        assembly.MainModule.AssemblyReferences.Add(new("Assembly0", new(2, 0)));
        assembly.MainModule.AssemblyReferences.Add(new("Assembly0", new(3, 0)));
        assembly.MainModule.AssemblyReferences.Add(new("Unpinned", new(1, 0)));
        for (int index = 0; index < references; index++)
            assembly.MainModule.AssemblyReferences.Add(new("Assembly" + index, new(1, 0)));
    }
    using var stream = new MemoryStream();
    assembly.Write(stream);
    return stream.ToArray();
}

IdentityCases();
if (args.Contains("--identities", StringComparer.Ordinal)) return;
ReferenceScaling();
if (args.Contains("--reference-scaling", StringComparer.Ordinal)) return;
var sources = new List<object>();
for (var index = 0; index < 4096; index++)
{
    var path = Path.Combine(directory, "Assembly" + index + ".dll");
    File.WriteAllBytes(path, Image("Assembly" + index));
    sources.Add(Activator.CreateInstance(sourceType, Internal, null, [path, null], null)!);
}

double Measure(int count)
{
    var array = Array.CreateInstance(sourceType, count);
    for (var index = 0; index < count; index++) array.SetValue(sources[index], index);
    var start = System.Diagnostics.Stopwatch.GetTimestamp();
    using var pinned = (IDisposable)Activator.CreateInstance(pinnedType, Internal, null,
        [Image("Assembly0", 9, count), "test", array, null], null)!;
    var construction = System.Diagnostics.Stopwatch.GetElapsedTime(start).TotalMilliseconds;
    var modules = ((IEnumerable<ModuleDefinition>)pinnedType.GetProperty("Modules", Internal)!
        .GetValue(pinned)!).ToArray();
    var original = pinnedType.GetMethod("Original", Internal)!
        .CreateDelegate<Func<ModuleDefinition, ModuleDefinition>>(pinned);
    var working = pinnedType.GetMethod("Working", Internal)!
        .CreateDelegate<Func<ModuleDefinition, ModuleDefinition>>(pinned);
    var position = pinnedType.GetMethod("Index", Internal)!
        .CreateDelegate<Func<ModuleDefinition, int>>(pinned);
    var rejectMismatch = pinnedType.GetMethod("RejectMismatch", Internal)!
        .CreateDelegate<Action<AssemblyNameReference>>(pinned);
    var collection = Activator.CreateInstance(collectionType, Internal, null, [pinned], null)!;
    var getSlice = collectionType.GetMethod("SliceOf", Internal)!
        .CreateDelegate<Func<ModuleDefinition, object>>(collection);
    var copies = modules.Select(original).ToArray();
    var slices = modules.Select(getSlice).ToArray();
    using var outside = AssemblyDefinition.CreateAssembly(new("Outside", new(1, 0)), "Outside", ModuleKind.Dll);
    Require(working(outside.MainModule) == outside.MainModule, "Unpinned working module changed.");
    ExpectOutside(() => original(outside.MainModule));
    ExpectOutside(() => position(copies[0]));
    var requests = modules[0].AssemblyReferences;
    ExpectOutside(() => rejectMismatch(requests[0]));
    rejectMismatch(requests[2]);
    var resolver = (IAssemblyResolver)pinned;
    try
    {
        resolver.Resolve(requests[1]);
        throw new InvalidOperationException("An unmatched assembly version was accepted.");
    }
    catch (InvalidDataException error)
    {
        Require(error.Message.Contains("Pinned: " + modules[0].Assembly.Name.FullName, StringComparison.Ordinal),
            "The first pinned assembly with this simple name changed.");
    }
    Require(resolver.Resolve(modules[^1].Assembly.Name) == modules[^1].Assembly,
        "Pinned resolution returned another module.");
    ExpectOutside(() => resolver.Resolve(requests[2]));

    var times = new List<double>();
    for (var repeat = 0; repeat < 6; repeat++)
    {
        start = System.Diagnostics.Stopwatch.GetTimestamp();
        for (var pass = 0; pass < 8; pass++)
        for (var index = 0; index < modules.Length; index++)
        {
            Require(original(copies[index]) == copies[index] && working(copies[index]) == modules[index] &&
                working(modules[index]) == modules[index] && position(modules[index]) == index,
                "Original/working mapping or command-line position changed.");
            Require(ReferenceEquals(getSlice(modules[index]), slices[index]) &&
                ReferenceEquals(getSlice(copies[index]), slices[index]), "Module evidence was duplicated.");
            rejectMismatch(requests[2]);
            if (index > 0)
                Require(resolver.Resolve(requests[index + 2]) == modules[index].Assembly,
                    "Repeated row lookup returned another assembly.");
        }
        var elapsed = System.Diagnostics.Stopwatch.GetElapsedTime(start).TotalMilliseconds;
        if (repeat > 0) times.Add(elapsed);
    }
    times.Sort();
    Console.WriteLine($"{count} assemblies: construction {construction:F2} ms, queries {times[2]:F2} ms");
    return times[2];
}

var small = Measure(512);
var large = Measure(4096);
Require(large < small * 24 + 30, "Assembly lookup cost grew faster than indexed queries.");
Console.WriteLine("PASS stable module positions, original copies, missing/versioned references and lookup scaling");

IDisposable Pin(byte[] selected, params byte[][] targets)
{
    var pins = Array.CreateInstance(sourceType, targets.Length);
    for (int index = 0; index < targets.Length; index++)
    {
        string path = Path.Combine(directory, "IdentityTarget" + index + ".dll");
        File.WriteAllBytes(path, targets[index]);
        pins.SetValue(Activator.CreateInstance(sourceType, Internal, null, [path, null], null), index);
    }
    return (IDisposable)Activator.CreateInstance(pinnedType, Internal, null, [selected, "test", pins, null], null)!;
}

static byte[] Serialize(AssemblyNameDefinition name, params AssemblyNameReference[] references)
{
    using var assembly = AssemblyDefinition.CreateAssembly(name, "IdentityFixture", ModuleKind.Dll);
    foreach (var reference in references) assembly.MainModule.AssemblyReferences.Add(reference);
    using var stream = new MemoryStream();
    assembly.Write(stream);
    return stream.ToArray();
}

ModuleDefinition Selected(IDisposable pinned) =>
    (ModuleDefinition)pinnedType.GetProperty("Selected", Internal)!.GetValue(pinned)!;

void IdentityCases()
{
    byte[] empty = Serialize(new("Target", new(1, 2, 3, 4)));
    byte[] neutral = Serialize(new("Target", new(1, 2, 3, 4)) { Culture = "neutral" });
    byte[] zero = Serialize(new("Target", new(1, 2, 3, 4)) { PublicKey = new byte[8], Attributes = 0 });
    var references = new[]
    {
        new AssemblyNameReference("Target", new(1, 2, 3, 4)),
        new AssemblyNameReference("Target", new(1, 2, 3, 4)) { Culture = "neutral" },
        new AssemblyNameReference("Target", new(1, 2, 3, 4)) { PublicKeyToken = new byte[8] },
        new AssemblyNameReference("Target", new(2, 2, 3, 4)),
        new AssemblyNameReference("Target", new(1, 3, 3, 4)),
        new AssemblyNameReference("Target", new(1, 2, 4, 4)),
        new AssemblyNameReference("Target", new(1, 2, 3, 5))
    };
    using (var pinned = Pin(Serialize(new("Source", new(1, 0)), references), empty, neutral, zero))
    {
        var module = Selected(pinned);
        var resolver = (IAssemblyResolver)pinned;
        var targets = ((IEnumerable<ModuleDefinition>)pinnedType.GetProperty("Modules", Internal)!
            .GetValue(pinned)!).Skip(1).ToArray();
        var moduleOf = pinnedType.GetMethod("ModuleOf", Internal)!
            .CreateDelegate<Func<TypeReference, ModuleDefinition?>>(pinned);
        var original = pinnedType.GetMethod("Original", Internal)!
            .CreateDelegate<Func<ModuleDefinition, ModuleDefinition>>(pinned);
        var contains = pinnedType.GetMethod("Contains", Internal)!
            .CreateDelegate<Func<ModuleDefinition, bool>>(pinned);
        for (int index = 0; index < 3; index++)
        {
            var reference = module.AssemblyReferences[index];
            Require(resolver.Resolve(reference) == targets[index].Assembly, "Raw identity resolved another pin.");
            Require(moduleOf(new("Fixture", "Type", module, reference)) == targets[index],
                "Type scope lost raw identity.");
            Require(resolver.Resolve(original(module).AssemblyReferences[index]) == targets[index].Assembly,
                "Original reference resolved another pin.");
        }
        for (int index = 3; index < references.Length; index++)
            ExpectOutside(() => resolver.Resolve(module.AssemblyReferences[index]));
        var changed = module.AssemblyReferences[0];
        changed.Name = "Other";
        changed.Culture = "neutral";
        changed.Version = new(99, 98, 97, 96);
        changed.PublicKeyToken = new byte[8];
        changed.MetadataToken = new(TokenType.AssemblyRef, 3);
        Require(resolver.Resolve(changed) == targets[0].Assembly, "Mutable Cecil columns redirected a raw row.");
        targets[0].Assembly.Name.Name = "ChangedDefinition";
        Require(contains(targets[0]) && !contains(original(targets[0])), "Executable membership changed.");
        Require(resolver.Resolve(targets[0].Assembly.Name) == targets[0].Assembly,
            "Mutable definition name redirected resolution.");
        ExpectOutside(() => resolver.Resolve(new("Target", new(1, 2, 3, 4))
            { MetadataToken = new(TokenType.AssemblyRef, 1) }));
    }
    CheckRawNames();
    CheckKeysAndFlags();
    CheckPlatform();
    CheckOwnership();
    CheckEntryType();
    Console.WriteLine("PASS raw identities, provenance, flags, platform equality and ownership");
}

void CheckRawNames()
{
    byte[] Variant(byte invalid, bool source)
    {
        byte[] bytes = source ? Serialize(new("Source", new(1, 0)), new AssemblyNameReference("BadX", new(1, 0))) :
            Serialize(new("BadX", new(1, 0)));
        using var pe = new PEReader(new MemoryStream(bytes, writable: false));
        var reader = Srm.PEReaderExtensions.GetMetadataReader(pe);
        var handle = source ? reader.GetAssemblyReference(reader.AssemblyReferences.Single()).Name :
            reader.GetAssemblyDefinition().Name;
        int offset = pe.PEHeaders.MetadataStartOffset + reader.GetHeapMetadataOffset(HeapIndex.String) +
            MetadataTokens.GetHeapOffset(handle);
        bytes[offset + 3] = invalid;
        return bytes;
    }
    using var pinned = Pin(Variant(0xff, true), Variant(0xff, false), Variant(0xfe, false));
    var modules = ((IEnumerable<ModuleDefinition>)pinnedType.GetProperty("Modules", Internal)!
        .GetValue(pinned)!).ToArray();
    Require(modules[1].Assembly.Name.FullName == modules[2].Assembly.Name.FullName,
        "Invalid UTF-8 fixture no longer collides in Cecil display.");
    Require(((IAssemblyResolver)pinned).Resolve(modules[0].AssemblyReferences.Single()) == modules[1].Assembly,
        "Invalid UTF-8 bytes aliased another pin.");
    using var other = Pin(Variant(0xfe, true), Variant(0xff, false), Variant(0xfe, false));
    var otherModules = ((IEnumerable<ModuleDefinition>)pinnedType.GetProperty("Modules", Internal)!
        .GetValue(other)!).ToArray();
    Require(((IAssemblyResolver)other).Resolve(otherModules[0].AssemblyReferences.Single()) ==
        otherModules[2].Assembly,
        "Equal row indices in different images aliased.");
    ExpectOutside(() => ((IAssemblyResolver)pinned).Resolve(otherModules[0].AssemblyReferences.Single()));
    using var shared = Pin(Serialize(new("FirstSource", new(1, 0)),
        new AssemblyNameReference("FirstTarget", new(1, 0))),
        Serialize(new("SecondSource", new(1, 0)), new AssemblyNameReference("SecondTarget", new(1, 0))),
        Serialize(new("FirstTarget", new(1, 0))), Serialize(new("SecondTarget", new(1, 0))));
    var sharedModules = ((IEnumerable<ModuleDefinition>)pinnedType.GetProperty("Modules", Internal)!
        .GetValue(shared)!).ToArray();
    for (int index = 0; index < 2; index++)
    {
        var reference = sharedModules[index].AssemblyReferences.Single();
        Require(reference.MetadataToken.RID == 1 &&
            ((IAssemblyResolver)shared).Resolve(reference) == sharedModules[index + 2].Assembly,
            "Equal reference row indices in one pinned set lost their owning images.");
    }
}

void CheckKeysAndFlags()
{
    byte[] key = Enumerable.Range(0, 64).Select(index => (byte)index).ToArray();
    byte[] token = SHA1.HashData(key)[^8..].Reverse().ToArray();
    var target = new AssemblyNameDefinition("Signed", new(1, 0))
        { PublicKey = key, HashAlgorithm = Mono.Cecil.AssemblyHashAlgorithm.Reserved };
    using (var pinned = Pin(Serialize(new("Source", new(1, 0)),
        new("Signed", new(1, 0)) { PublicKey = key }, new("Signed", new(1, 0)) { PublicKeyToken = token }),
        Serialize(target)))
    {
        var requests = Selected(pinned).AssemblyReferences;
        Require(((IAssemblyResolver)pinned).Resolve(requests[0]) == ((IAssemblyResolver)pinned).Resolve(requests[1]),
            "Full public key and equivalent token resolved apart.");
    }
    var invalid = new List<AssemblyNameReference>
    {
        new("FlagTarget", new(1, 0)),
        new("FlagTarget", new(1, 0)) { PublicKeyToken = [1, 2, 3] }
    };
    foreach (uint flag in new uint[] { 0x0100, 0x0200, 0x0400, 0x0800, 0x4000, 0x8000, 0x0020, 0x80000000 })
        invalid.Add(new("FlagTarget", new(1, 0)) { Attributes = (AssemblyAttributes)flag });
    using (var pinned = Pin(Serialize(new("Source", new(1, 0)), [.. invalid]),
        Serialize(new("FlagTarget", new(1, 0)))))
    {
        var resolver = (IAssemblyResolver)pinned;
        var requests = Selected(pinned).AssemblyReferences;
        Require(resolver.Resolve(requests[0]).Name.Name == "FlagTarget", "Valid flag control did not resolve.");
        ExpectRejected(() => resolver.Resolve(requests[1]), "Invalid assembly identity in image row");
        foreach (var request in requests.Skip(2))
            ExpectRejected(() => resolver.Resolve(request), "Unsupported assembly identity flags in image row");
    }
    using (var pinned = Pin(Serialize(new("JitFlags", new(1, 0)) { Attributes = (AssemblyAttributes)0xc000 })))
        Require(((IAssemblyResolver)pinned).Resolve(Selected(pinned).Assembly.Name) == Selected(pinned).Assembly,
            "Definition JIT flags changed identity admission.");
    foreach (uint flag in new uint[] { 0x0100, 0x0200, 0x0400, 0x0800, 0x0020, 0x80000000 })
        ExpectOutside(() => { using var rejected = Pin(Serialize(new("BadFlags", new(1, 0))
            { Attributes = (AssemblyAttributes)flag })); });
}

void CheckPlatform()
{
    var runtime = typeof(object).Assembly.GetName();
    var name = runtime.Name!;
    byte[] token = runtime.GetPublicKeyToken()!;
    var requests = new[]
    {
        new AssemblyNameReference(name, runtime.Version!) { PublicKeyToken = token },
        new AssemblyNameReference(name, new(1, 2, 3, 4)) { PublicKeyToken = token },
        new AssemblyNameReference(name, runtime.Version!) { PublicKeyToken = token, Culture = "neutral" },
        new AssemblyNameReference(name.ToLowerInvariant(), runtime.Version!) { PublicKeyToken = token },
        new AssemblyNameReference(name, runtime.Version!)
            { PublicKeyToken = Convert.FromHexString("b03f5f7f11d50a3a") }
    };
    using var pinned = Pin(Serialize(new("PlatformSource", new(1, 0)), requests),
        Serialize(new(name, runtime.Version!)));
    var module = Selected(pinned);
    var resolver = (IAssemblyResolver)pinned;
    var first = resolver.Resolve(module.AssemblyReferences[0]);
    Require(first == resolver.Resolve(module.AssemblyReferences[1]), "Runtime versions did not reuse one module.");
    Require(first == resolver.Resolve(module.AssemblyReferences[0]), "Repeated runtime request duplicated a module.");
    for (int index = 2; index < requests.Length; index++)
        ExpectOutside(() => resolver.Resolve(module.AssemblyReferences[index]));
    using var noCore = Pin(Serialize(new("NoCore", new(1, 0))));
    var synthetic = Selected(noCore).TypeSystem.CoreLibrary as AssemblyNameReference ??
        throw new InvalidOperationException("Expected a synthetic core reference.");
    ExpectOutside(() => ((IAssemblyResolver)noCore).Resolve(synthetic));
}

void CheckOwnership()
{
    byte[] bytes = Serialize(new("Owner", new(1, 0)), new AssemblyNameReference("Absent", new(1, 0)));
    using var pinned = Pin(bytes);
    var register = pinnedType.GetMethod("RegisterIdentityImage", Internal)!
        .CreateDelegate<Action<ModuleDefinition, byte[]>>(pinned);
    var unregister = pinnedType.GetMethod("UnregisterIdentityImage", Internal)!
        .CreateDelegate<Action<ModuleDefinition>>(pinned);
    var contains = pinnedType.GetMethod("Contains", Internal)!
        .CreateDelegate<Func<ModuleDefinition, bool>>(pinned);
    var reject = pinnedType.GetMethod("RejectMismatch", Internal)!
        .CreateDelegate<Action<AssemblyNameReference>>(pinned);
    var rows = (System.Collections.IDictionary)pinnedType.GetField("rowsByImage", Internal)!.GetValue(pinned)!;
    int rowsBefore = rows.Count;
    byte[] invalid = Serialize(new("InvalidImport", new(1, 0)) { Attributes = (AssemblyAttributes)0x100 });
    using var invalidStream = new MemoryStream(invalid, writable: false);
    using var invalidModule = ModuleDefinition.ReadModule(invalidStream);
    ExpectOutside(() => register(invalidModule, invalid));
    Require(rows.Count == rowsBefore, "Rejected import retained its image rows.");
    ExpectOutside(() => reject(invalidModule.Assembly.Name));
    using var stream = new MemoryStream(bytes, writable: false);
    using var imported = ModuleDefinition.ReadModule(stream);
    register(imported, bytes);
    Require(!contains(imported), "Import registration admitted executable membership.");
    reject(imported.AssemblyReferences[0]);
    ExpectOutside(() => register(imported, bytes));
    reject(imported.AssemblyReferences[0]);
    Require(rows.Count == rowsBefore + 1, "Duplicate import registration changed its existing image rows.");
    unregister(imported);
    Require(rows.Count == rowsBefore, "Released import retained its image rows.");
    ExpectOutside(() => reject(imported.AssemblyReferences[0]));
    var active = pinnedType.GetProperty("Active", BindingFlags.NonPublic | BindingFlags.Static)!;
    ExpectOutside(() => { using var duplicate = Pin(bytes, bytes); });
    Require(ReferenceEquals(active.GetValue(null), pinned), "Constructor failure replaced the active owner.");
    var owned = (System.Collections.IDictionary)pinnedType.GetField("ownedModules", Internal)!.GetValue(pinned)!;
    var streams = owned.Values.Cast<MemoryStream>().ToArray();
    var reference = Selected(pinned).AssemblyReferences[0];
    pinned.Dispose();
    pinned.Dispose();
    Require(streams.All(item => !item.CanRead), "Disposed resolver retained an owned module stream.");
    ExpectOutside(() => reject(reference));

    var read = extractor.GetType("Nethermind.LeanCIL.StaticData", true)!
        .GetMethod("ReadModule", BindingFlags.Static | BindingFlags.NonPublic)!;
    MemoryStream? failedStream = null;
    Action<MemoryStream> failRetention = stream =>
    {
        failedStream = stream;
        throw new InvalidDataException("Retention callback rejected ownership");
    };
    ExpectOutside(() => read.Invoke(null, [bytes, null, failRetention]));
    Require(failedStream is { CanRead: false }, "Failed ownership callback retained an open stream.");
}

void CheckEntryType()
{
    using var target = AssemblyDefinition.CreateAssembly(new("ValueOwner", new(1, 0)), "ValueOwner", ModuleKind.Dll);
    var core = new AssemblyNameReference("System.Runtime", new(11, 0, 0, 0))
        { PublicKeyToken = Convert.FromHexString("b03f5f7f11d50a3a") };
    target.MainModule.AssemblyReferences.Add(core);
    target.MainModule.Types.Add(new("Fixture", "Value", Mono.Cecil.TypeAttributes.Public |
        Mono.Cecil.TypeAttributes.Sealed | Mono.Cecil.TypeAttributes.SequentialLayout,
        new TypeReference("System", "ValueType", target.MainModule, core)));
    using var stream = new MemoryStream();
    target.Write(stream);
    using var pinned = Pin(Serialize(new("Entry", new(1, 0))), stream.ToArray());
    var module = Selected(pinned);
    var method = extractor.GetType("Nethermind.LeanCIL.ContractMethodMetadata", true)!
        .GetMethod("EntryArgument", BindingFlags.Static | BindingFlags.NonPublic)!;
    var argument = (TypeReference)method.Invoke(null, [module, "Fixture.Value, ValueOwner"])!;
    Require(argument is TypeDefinition && argument.Module != module &&
        argument.MetadataToken.TokenType == TokenType.TypeDef && ReferenceEquals(argument.Resolve(), argument) &&
        module.AssemblyReferences.Count == 0, "Pinned entry type lost its defining image provenance.");
}

void ReferenceScaling()
{
    (long Registration, long Decoding, long Queries) MeasureReferences(int count, int nameBytes, int keyBytes)
    {
        var requests = new AssemblyNameReference[count];
        for (int index = 0; index < count; index++)
            requests[index] = new(new string('N', nameBytes - 4) + index.ToString("D4"), new(1, 0))
                { PublicKey = new byte[keyBytes] };
        byte[] bytes = Serialize(new("Scaling", new(1, 0)), requests);
        long allocated = GC.GetAllocatedBytesForCurrentThread();
        long started = System.Diagnostics.Stopwatch.GetTimestamp();
        using var pinned = Pin(bytes);
        double registrationMs = System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds;
        long registration = GC.GetAllocatedBytesForCurrentThread() - allocated;
        var reject = pinnedType.GetMethod("RejectMismatch", Internal)!
            .CreateDelegate<Action<AssemblyNameReference>>(pinned);
        var module = Selected(pinned);
        allocated = GC.GetAllocatedBytesForCurrentThread();
        started = System.Diagnostics.Stopwatch.GetTimestamp();
        foreach (var reference in module.AssemblyReferences) reject(reference);
        double decodingMs = System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds;
        long decoding = GC.GetAllocatedBytesForCurrentThread() - allocated;
        var metadata = pinnedType.GetMethod("Metadata", Internal)!.Invoke(pinned, [module])!;
        var cache = (System.Collections.IDictionary)metadata.GetType().GetField("assemblyIdentities", Internal)!
            .GetValue(metadata)!;
        Require(cache.Count == count + 1, "Raw identities were not cached once per requested row.");
        var cached = cache.Values.Cast<object>().ToArray();
        allocated = GC.GetAllocatedBytesForCurrentThread();
        started = System.Diagnostics.Stopwatch.GetTimestamp();
        for (int repeat = 0; repeat < 64; repeat++)
            foreach (var reference in module.AssemblyReferences) reject(reference);
        double queryMs = System.Diagnostics.Stopwatch.GetElapsedTime(started).TotalMilliseconds;
        long queries = GC.GetAllocatedBytesForCurrentThread() - allocated;
        Require(cache.Count == cached.Length && cache.Values.Cast<object>().Zip(cached)
            .All(pair => ReferenceEquals(pair.First, pair.Second)), "Repeated resolution rebuilt raw identities.");
        Console.WriteLine($"{count} refs, name/key {nameBytes}/{keyBytes}: registration {registrationMs:F2} ms " +
            $"{registration} B, decoding {decodingMs:F2} ms {decoding} B, queries {queryMs:F2} ms {queries} B");
        return (registration, decoding, queries);
    }

    MeasureReferences(8, 16, 64);
    (long Registration, long Decoding, long Queries)? previous = null;
    foreach (int count in new[] { 64, 256, 1024 })
    {
        var current = MeasureReferences(count, 64, 256);
        if (previous is { } prior)
            Require(current.Registration < prior.Registration * 6 && current.Decoding < prior.Decoding * 6 &&
                current.Queries < prior.Queries * 6 + 1024, "Reference count allocation grew superlinearly.");
        previous = current;
    }
    previous = null;
    foreach (int size in new[] { 16, 64, 256 })
    {
        var current = MeasureReferences(64, size, size * 4);
        if (previous is { } prior)
            Require(current.Registration < prior.Registration * 6 && current.Decoding < prior.Decoding * 6,
                "Identity payload allocation grew superlinearly.");
        previous = current;
    }
}

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

static void ExpectRejected(Action action, string message)
{
    try { action(); }
    catch (InvalidDataException error) when (error.Message == message) { return; }
    throw new InvalidOperationException("Expected exact assembly identity rejection: " + message);
}

static void ExpectOutside(Action action)
{
    try { action(); }
    catch (InvalidDataException) { return; }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException) { return; }
    throw new InvalidOperationException("An unpinned module or mismatched reference was accepted.");
}
