#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using Mono.Cecil;

// Direct calls isolate assembly lookup from extraction admission and proof compilation.
var extractor = Assembly.LoadFrom(ExtractorPath);
const BindingFlags Internal = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
var pinnedType = extractor.GetType("Nethermind.LeanCIL.PinnedAssemblies", throwOnError: true)!;
var sourceType = pinnedType.GetNestedType("Source", BindingFlags.Public | BindingFlags.NonPublic)!;
var collectionType = extractor.GetType("Nethermind.LeanCIL.MetadataSlices+Collection", throwOnError: true)!;
var directory = At("artifacts/MetadataAssemblyIndexes");
Directory.CreateDirectory(directory);

byte[] Image(string name, int version = 1)
{
    using var assembly = AssemblyDefinition.CreateAssembly(new(name, new(version, 0)), name, ModuleKind.Dll);
    using var stream = new MemoryStream();
    assembly.Write(stream);
    return stream.ToArray();
}

var selected = Image("Assembly0", 9);
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
        [selected, "test", array, null], null)!;
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
    ExpectOutside(() => rejectMismatch(new("Assembly0", new(2, 0))));
    rejectMismatch(new("Unpinned", new(1, 0)));
    var resolver = (IAssemblyResolver)pinned;
    try
    {
        resolver.Resolve(new("Assembly0", new(3, 0)));
        throw new InvalidOperationException("An unmatched assembly version was accepted.");
    }
    catch (InvalidDataException error)
    {
        Require(error.Message.Contains("Pinned: " + modules[0].Assembly.Name.FullName, StringComparison.Ordinal),
            "The first pinned assembly with this simple name changed.");
    }
    Require(resolver.Resolve(modules[^1].Assembly.Name) == modules[^1].Assembly,
        "Pinned resolution returned another module.");
    ExpectOutside(() => resolver.Resolve(new("Unpinned", new(1, 0))));

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
            rejectMismatch(new("Unpinned", new(1, 0)));
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

static void Require(bool condition, string message)
{
    if (!condition) throw new InvalidOperationException(message);
}

static void ExpectOutside(Action action)
{
    try { action(); }
    catch (InvalidDataException) { return; }
    throw new InvalidOperationException("An unpinned module or mismatched reference was accepted.");
}
