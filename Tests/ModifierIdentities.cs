#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include PinnedMetadata.cs

using System.Collections;
using System.Diagnostics;
using System.Reflection;
using Mono.Cecil;

var root = Path.GetFullPath("artifacts/ModifierIdentities");
Directory.CreateDirectory(root);
var extractor = Assembly.LoadFrom(Path.GetFullPath("Extractor/bin/Nethermind.LeanCIL.dll"));
const BindingFlags Static = BindingFlags.Static | BindingFlags.NonPublic;
const BindingFlags Instance = BindingFlags.Instance | BindingFlags.NonPublic;
var inUnwrap = extractor.GetType("Nethermind.LeanCIL.InReferences", true)!
    .GetMethod("Unwrap", Static)!.CreateDelegate<Func<TypeReference, ByReferenceType?>>();
var initUnwrap = extractor.GetType("Nethermind.LeanCIL.InitAccessors", true)!
    .GetMethod("Unwrap", Static)!.CreateDelegate<Func<TypeReference, TypeReference?>>();

void Require(bool condition, string message)
{
    if (!condition) throw new Exception(message);
}

AssemblyNameReference Runtime(ModuleDefinition module, int version = 11)
{
    var runtime = new AssemblyNameReference("System.Runtime", new(version, 0, 0, 0))
    {
        PublicKeyToken = Convert.FromHexString("b03f5f7f11d50a3a")
    };
    module.AssemblyReferences.Add(runtime);
    return runtime;
}

void Reject(Func<bool> action)
{
    try { action(); }
    catch (InvalidDataException) { return; }
    throw new Exception("Missing or malformed provenance was accepted");
}

void CheckMarkers(bool initialization)
{
    string space = initialization ? "System.Runtime.CompilerServices" : "System.Runtime.InteropServices";
    string name = initialization ? "IsExternalInit" : "InAttribute";
    string path = Path.Combine(root, initialization ? "Init.dll" : "In.dll");
    using (var assembly = AssemblyDefinition.CreateAssembly(new("Modifiers", new(1, 0)),
        "Modifiers", ModuleKind.Dll))
    {
        var module = assembly.MainModule;
        var runtime = Runtime(module);
        var owner = new TypeDefinition("Fixture", "Owner", Mono.Cecil.TypeAttributes.Public);
        module.Types.Add(owner);
        TypeReference element = initialization ? module.TypeSystem.Void : new ByReferenceType(module.TypeSystem.Int32);
        void Field(string label, TypeReference marker, TypeReference? shape = null) =>
            owner.Fields.Add(new(label, Mono.Cecil.FieldAttributes.Public,
                new RequiredModifierType(marker, shape ?? element)));
        var genuine = new TypeReference(space, name, module, runtime);
        Field("Genuine", genuine);
        Field("Flattened", new TypeReference("", space + "." + name, module, runtime));
        Field("WrongVersion", new TypeReference(space, name, module, Runtime(module, 9)));
        var foreign = new AssemblyNameReference("Other", new(1, 0));
        module.AssemblyReferences.Add(foreign);
        Field("Foreign", new TypeReference(space, name, module, foreign));
        Field("NestedRef", new TypeReference(space, name, module, runtime)
        {
            DeclaringType = new TypeReference("Fixture", "Outer", module, runtime)
        });
        var local = new TypeDefinition(space, name, Mono.Cecil.TypeAttributes.Public);
        module.Types.Add(local);
        Field("Local", local);
        var nested = new TypeDefinition(space, name, Mono.Cecil.TypeAttributes.NestedPublic);
        owner.NestedTypes.Add(nested);
        Field("NestedDef", nested);
        Field("WrongShape", genuine, module.TypeSystem.Int32);
        owner.Fields.Add(new("Optional", Mono.Cecil.FieldAttributes.Public,
            new OptionalModifierType(genuine, element)));
        if (!initialization)
            Field("InnerModifier", genuine,
                new ByReferenceType(new OptionalModifierType(genuine, module.TypeSystem.Int32)));
        assembly.Write(path);
    }
    TypeReference escaped;
    using (var pinned = new PinnedMetadata(extractor, path))
    {
        bool Accepted(TypeReference type) =>
            initialization ? initUnwrap(type) is not null : inUnwrap(type) is not null;
        var fields = pinned.Module.GetType("Fixture.Owner").Fields;
        foreach (var field in fields)
        {
            bool expected = field.Name == "Genuine" || initialization &&
                field.Name is "Local" or "WrongVersion" or "Foreign";
            bool accepted = Accepted(field.FieldType);
            Require(accepted == expected, $"{name}: {field.Name} accepted={accepted}, expected={expected}");
        }
        escaped = fields[0].FieldType;
        var genuine = ((RequiredModifierType)escaped).ModifierType;
        genuine.Namespace = "Mutated";
        genuine.Name = "Unrelated";
        genuine.Scope = pinned.Module;
        Require(Accepted(escaped), "Mutable name or scope changed the genuine raw marker identity");
        var collisionType = fields.Single(field => field.Name == "Flattened").FieldType;
        var collision = ((RequiredModifierType)collisionType).ModifierType;
        collision.Namespace = space;
        collision.Name = name;
        collision.Scope = pinned.Module.AssemblyReferences.First(reference => reference.Name == "System.Runtime");
        Require(!Accepted(collisionType), "Mutable display fields supplied missing raw identity");
        var token = genuine.MetadataToken;
        foreach (uint invalid in new uint[] { 0x01000000, 0x01ffffff, 0x06000001 })
        {
            genuine.MetadataToken = new MetadataToken(invalid);
            Reject(() => Accepted(escaped));
        }
        genuine.MetadataToken = token;
    }
    Reject(() => initialization ? initUnwrap(escaped) is not null : inUnwrap(escaped) is not null);
    Console.WriteLine($"PASS {name}: raw columns, scopes, nesting, shapes, mutations and provenance");
}

CheckMarkers(false);
CheckMarkers(true);

(long Allocated, double Milliseconds) MeasureRows(int count, int nameLength)
{
    string path = Path.Combine(root, $"Rows-{count}-{nameLength}.dll");
    using (var assembly = AssemblyDefinition.CreateAssembly(new("Rows", new(1, 0)), "Rows", ModuleKind.Dll))
    {
        var module = assembly.MainModule;
        var runtime = Runtime(module);
        var owner = new TypeDefinition("Fixture", "Owner", Mono.Cecil.TypeAttributes.Public);
        module.Types.Add(owner);
        for (int index = 0; index < count; index++)
        {
            var marker = new TypeReference("Fixture", new string('X', nameLength) + index, module, runtime);
            owner.Fields.Add(new("F" + index, Mono.Cecil.FieldAttributes.Public,
                new RequiredModifierType(marker, module.TypeSystem.Void)));
        }
        assembly.Write(path);
    }
    using var pinned = new PinnedMetadata(extractor, path);
    var metadataMethod = pinned.Context.GetType().GetMethod("IdentityMetadata", Instance)!;
    object metadata = metadataMethod.Invoke(pinned.Context, [pinned.Module])!;
    var query = metadata.GetType().GetMethod("TopLevelTypeName", Instance)!
        .CreateDelegate<Func<uint, object?>>(metadata);
    var cache = (IDictionary)metadata.GetType().GetField("typeNames", Instance)!.GetValue(metadata)!;
    uint[] tokens = pinned.Module.GetType("Fixture.Owner").Fields
        .Select(field => ((RequiredModifierType)field.FieldType).ModifierType.MetadataToken.ToUInt32()).ToArray();
    var timings = new double[5];
    long allocated = 0;
    object?[] rows = new object?[count];
    for (int sample = 0; sample < timings.Length; sample++)
    {
        cache.Clear();
        long start = GC.GetAllocatedBytesForCurrentThread();
        long started = Stopwatch.GetTimestamp();
        for (int index = 0; index < count; index++) rows[index] = query(tokens[index]);
        timings[sample] = Stopwatch.GetElapsedTime(started).TotalMilliseconds;
        allocated = Math.Max(allocated, GC.GetAllocatedBytesForCurrentThread() - start);
    }
    Array.Sort(timings);
    Require(cache.Count == count, "Each raw row must have exactly one cache entry");
    long repeatStart = GC.GetAllocatedBytesForCurrentThread();
    for (int repeat = 0; repeat < 16; repeat++)
        for (int index = 0; index < count; index++)
            Require(ReferenceEquals(query(tokens[index]), rows[index]), "Repeated query decoded another row");
    long repeatAllocated = GC.GetAllocatedBytesForCurrentThread() - repeatStart;
    Require(repeatAllocated < 1024, "Repeated row queries allocate metadata names");
    Require(cache.Count == count, "Repeated row queries grew the cache");
    Console.WriteLine($"Rows={count}, name bytes={nameLength}, allocated={allocated}, " +
        $"cached allocated={repeatAllocated}, median decode ms={timings[2]:F3}");
    return (allocated, timings[2]);
}

MeasureRows(16, 16);
foreach (int nameLength in new[] { 32, 512 })
{
    (long Allocated, double Milliseconds) previous = default;
    foreach (int count in new[] { 256, 1024, 4096 })
    {
        var measurement = MeasureRows(count, nameLength);
        Require(previous.Allocated == 0 || measurement.Allocated <= previous.Allocated * 5 + 16384,
            "Raw row allocations grew superlinearly");
        previous = measurement;
    }
}
