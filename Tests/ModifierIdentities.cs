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

RowFixture PrepareRows(int count, int nameLength)
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
    var pinned = new PinnedMetadata(extractor, path);
    try
    {
        var metadataMethod = pinned.Context.GetType().GetMethod("IdentityMetadata", Instance)!;
        object metadata = metadataMethod.Invoke(pinned.Context, [pinned.Module])!;
        var query = metadata.GetType().GetMethod("TopLevelTypeName", Instance)!
            .CreateDelegate<Func<uint, object?>>(metadata);
        var cache = (IDictionary)metadata.GetType().GetField("typeNames", Instance)!.GetValue(metadata)!;
        uint[] tokens = pinned.Module.GetType("Fixture.Owner").Fields
            .Select(field => ((RequiredModifierType)field.FieldType).ModifierType.MetadataToken.ToUInt32()).ToArray();
        return new(pinned, query, cache, tokens);
    }
    catch
    {
        pinned.Dispose();
        throw;
    }
}

long CheckAllocations(RowFixture fixture)
{
    long start = GC.GetAllocatedBytesForCurrentThread();
    fixture.Pass(cold: true);
    long allocated = GC.GetAllocatedBytesForCurrentThread() - start;
    Require(fixture.Cache.Count == fixture.Tokens.Length, "Each raw row must have exactly one cache entry");
    long repeatStart = GC.GetAllocatedBytesForCurrentThread();
    for (int repeat = 0; repeat < 16; repeat++) fixture.Pass(cold: false);
    long repeatAllocated = GC.GetAllocatedBytesForCurrentThread() - repeatStart;
    Require(repeatAllocated < 1024, "Repeated row queries allocate metadata names");
    Require(fixture.Cache.Count == fixture.Tokens.Length, "Repeated row queries grew the cache");
    Console.WriteLine($"Rows={fixture.Tokens.Length}, allocated={allocated}, cached allocated={repeatAllocated}");
    return allocated;
}

const double StepGrowthLimit = 9;
const double SpanGrowthLimit = 36;

// Crossing from L1 to L2 cache can push one 4x row step past 6x while overall growth stays linear;
// cap both each 4x step and the 16x span so O(N^1.5) and quadratic growth still fail.
bool GrowthAccepted(double[] batches)
{
    for (int index = 1; index < batches.Length; index++)
        if (batches[index] > batches[index - 1] * StepGrowthLimit + 1) return false;
    return batches.Length < 3 || batches[^1] <= batches[0] * SpanGrowthLimit + 1;
}

Require(GrowthAccepted([25, 100, 400]), "Linear batch growth was rejected");
Require(GrowthAccepted([25, 125, 600]), "N log n batch growth was rejected");
Require(GrowthAccepted([34, 210, 540]), "Cache-tier linear batch growth was rejected");
Require(!GrowthAccepted([25, 200, 1600]), "Subquadratic N^1.5 batch growth was accepted");
Require(!GrowthAccepted([25, 400, 6400]), "Quadratic batch growth was accepted");

double Batch(RowFixture fixture, bool cold, int repetitions)
{
    long started = Stopwatch.GetTimestamp();
    for (int repeat = 0; repeat < repetitions; repeat++) fixture.Pass(cold);
    return Stopwatch.GetElapsedTime(started).TotalMilliseconds;
}

void CheckTimings(RowFixture[] fixtures, bool cold, int nameLength)
{
    const int rounds = 9;
    const double minimumBatchMilliseconds = 25;
    // Calibrate each fixture to a comparable ~25ms batch after warm-up so larger fixtures do not run
    // 16x longer wall batches that absorb far more OS preemption or Tier-0 JIT skew.
    int[] repetitions = new int[fixtures.Length];
    for (int index = 0; index < fixtures.Length; index++)
    {
        int count = 1;
        while (Batch(fixtures[index], cold, count) < minimumBatchMilliseconds)
            count = checked(count * 2);
        // Re-check once after warm-up so Tier-1 promotion does not shrink the calibrated batch.
        while (Batch(fixtures[index], cold, count) < minimumBatchMilliseconds)
            count = checked(count * 2);
        repetitions[index] = count;
    }
    GC.Collect();
    double[][] samples = fixtures.Select(_ => new double[rounds]).ToArray();
    for (int round = 0; round < rounds; round++)
        for (int position = 0; position < fixtures.Length; position++)
        {
            int index = round % 2 == 0 ? position : fixtures.Length - 1 - position;
            samples[index][round] = Batch(fixtures[index], cold, repetitions[index]);
        }
    double[] minimumPasses = Enumerable.Range(0, fixtures.Length)
        .Select(index => samples[index].Min() / repetitions[index]).ToArray();
    double[] normalized = minimumPasses.Select(pass => pass * repetitions[0]).ToArray();
    for (int index = 0; index < fixtures.Length; index++)
        Console.WriteLine($"Rows={fixtures[index].Tokens.Length}, name bytes={nameLength}, cold={cold}, " +
            $"passes={repetitions[index]}, minimum batch ms={samples[index].Min():F3}, " +
            $"minimum pass ms={minimumPasses[index]:F6}");
    Require(GrowthAccepted(normalized),
        $"Modifier query CPU growth exceeded {StepGrowthLimit}x/step or {SpanGrowthLimit}x/span: " +
        $"cold={cold}, bytes={nameLength}");
}

foreach (int nameLength in new[] { 32, 512 })
{
    var fixtures = new List<RowFixture>();
    try
    {
        foreach (int count in new[] { 256, 1024, 4096 }) fixtures.Add(PrepareRows(count, nameLength));
        long previous = 0;
        foreach (var fixture in fixtures)
        {
            long allocated = CheckAllocations(fixture);
            Require(previous == 0 || allocated <= previous * 5 + 16384,
                "Raw row allocations grew superlinearly");
            previous = allocated;
        }
        CheckTimings(fixtures.ToArray(), cold: true, nameLength);
        CheckTimings(fixtures.ToArray(), cold: false, nameLength);
    }
    finally
    {
        for (int index = fixtures.Count - 1; index >= 0; index--) fixtures[index].Dispose();
    }
}

/// <summary>One pinned row set with explicit nested-context ownership and retained cache identities.</summary>
sealed class RowFixture(PinnedMetadata pinned, Func<uint, object?> query, IDictionary cache, uint[] tokens)
    : IDisposable
{
    readonly object?[] rows = new object?[tokens.Length];
    internal IDictionary Cache => cache;
    internal uint[] Tokens => tokens;

    internal void Pass(bool cold)
    {
        if (cold)
        {
            cache.Clear();
            Array.Clear(rows);
        }
        for (int index = 0; index < tokens.Length; index++)
        {
            object? row = query(tokens[index]);
            if (cold) rows[index] = row;
            else if (!ReferenceEquals(row, rows[index]))
                throw new Exception("Repeated query decoded another row");
        }
    }

    public void Dispose() => pinned.Dispose();
}
