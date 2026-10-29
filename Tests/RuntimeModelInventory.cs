#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include CompilerToolchain.cs
using System.Reflection;
using System.Text.Json;
using Mono.Cecil;

if (args is not ([] or ["--update"])) throw new ArgumentException("Usage: RuntimeModelInventory.cs [--update]");
var extractor = Assembly.LoadFrom(ExtractorPath);
var flags = BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic;
var translate = extractor.GetType("Nethermind.LeanCIL.RuntimeModels", true)!.GetMethod("Translate", flags)!;
var select = extractor.GetType("Nethermind.LeanCIL.FeatureProfile", true)!.GetMethod("Select", flags)!;
var profiles = new[] { "scalar", "x64-v4", "arm64-advsimd" }.Select(name => select.Invoke(null, [name])).ToArray();
var toolchain = RestoreCompilerToolchain();
using var probe = ModuleDefinition.CreateModule("RuntimeModelInventory", ModuleKind.Dll);
var admitted = new SortedDictionary<string, SortedSet<string>>(StringComparer.Ordinal);
var instances = new SortedSet<string>(StringComparer.Ordinal);
foreach (var assembly in new[] { "System.Runtime", "System.Memory", "System.Runtime.Intrinsics" })
{
    using var reference = ModuleDefinition.ReadModule(Path.Combine(toolchain.References, assembly + ".dll"));
    var runtime = AssemblyNameReference.Parse(
        "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a");
    var elements = new[] { "Byte", "SByte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64",
        "IntPtr", "UIntPtr", "Boolean", "Char", "Single", "Double" }
        .Select(name => new TypeReference("System", name, probe, runtime, true)).ToArray();
    foreach (var type in reference.GetTypes())
    foreach (var definition in type.Methods.Where(method => method.IsPublic && method.GenericParameters.Count <= 2))
    {
        if (type.GenericParameters.Count > 1) continue;
        foreach (var owner in Arguments(type.HasGenericParameters, elements))
        foreach (var first in Arguments(definition.HasGenericParameters, elements))
        foreach (var second in Arguments(definition.GenericParameters.Count == 2, elements))
        {
            MethodReference method = probe.ImportReference(definition);
            foreach (var parameter in method.GenericParameters) parameter.Name = "!!" + parameter.Position;
            foreach (var parameter in method.DeclaringType.GenericParameters) parameter.Name = "!" + parameter.Position;
            if (owner is not null)
            {
                var closed = new GenericInstanceType(method.DeclaringType);
                closed.GenericArguments.Add(owner);
                method.DeclaringType = closed;
            }
            if (first is not null)
            {
                var generic = new GenericInstanceMethod(method);
                generic.GenericArguments.Add(first);
                if (second is not null) generic.GenericArguments.Add(second);
                method = generic;
            }
            foreach (var profile in profiles)
            {
                string? operation;
                try { operation = (string?)translate.Invoke(null, [method, profile]); }
                catch (TargetInvocationException exception) when (exception.InnerException is
                    InvalidDataException or NotSupportedException or AssemblyResolutionException) { continue; }
                if (operation is null) continue;
                if (!admitted.TryGetValue(type.FullName, out var definitions))
                    admitted.Add(type.FullName, definitions = new(StringComparer.Ordinal));
                definitions.Add(assembly + "::" + definition.FullName);
                instances.Add(assembly + "::" + method.FullName);
            }
        }
    }
}
var entries = admitted.Values.SelectMany(values => values).Order(StringComparer.Ordinal).ToArray();
var baseline = At("Tests/RuntimeModelInventory.txt");
var output = At("artifacts/RuntimeModelInventory");
Directory.CreateDirectory(output);
File.WriteAllText(Path.Combine(output, "inventory.json"), JsonSerializer.Serialize(new
{
    referencePack = CorpusReferenceVersion, definitions = entries.Length, instances = instances.Count,
    families = admitted.ToDictionary(pair => pair.Key, pair => pair.Value.Count), entries
}, new JsonSerializerOptions { WriteIndented = true }));
if (args is ["--update"]) File.WriteAllLines(baseline, entries);
var expected = File.ReadAllLines(baseline);
if (!expected.SequenceEqual(entries))
    throw new InvalidOperationException("Runtime model catalog changed; review and update its baseline.\n" +
        string.Join('\n', entries.Except(expected).Select(entry => "+ " + entry)
            .Concat(expected.Except(entries).Select(entry => "- " + entry))));
foreach (var (family, definitions) in admitted) Console.WriteLine($"{family}: {definitions.Count}");
Console.WriteLine($"PASS runtime dispatcher catalog: {entries.Length} definitions, {admitted.Count} API families, " +
    $"{instances.Count} admitted closed instances in the fixed primitive domain");

static IEnumerable<TypeReference?> Arguments(bool generic, TypeReference[] elements) =>
    generic ? elements : [null];
