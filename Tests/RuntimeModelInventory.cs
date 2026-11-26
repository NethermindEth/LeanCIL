#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include CompilerToolchain.cs
#:include PinnedMetadata.cs
using System.Reflection;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

if (args is not ([] or ["--update"])) throw new ArgumentException("Usage: RuntimeModelInventory.cs [--update]");
var extractor = Assembly.LoadFrom(ExtractorPath);
var flags = BindingFlags.Static | BindingFlags.Public | BindingFlags.NonPublic;
var callModel = extractor.GetType("Nethermind.LeanCIL.RuntimeModels", true)!.GetMethod("CallModel", flags)!;
var identityImage = extractor.GetType("Nethermind.LeanCIL.RuntimeModels", true)!.GetMethod("IdentityImage", flags)!;
var select = extractor.GetType("Nethermind.LeanCIL.FeatureProfile", true)!.GetMethod("Select", flags)!;
// No built-in declares AES, so each architecture's widest built-in is also probed with its AES flag.
object Declaring(string name, string flag)
{
    var profile = JsonSerializer.SerializeToNode(select.Invoke(null, [name]),
        new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase })!;
    profile["name"] = $"{name}-{flag}";
    profile[flag] = true;
    var path = At($"artifacts/RuntimeModelInventory/{name}-{flag}.json");
    Directory.CreateDirectory(Path.GetDirectoryName(path)!);
    File.WriteAllText(path, profile.ToJsonString());
    return select.Invoke(null, ["@" + path])!;
}
var profiles = new[] { "scalar", "x64-v4", "arm64-advsimd" }.Select(name => select.Invoke(null, [name]))
    .Append(Declaring("x64-v4", "aes")).Append(Declaring("arm64-advsimd", "armAes")).ToArray();
var toolchain = RestoreCompilerToolchain();
var admitted = new SortedDictionary<string, SortedSet<string>>(StringComparer.Ordinal);
var instances = new SortedSet<string>(StringComparer.Ordinal);
var primitiveNames = new[] { "Byte", "SByte", "Int16", "UInt16", "Int32", "UInt32", "Int64", "UInt64",
    "IntPtr", "UIntPtr", "Boolean", "Char", "Single", "Double" };
const int batchSize = 512;
bool checkedMissingContext = false;
int unsupported = 0;
var conventionChecks = new HashSet<string>(StringComparer.Ordinal);
var acceptedConventions = new List<string>();
foreach (var assembly in new[] { "System.Runtime", "System.Memory", "System.Runtime.Intrinsics" })
{
    using var reference = ModuleDefinition.ReadModule(Path.Combine(toolchain.References, assembly + ".dll"));
    var candidates = from type in reference.GetTypes()
        where type.GenericParameters.Count <= 1
        from definition in type.Methods
        where definition.IsPublic && definition.GenericParameters.Count <= 2
        from owner in Arguments(type.HasGenericParameters, primitiveNames)
        from first in Arguments(definition.HasGenericParameters, primitiveNames)
        from second in Arguments(definition.GenericParameters.Count == 2, primitiveNames)
        select (type, definition, owner, first, second);
    foreach (var batch in candidates.Chunk(batchSize))
    {
        using var probe = ModuleDefinition.CreateModule("RuntimeModelInventory", ModuleKind.Dll);
        var runtime = AssemblyNameReference.Parse(
            "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a");
        probe.AssemblyReferences.Add(runtime);
        var carrier = new MethodDefinition("References", Mono.Cecil.MethodAttributes.Static, probe.TypeSystem.Void);
        probe.Types[0].Methods.Add(carrier);
        var elements = primitiveNames.ToDictionary(name => name,
            name => new TypeReference("System", name, probe, runtime, true), StringComparer.Ordinal);
        var labels = new List<(string Family, string Definition, string Instance)>(batch.Length);
        foreach (var (type, definition, owner, first, second) in batch)
        {
            MethodReference method = probe.ImportReference(definition);
            foreach (var parameter in method.GenericParameters) parameter.Name = "!!" + parameter.Position;
            foreach (var parameter in method.DeclaringType.GenericParameters) parameter.Name = "!" + parameter.Position;
            if (owner is not null)
            {
                var closed = new GenericInstanceType(method.DeclaringType);
                closed.GenericArguments.Add(elements[owner]);
                method.DeclaringType = closed;
            }
            if (first is not null)
            {
                var generic = new GenericInstanceMethod(method);
                generic.GenericArguments.Add(elements[first]);
                if (second is not null) generic.GenericArguments.Add(elements[second]);
                method = generic;
            }
            carrier.Body.Instructions.Add(Instruction.Create(OpCodes.Ldtoken, method));
            carrier.Body.Instructions.Add(Instruction.Create(OpCodes.Pop));
            labels.Add((type.FullName, assembly + "::" + definition.FullName, assembly + "::" + method.FullName));
        }
        carrier.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
        var probePath = At("artifacts/RuntimeModelInventory/Probe.dll");
        probe.Write(probePath);
        MethodReference contextProbe;
        using (var pinned = new PinnedMetadata(extractor, probePath))
        {
            var instructions = pinned.Module.Types[0].Methods.Single().Body.Instructions;
            contextProbe = (MethodReference)instructions[0].Operand;
            for (int index = 0; index < labels.Count; index++)
            {
                var method = (MethodReference)instructions[index * 2].Operand;
                var label = labels[index];
                foreach (var profile in profiles)
                {
                    if (!HasPinnedModel(method, profile)) continue;
                    var probeConvention = (method.DeclaringType.GetElementType().FullName, method.Name) is
                        ("System.Object", ".ctor") or ("System.Math", "Min") or
                        ("System.Numerics.BitOperations", "PopCount") or
                        ("System.Buffers.Binary.BinaryPrimitives", "ReverseEndianness") or
                        ("System.Runtime.Intrinsics.Vector128", "CreateScalarUnsafe" or "GetElement") or
                        ("System.Span`1" or "System.ReadOnlySpan`1", "get_Item" or "Slice" or "get_Length" or
                            "get_IsEmpty" or "GetPinnableReference" or "get_Empty" or "op_Implicit");
                    if (probeConvention && conventionChecks.Add(method.Name))
                        CheckConventions(method, profile);
                    if (!admitted.TryGetValue(label.Family, out var definitions))
                        admitted.Add(label.Family, definitions = new(StringComparer.Ordinal));
                    definitions.Add(label.Definition);
                    instances.Add(label.Instance);
                }
            }
        }
        if (!checkedMissingContext)
        {
            try
            {
                HasPinnedModel(contextProbe, profiles[0]);
                throw new InvalidOperationException(
                    "A missing metadata context was recorded as an unsupported method.");
            }
            catch (TargetInvocationException exception) when (exception.InnerException is InvalidDataException
                { Message: "Type identity without a pinned module image" }) { checkedMissingContext = true; }
        }
    }
}
var entries = admitted.Values.SelectMany(values => values).Order(StringComparer.Ordinal).ToArray();
if (conventionChecks.Count != 13 || acceptedConventions.Count != 0)
    throw new InvalidOperationException(
        $"Checked {conventionChecks.Count} names. Accepted conventions: {string.Join(", ", acceptedConventions)}");
if (entries.Length == 0 || instances.Count == 0 || unsupported == 0 || !checkedMissingContext)
    throw new InvalidOperationException("The runtime inventory must exercise admission and unsupported methods.");
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

bool HasPinnedModel(MethodReference method, object? profile)
{
    identityImage.Invoke(null, [method.DeclaringType]);
    try
    {
        if (callModel.Invoke(null, [method, profile]) is true) return true;
    }
    catch (TargetInvocationException exception) when (exception.InnerException is
        InvalidDataException or NotSupportedException or AssemblyResolutionException)
    {
        // The pinned candidate has an unsupported signature or scope.
    }
    catch (TargetInvocationException exception)
    {
        throw new InvalidOperationException("Inventory candidate: " + method.FullName, exception);
    }
    unsupported++;
    return false;
}

void CheckConventions(MethodReference method, object? profile)
{
    var member = method.GetElementMethod();
    var convention = member.CallingConvention;
    var hasThis = member.HasThis;
    foreach (byte header in new byte[] { 0x40, 0x60, 0x01 })
    {
        member.ExplicitThis = (header & 0x40) != 0;
        member.HasThis = (header & 0x20) != 0;
        member.CallingConvention = (MethodCallingConvention)(header & 0x1f);
        if (callModel.Invoke(null, [method, profile]) is true)
            acceptedConventions.Add($"{method.Name} 0x{header:X2}");
    }
    // Keep the generic flag while checking EXPLICITTHIS on a genuine generic MethodSpec.
    member.CallingConvention = convention;
    member.HasThis = hasThis;
    if (method is GenericInstanceMethod)
    {
        member.ExplicitThis = true;
        if (callModel.Invoke(null, [method, profile]) is true)
            acceptedConventions.Add($"{method.Name} ExplicitThis");
    }
    member.ExplicitThis = false;
}

static IEnumerable<string?> Arguments(bool generic, string[] elements) =>
    generic ? elements : new string?[] { null };
