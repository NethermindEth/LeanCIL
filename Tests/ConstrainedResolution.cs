#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PinnedMetadata.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

var extractor = Assembly.LoadFrom(ExtractorPath);
var resolve = extractor.GetType("Nethermind.LeanCIL.ConstrainedCalls", throwOnError: true)!
    .GetMethod("Resolve", BindingFlags.Static | BindingFlags.NonPublic)!;
const BindingFlags Internal = BindingFlags.Instance | BindingFlags.Public | BindingFlags.NonPublic;
var pinnedType = extractor.GetType("Nethermind.LeanCIL.PinnedAssemblies", throwOnError: true)!;
PinnedMetadata Pinned() => new(extractor, At("Examples/Assembly/bin/Examples.dll"));

object Index(MethodDefinition method) => Activator.CreateInstance(
    extractor.GetType("Nethermind.LeanCIL.InstructionIndex", true)!,
    BindingFlags.Instance | BindingFlags.NonPublic, null, [method], null)!;

foreach (var (receiverName, methodName) in new[]
{
    ("CounterValue", "Read"),
    ("ExplicitCounterValue", "Examples.ICounterValue.Read")
})
{
    using var pinned = Pinned();
    var module = pinned.Module;
    var method = module.GetType("Examples.ConstrainedCalls").Methods.Single(method => method.Name == "Read");
    var receiver = module.GetType("Examples." + receiverName);
    var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Constrained);
    prefix.Operand = receiver;
    var resolution = resolve.Invoke(null, [method, prefix.Next, Index(method), "scalar"])!;
    var target = (MethodDefinition)resolution.GetType().GetProperty("Target")!.GetValue(resolution)!;
    if (target.DeclaringType != receiver || target.Name != methodName)
        throw new Exception("Incorrect concrete constrained implementation: " + target.FullName);
    Console.WriteLine("PASS constrained resolution: " + receiverName);
}

foreach (var (mutation, marker) in new[]
{
    ("branch", "Branch bypasses constrained receiver prefix"),
    ("switch", "Branch bypasses constrained receiver prefix"),
    ("reference", "concrete struct of an extracted assembly"),
    ("missing", "no unique struct implementation"),
    ("ordinary", "adjacent concrete constrained receiver"),
    ("open-direct-owner", "Unsupported constrained method owner")
})
{
    using var pinned = Pinned();
    var module = pinned.Module;
    var method = module.GetType("Examples.ConstrainedCalls").Methods.Single(method => method.Name == "Read");
    var receiver = module.GetType("Examples.CounterValue");
    var prefix = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Constrained);
    var call = prefix.Next;
    prefix.Operand = receiver;
    switch (mutation)
    {
        case "branch":
            method.Body.GetILProcessor().InsertBefore(prefix, Instruction.Create(OpCodes.Br, call));
            break;
        case "switch":
            method.Body.GetILProcessor().InsertBefore(prefix, Instruction.Create(OpCodes.Switch, [call, call]));
            break;
        case "reference": prefix.Operand = module.GetType("Examples.ConstrainedCalls"); break;
        case "missing": receiver.Methods.Remove(receiver.Methods.Single(method => method.Name == "Read")); break;
        case "ordinary": prefix.OpCode = OpCodes.Nop; prefix.Operand = null; break;
        case "open-direct-owner":
            var definition = module.GetType("Examples.GenericCounterValue`1");
            var generic = new GenericInstanceType(definition);
            generic.GenericArguments.Add(module.TypeSystem.Int32);
            prefix.Operand = generic;
            call.Operand = definition.Methods.Single(member => member.Name == "Read" && !member.HasGenericParameters);
            break;
    }
    try
    {
        resolve.Invoke(null, [method, call, Index(method), "scalar"]);
        throw new Exception("Constrained resolver accepted " + mutation);
    }
    catch (TargetInvocationException error) when
        (error.InnerException is InvalidDataException rejected && rejected.Message.Contains(marker, StringComparison.Ordinal))
    {
        Console.WriteLine("PASS constrained rejection: " + mutation);
    }
}

var runtimeType = extractor.GetType("Nethermind.LeanCIL.RuntimeModels", throwOnError: true)!;
var exactScope = runtimeType.GetMethod("ExactScope", BindingFlags.Static | BindingFlags.NonPublic)!;
var platformType = extractor.GetType("Nethermind.LeanCIL.PlatformAssemblies", throwOnError: true)!;
var platform = platformType.GetField("SystemRuntime", BindingFlags.Static | BindingFlags.NonPublic)!.GetValue(null);
foreach (bool forged in new[] { false, true })
{
    using var fixture = Pinned();
    var pinned = fixture.Context;
    using var source = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll"));
    source.Assembly.Name.Name = "IdentityOnly";
    if (forged) source.AssemblyReferences.Single(reference => reference.Name == "System.Runtime").Version = new(1, 0);
    using var stream = new MemoryStream();
    source.Write(stream);
    byte[] bytes = stream.ToArray();
    using var imported = ModuleDefinition.ReadModule(new MemoryStream(bytes));
    var parent = imported.GetType("Examples.CounterValue").BaseType;
    ExpectRejected(() => exactScope.Invoke(null, [parent, platform]));
    pinnedType.GetMethod("RegisterIdentityImage", Internal)!.Invoke(pinned, [imported, bytes]);
    // Cecil's display fields cannot replace the image's assembly identity columns.
    imported.AssemblyReferences.Single(reference => reference.Name == "System.Runtime").Version = new(11, 0, 0, 0);
    if ((bool)exactScope.Invoke(null, [parent, platform])! == forged)
        throw new Exception("Imported identity did not match its raw assembly row.");
    if ((bool)pinnedType.GetMethod("Contains", Internal)!.Invoke(pinned, [imported])! ||
        pinnedType.GetMethod("ModuleOf", Internal)!
            .Invoke(pinned, [imported.GetType("Examples.CounterValue")]) is not null)
        throw new Exception("Metadata-only image became an executable pin.");
    var method = imported.GetType("Examples.CounterValue").Methods.Single(member => member.Name == "Read");
    ExpectRejected(() => pinnedType.GetMethod("Body", Internal)!.Invoke(pinned, [method]));
    ExpectRejected(() => pinnedType.GetMethod("Metadata", Internal)!.Invoke(pinned, [imported]));
    ExpectRejected(() => pinnedType.GetMethod("Original", Internal)!.Invoke(pinned, [imported]));
    ExpectRejected(() => pinnedType.GetMethod("Index", Internal)!.Invoke(pinned, [imported]));
    ExpectRejected(() => ((IAssemblyResolver)pinned).Resolve(imported.Assembly.Name));
    Console.WriteLine("PASS metadata-only identity and executable isolation: forged=" + forged);
}

double IdentityLookupCost(int count)
{
    using var fixture = Pinned();
    var register = pinnedType.GetMethod("RegisterIdentityImage", Internal)!
        .CreateDelegate<Action<ModuleDefinition, byte[]>>(fixture.Context);
    var lookup = pinnedType.GetMethod("IdentityMetadata", Internal)!
        .CreateDelegate<Func<ModuleDefinition, object>>(fixture.Context);
    byte[] bytes = File.ReadAllBytes(At("Examples/Assembly/bin/Examples.dll"));
    var modules = new List<ModuleDefinition>();
    try
    {
        for (int index = 0; index < count; index++)
        {
            var module = ModuleDefinition.ReadModule(new MemoryStream(bytes));
            modules.Add(module);
            register(module, bytes);
        }
        var samples = new List<double>();
        for (int sample = 0; sample < 7; sample++)
        {
            long start = System.Diagnostics.Stopwatch.GetTimestamp();
            for (int repeat = 0; repeat < 128; repeat++)
                foreach (var module in modules)
                    if (!ReferenceEquals(lookup(module), lookup(module)))
                        throw new Exception("Import metadata was not cached by module.");
            samples.Add(System.Diagnostics.Stopwatch.GetElapsedTime(start).TotalMilliseconds);
        }
        samples.Sort();
        Console.WriteLine($"{count} imported modules, 128 identity lookup passes: {samples[3]:F3} ms");
        return samples[3];
    }
    finally { foreach (var module in modules) module.Dispose(); }
}

// A lookup that scans the registered modules costs 256 times as much at 16 times the modules; a keyed
// lookup stays within the factor of 4 that cache misses add per lookup on a loaded machine.
double smallest = IdentityLookupCost(64);
IdentityLookupCost(256);
double largest = IdentityLookupCost(1024);
if (largest > smallest * 16 * 4 + 1)
    throw new Exception("Import identity lookup cost grew faster than module count.");

static void ExpectRejected(Action action)
{
    try { action(); }
    catch (InvalidDataException) { return; }
    catch (TargetInvocationException error) when (error.InnerException is InvalidDataException) { return; }
    throw new Exception("Unregistered identity or imported executable image was accepted.");
}
