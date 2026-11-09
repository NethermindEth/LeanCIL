#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

// Framework argument guards as checked runtime contracts: proofs that each raises its exception exactly when its .NET
// condition holds, a proof that fails once the guard is swapped, and named rejection of uncatalogued guard overloads.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Guards");
Directory.CreateDirectory(root);

foreach (var (proof, entry) in new[]
{
    ("GuardCount", "Guards::Count(System.Int32)"),
    ("GuardIndex", "Guards::Index(System.UInt32,System.UInt32)"),
    ("GuardRequired", "Guards::Required(System.String)")
})
{
    verification.Verify(assembly, "Examples", entry, At($"Examples/Proofs/{proof}.lean"), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

// The guard method decides the proof: with ThrowIfNegativeOrZero, zero raises and GuardCount no longer holds.
var swapped = Mutate("swapped", "Count",
    (module, call) => Guard(module, call, "ThrowIfNegativeOrZero", module.TypeSystem.Int32));
var refuted = Execute(["dotnet", ExtractorPath, "extract", swapped, "Examples.Guards::Count(System.Int32)",
    Path.Combine(root, "Reject-swapped")]);
if (refuted.Code != 0)
    throw new InvalidOperationException("The swapped guard should extract\n" + refuted.Output);
var checkedSwap = Execute(["dotnet", ExtractorPath, "verify", Path.Combine(root, "Reject-swapped"), "--proof",
    At("Examples/Proofs/GuardCount.lean")]);
if (checkedSwap.Code == 0 ||
    !checkedSwap.Output.Contains("Lean could not prove the selected theorem", StringComparison.Ordinal))
    throw new InvalidOperationException("GuardCount must fail for ThrowIfNegativeOrZero\n" + checkedSwap.Output);
Console.WriteLine("PASS swapped guard refutes GuardCount");

// Floating-point and pointer guards are not modeled: NaN and pointer comparison are outside the integer contract.
foreach (var (name, method, rewrite, expected) in
    new (string, string, Func<ModuleDefinition, Instruction, MethodReference>, string)[]
{
    ("double", "Count", (module, call) => Guard(module, call, "ThrowIfNegative", module.TypeSystem.Double),
        "System.Void System.ArgumentOutOfRangeException::ThrowIfNegative<System.Double>(!!0,System.String)"),
    ("pointer", "Required", (module, call) => NullGuard(module, call),
        "System.Void System.ArgumentNullException::ThrowIfNull(System.Void*,System.String)")
})
{
    var dll = Mutate(name, method, rewrite);
    var output = Path.GetDirectoryName(dll)!;
    var selector = method == "Count"
        ? "Examples.Guards::Count(System.Int32)"
        : "Examples.Guards::Required(System.String)";
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, selector, Path.Combine(output, "out")]);
    if (result.Code != 1 || !result.Output.Replace("\r\n", "\n").Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException($"Incorrect guard rejection: {name}\n{result.Output}");
    Console.WriteLine($"PASS guard rejection: {name}");
}
Console.WriteLine(
    "PASS guards: integer and null guards raise exactly their exceptions; other overloads rejected by name");

string Mutate(string name, string method, Func<ModuleDefinition, Instruction, MethodReference> rewrite)
{
    var output = Path.Combine(root, "Mutant-" + name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var body = module.GetType("Examples.Guards").Methods.Single(candidate => candidate.Name == method).Body;
    var call = body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Call);
    call.Operand = rewrite(module, call);
    module.Write(dll);
    return dll;
}

// The same guard owner with another method name and type argument.
static MethodReference Guard(ModuleDefinition module, Instruction call, string name, TypeReference argument)
{
    var original = ((GenericInstanceMethod)call.Operand).ElementMethod;
    var guard = new MethodReference(name, module.TypeSystem.Void, original.DeclaringType);
    guard.GenericParameters.Add(new GenericParameter("T", guard));
    guard.Parameters.Add(new ParameterDefinition(guard.GenericParameters[0]));
    guard.Parameters.Add(new ParameterDefinition(module.TypeSystem.String));
    var instance = new GenericInstanceMethod(guard);
    instance.GenericArguments.Add(argument);
    return instance;
}

// ThrowIfNull's pointer overload, which tests an unmanaged address.
static MethodReference NullGuard(ModuleDefinition module, Instruction call)
{
    var original = (MethodReference)call.Operand;
    var guard = new MethodReference("ThrowIfNull", module.TypeSystem.Void, original.DeclaringType);
    guard.Parameters.Add(new ParameterDefinition(new PointerType(module.TypeSystem.Void)));
    guard.Parameters.Add(new ParameterDefinition(module.TypeSystem.String));
    return guard;
}
