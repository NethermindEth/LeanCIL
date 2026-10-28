#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include NativeShiftCounts.cs

using System.Numerics;
using System.Reflection;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/NativeIntegers");
Directory.CreateDirectory(root);
if (IntPtr.Size != 8) throw new InvalidOperationException("Runtime comparisons require a 64-bit process");
var runtime = Assembly.Load(File.ReadAllBytes(assembly));
var owner = runtime.GetType("Examples.NativeIntegers")!;
using var source = ModuleDefinition.ReadModule(assembly);
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);
if (args is ["--shift-counts"])
{
    QueueNativeShiftCounts(queue, assembly, root);
    queue.Flush();
    return;
}
if (args.Length != 0) throw new ArgumentException("Usage: NativeIntegers.cs [--shift-counts]");

void Prove(string dll, string selector, string name, List<string> claims)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 4096\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact " + (claims.Count == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {name}: {claims.Count} runtime comparisons and proofs");
    });
}

verification.Verify(assembly, "Examples", "NativeIntegers::Add(nint,nint)",
    At("Examples/Proofs/NativeAdd.lean"), Path.Combine(root, "UniversalAdd"));

BigInteger[] Values(Type type) => type == typeof(int) || type == typeof(uint)
    ? [0, 1, 31, 32, 63, 64, 2147483648, 4294967295]
    : [0, 1, 2, 3, 2147483647, 2147483648, 9223372036854775807, 9223372036854775808, 18446744073709551615];

object Box(Type type, BigInteger bits) => type == typeof(int) ? unchecked((int)(uint)bits) :
    type == typeof(uint) ? (uint)bits : type == typeof(nint) ? unchecked((nint)(ulong)bits) : (nuint)(ulong)bits;

BigInteger Bits(object value) => value switch
{
    int x => unchecked((uint)x), uint x => x, nint x => unchecked((ulong)x), nuint x => (ulong)x,
    _ => throw new InvalidOperationException("Unexpected runtime result")
};

// Compiler-generated arithmetic, conversions, calls, locals, fields and byrefs.
foreach (var method in owner.GetMethods(BindingFlags.Public | BindingFlags.Static | BindingFlags.DeclaredOnly))
{
    var definition = source.GetType("Examples.NativeIntegers").Methods.Single(m => m.Name == method.Name);
    var parameters = method.GetParameters();
    var combinations = new List<(List<object> Runtime, List<string> Lean)> { ([], []) };
    foreach (var parameter in parameters)
    {
        var next = new List<(List<object>, List<string>)>();
        var type = parameter.ParameterType;
        foreach (var (actual, lean) in combinations)
        {
            if (type.IsByRef)
            {
                next.Add(([.. actual, Activator.CreateInstance(type.GetElementType()!)!], [.. lean, "Examples.reference"]));
                continue;
            }
            foreach (var bits in Values(type))
                next.Add(([.. actual, Box(type, bits)], [.. lean, $".scalar (.i{(type == typeof(int) || type == typeof(uint) ? 32 : 64)} {bits})"]));
        }
        combinations = next;
    }

    var claims = new List<string>();
    var resultWidth = method.ReturnType == typeof(int) || method.ReturnType == typeof(uint) ? 32 : 64;
    var memory = method.Name == "Fields" ? "{ Examples.caller with allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 1, []⟩, true, []⟩ else none, views := [⟨0, 0, 16, true, true⟩] }" : "Examples.caller";
    foreach (var (actual, lean) in combinations)
    {
        string outcome;
        try
        {
            var result = method.Invoke(null, actual.ToArray())!;
            outcome = $".ok [.scalar (.i{resultWidth} {Bits(result)})]";
        }
        catch (TargetInvocationException error) when (error.InnerException is DivideByZeroException or OverflowException)
        {
            var fault = error.InnerException is DivideByZeroException ? "divideByZero" : "overflow";
            var pc = definition.Body.Instructions.ToList().FindIndex(i => i.OpCode.Code is Code.Div or Code.Div_Un or
                Code.Add_Ovf or Code.Add_Ovf_Un or Code.Conv_Ovf_I4 or Code.Conv_Ovf_U4_Un);
            if (pc < 0) throw new InvalidOperationException("Missing faulting CIL instruction", error);
            outcome = $".error ⟨0, {pc}, .arithmetic .{fault}⟩";
        }
        claims.Add($"(CIL.Safety.invoke Extracted.program 32 0 [{string.Join(", ", lean)}] ({memory})).map Prod.snd = {outcome}");
    }
    Prove(assembly, definition.FullName, method.Name, claims);
}

// Exact mixed native/int32 encodings, in both operand orders. Grouping operations
// behind a switch keeps proof builds small while checking each actual instruction.
var mixedOperations = new[]
{
    OpCodes.Add, OpCodes.Sub, OpCodes.Mul, OpCodes.Div, OpCodes.Div_Un, OpCodes.Rem, OpCodes.Rem_Un,
    OpCodes.Add_Ovf, OpCodes.Add_Ovf_Un, OpCodes.Sub_Ovf, OpCodes.Sub_Ovf_Un, OpCodes.Mul_Ovf, OpCodes.Mul_Ovf_Un,
    OpCodes.And, OpCodes.Or, OpCodes.Xor, OpCodes.Ceq, OpCodes.Clt, OpCodes.Clt_Un, OpCodes.Cgt, OpCodes.Cgt_Un,
    OpCodes.Beq, OpCodes.Blt, OpCodes.Bgt, OpCodes.Ble, OpCodes.Bge
};
var unsignedBranches = new[] { OpCodes.Bne_Un, OpCodes.Blt_Un, OpCodes.Bgt_Un, OpCodes.Ble_Un, OpCodes.Bge_Un };
foreach (var (candidates, scenario, conversion) in new[] {
    (mixedOperations, "Mixed", (OpCode?)null),
    (unsignedBranches, "ExplicitSigned", (OpCode?)OpCodes.Conv_I),
    (unsignedBranches, "ExplicitUnsigned", (OpCode?)OpCodes.Conv_U)
})
foreach (var reverse in new[] { false, true })
foreach (var (operations, group) in candidates.Chunk(6).Select((ops, index) => (ops, index)))
{
    var name = $"{scenario}-{reverse}-{group}";
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    var faultSites = new List<int>();
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = new MethodDefinition("Mixed", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.IntPtr);
        method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
        method.Parameters.Add(new ParameterDefinition(module.TypeSystem.IntPtr));
        method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
        module.GetType("Examples.NativeIntegers").Methods.Add(method);
        var code = method.Body.Instructions;
        var targets = operations.Select(_ => Instruction.Create(reverse ? OpCodes.Ldarg_2 : OpCodes.Ldarg_1)).ToArray();
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(OpCodes.Switch, targets));
        code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
        code.Add(Instruction.Create(OpCodes.Conv_I));
        code.Add(Instruction.Create(OpCodes.Ret));
        foreach (var (operation, index) in operations.Select((op, index) => (op, index)))
        {
            code.Add(targets[index]);
            if (reverse && conversion.HasValue) code.Add(Instruction.Create(conversion.Value));
            code.Add(Instruction.Create(reverse ? OpCodes.Ldarg_1 : OpCodes.Ldarg_2));
            if (!reverse && conversion.HasValue) code.Add(Instruction.Create(conversion.Value));
            faultSites.Add(code.Count);
            if (operation.FlowControl == FlowControl.Cond_Branch)
            {
                var taken = Instruction.Create(OpCodes.Ldc_I4_1);
                var join = Instruction.Create(OpCodes.Conv_I);
                code.Add(Instruction.Create(operation, taken));
                code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
                code.Add(Instruction.Create(OpCodes.Br, join));
                code.Add(taken);
                code.Add(join);
            }
            else
            {
                code.Add(Instruction.Create(operation));
                code.Add(Instruction.Create(OpCodes.Conv_I));
            }
            code.Add(Instruction.Create(OpCodes.Ret));
        }
        selector = method.FullName;
        module.Write(dll);
    }

    var methodInfo = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.NativeIntegers")!.GetMethod("Mixed")!;
    var claims = new List<string>();
    foreach (var index in Enumerable.Range(0, operations.Length))
    foreach (var wide in new ulong[] { 0, 1, 9223372036854775807, 9223372036854775808, ulong.MaxValue })
    foreach (var narrow in new uint[] { 0, 1, int.MaxValue, 2147483648, uint.MaxValue })
    {
        string outcome;
        try
        {
            var result = methodInfo.Invoke(null, [index, unchecked((nint)wide), unchecked((int)narrow)])!;
            outcome = $".ok [.scalar (.i64 {Bits(result)})]";
        }
        catch (TargetInvocationException error) when (error.InnerException is DivideByZeroException or OverflowException)
        {
            var fault = error.InnerException is DivideByZeroException ? "divideByZero" : "overflow";
            outcome = $".error ⟨0, {faultSites[index]}, .arithmetic .{fault}⟩";
        }
        claims.Add($"(CIL.Safety.invoke Extracted.program 12 0 [.scalar (.i32 {index}), .scalar (.i64 {wide}), .scalar (.i32 {narrow})] Examples.empty).map Prod.snd = {outcome}");
    }
    Prove(dll, selector, name, claims);
}
QueueNativeShiftCounts(queue, assembly, root);
queue.Flush();

// No argument-only exception: inlining/constant propagation can change whether
// the JIT sees ldc.i4, even when this method itself loads an argument or local.
// Cover every short/long encoding, both orders, and negative constant provenance.
var branchRejections = 0;
foreach (var branch in unsignedBranches.Concat(new[] {
    OpCodes.Bne_Un_S, OpCodes.Blt_Un_S, OpCodes.Bgt_Un_S, OpCodes.Ble_Un_S, OpCodes.Bge_Un_S }))
foreach (var reverse in new[] { false, true })
foreach (var operandSource in new[] { "argument", "constant", "local" })
{
    var output = Path.Combine(root, $"Reject-{branch.Name}-{reverse}-{operandSource}");
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = new MethodDefinition("AmbiguousBranch", Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static,
        module.TypeSystem.Int32);
    method.Parameters.Add(new ParameterDefinition(module.TypeSystem.IntPtr));
    method.Parameters.Add(new ParameterDefinition(module.TypeSystem.Int32));
    module.GetType("Examples.NativeIntegers").Methods.Add(method);
    var code = method.Body.Instructions;
    if (operandSource == "local")
    {
        method.Body.Variables.Add(new VariableDefinition(module.TypeSystem.Int32));
        code.Add(Instruction.Create(OpCodes.Ldc_I4_M1));
        code.Add(Instruction.Create(OpCodes.Stloc_0));
    }
    var narrow = operandSource switch {
        "constant" => OpCodes.Ldc_I4_M1, "local" => OpCodes.Ldloc_0, _ => OpCodes.Ldarg_1
    };
    code.Add(Instruction.Create(reverse ? narrow : OpCodes.Ldarg_0));
    code.Add(Instruction.Create(reverse ? OpCodes.Ldarg_0 : narrow));
    var taken = Instruction.Create(OpCodes.Ldc_I4_1);
    code.Add(Instruction.Create(branch, taken));
    code.Add(Instruction.Create(OpCodes.Ldc_I4_0));
    code.Add(Instruction.Create(OpCodes.Ret));
    code.Add(taken);
    code.Add(Instruction.Create(OpCodes.Ret));
    module.Write(dll);
    var rejection = Execute(Extract("extract", dll, "Examples", method.FullName, output));
    if (rejection.Code == 0 || !rejection.Output.Contains("Unsupported mixed native/int32 unsigned branch; insert explicit conv.i or conv.u"))
        throw new InvalidOperationException("Ambiguous unsigned branch accepted: " + rejection.Output);
    branchRejections++;
}
Console.WriteLine($"PASS {branchRejections} mixed unsigned branch rejections; explicit conv.i/conv.u cases proved above");

// Native metadata must not weaken target, layout or runtime identity checks.
foreach (var mutation in new[] { "required32", "scope", "field", "mixed64" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = module.GetType("Examples.NativeIntegers").Methods.Single(m => m.Name == (mutation == "field" ? "Fields" : "Add"));
    if (mutation == "required32") module.Attributes |= ModuleAttributes.Required32Bit;
    if (mutation == "scope")
    {
        var fake = new AssemblyNameReference("Fake.Runtime", new Version(10, 0, 0, 0));
        module.AssemblyReferences.Add(fake);
        method.Parameters[0].ParameterType = new TypeReference("System", "IntPtr", module, fake, true);
    }
    if (mutation == "field") module.GetType("Examples.NativePair").Fields[1].Offset = 9;
    if (mutation == "mixed64") method.Parameters[0].ParameterType = module.TypeSystem.Int64;
    module.Write(dll);
    var result = Execute(Extract("extract", dll, "Examples", method.FullName, output));
    var marker = mutation switch
    {
        "required32" => "Unsupported assembly identity", "scope" => "Unsupported type identity",
        "field" => "Invalid field layout", _ => "Unsupported native operand mixture"
    };
    if (result.Code == 0 || !result.Output.Contains(marker))
        throw new InvalidOperationException("Incorrect native metadata rejection: " + result.Output);
    Console.WriteLine("PASS rejection: " + mutation);
}

// sizeof must follow an admitted profile, never the extractor host's pointer size.
using var identity = JsonDocument.Parse(File.ReadAllText(Path.Combine(root, "UniversalAdd", "identity.json")));
var profile = identity.RootElement.GetProperty("profile").EnumerateObject()
    .ToDictionary(p => JsonNamingPolicy.CamelCase.ConvertName(p.Name), p => p.Value.Clone());
profile["nativeWidth"] = JsonSerializer.SerializeToElement(32);
var profilePath = Path.Combine(root, "invalid32.json");
File.WriteAllText(profilePath, JsonSerializer.Serialize(profile));
var invalidProfile = Execute(Extract("extract", assembly, "Examples", "NativeIntegers::SignedSize()",
    Path.Combine(root, "Reject-profile32"), "@" + profilePath));
if (invalidProfile.Code == 0 || !invalidProfile.Output.Contains("Invalid execution profile"))
    throw new InvalidOperationException("Native sizeof accepted an unsupported profile: " + invalidProfile.Output);

Console.WriteLine($"Native integers passed: {cases} cases and five metadata/profile rejections.");
