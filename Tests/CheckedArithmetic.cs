#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Numerics;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/CheckedArithmetic");
Directory.CreateDirectory(root);
var cases = 0;

// The universal contracts require no overflow, with no restriction beyond the sum fitting.
foreach (var width in new[] { 32, 64 })
    verification.Verify(assembly, "Examples", width == 32 ? "CheckedArithmetic::Add(uint,uint)" : "CheckedArithmetic::Add64(ulong,ulong)",
        At($"Examples/Proofs/CheckedAdd{width}.lean"), Path.Combine(root, $"CheckedAdd{width}"));

// The checked automation follows extracted instruction lookups, not fixed PCs.
var shiftedOutput = Path.Combine(root, "ShiftedCheckedAdd64");
Directory.CreateDirectory(shiftedOutput);
var shiftedDll = Path.Combine(shiftedOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.CheckedArithmetic").Methods.Single(m => m.Name == "Add64");
    var il = method.Body.GetILProcessor();
    foreach (var instruction in method.Body.Instructions.ToArray())
        il.InsertBefore(instruction, Instruction.Create(OpCodes.Nop));
    module.Write(shiftedDll);
}
verification.Verify(shiftedDll, "Examples", "CheckedArithmetic::Add64(ulong,ulong)",
    At("Examples/Proofs/CheckedAdd64.lean"), shiftedOutput);
Console.WriteLine("PASS checked automation: unchanged arbitrary-memory contract after instruction shifts");

// Execute the exact same emitted CIL in .NET and in the checked Lean semantics.
foreach (var width in new[] { 32, 64 })
foreach (var operation in new[] { OpCodes.Add_Ovf, OpCodes.Add_Ovf_Un, OpCodes.Sub_Ovf, OpCodes.Sub_Ovf_Un, OpCodes.Mul_Ovf, OpCodes.Mul_Ovf_Un })
{
    var output = Path.Combine(root, operation.Name.Replace('.', '_') + width);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.CheckedArithmetic").Methods.Single(m => m.Name == (width == 32 ? "Add" : "Add64"));
        var code = method.Body.Instructions;
        code.Clear();
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(OpCodes.Ldarg_1));
        code.Add(Instruction.Create(operation));
        code.Add(Instruction.Create(OpCodes.Ret));
        selector = method.FullName;
        module.Write(dll);
    }

    var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.CheckedArithmetic")!
        .GetMethod(width == 32 ? "Add" : "Add64")!;
    var modulus = BigInteger.One << width;
    var sign = modulus >> 1;
    var unsignedRoot = BigInteger.One << (width / 2);
    var signedRoot = width == 32 ? 46340L : 3037000499L;
    BigInteger[] values = [0, 1, 2, 3, sign - 1, sign, sign + 1, modulus - 3, modulus - 1,
        unsignedRoot - 1, unsignedRoot, signedRoot, signedRoot + 1];
    var signed = operation == OpCodes.Add_Ovf || operation == OpCodes.Sub_Ovf || operation == OpCodes.Mul_Ovf;
    var claims = new List<string>();

    foreach (var left in values)
    foreach (var right in values)
    {
        var x = signed && left >= sign ? left - modulus : left;
        var y = signed && right >= sign ? right - modulus : right;
        var resultValue = operation.Code switch { Code.Add_Ovf or Code.Add_Ovf_Un => x + y, Code.Sub_Ovf or Code.Sub_Ovf_Un => x - y, _ => x * y };
        var fault = resultValue < (signed ? -sign : 0) || resultValue >= (signed ? sign : modulus) ? "overflow" : null;
        var expected = fault is null ? (resultValue + modulus) % modulus : 0;
        object Box(BigInteger bits) => width == 32 ? (object)(uint)bits : (ulong)bits;

        try
        {
            var result = runtime.Invoke(null, [Box(left), Box(right)]);
            var actual = result is uint word ? new BigInteger(word) : new BigInteger((ulong)result!);
            if (fault is not null || actual != expected)
                throw new InvalidOperationException($"Runtime mismatch: {operation} {width}: {left}, {right}");
        }
        catch (TargetInvocationException error) when (error.InnerException is OverflowException)
        {
            var actual = "overflow";
            if (actual != fault) throw new InvalidOperationException("Unexpected runtime fault", error);
        }

        var resultClaim = fault is null ? $".ok [.scalar (.i{width} {expected})]" : $".error ⟨0, 2, .arithmetic .{fault}⟩";
        claims.Add($"(CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i{width} {left}), .scalar (.i{width} {right})] Examples.empty).map Prod.snd = {resultClaim}");
    }

    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nset_option maxRecDepth 4096\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(dll, "Examples", selector, proof, output);
    cases += claims.Count;
    Console.WriteLine($"PASS {operation.Name} {width}: {claims.Count} runtime comparisons and proofs");
}

// A different actual implementation must not satisfy the same universal contract.
var wrongOutput = Path.Combine(root, "WrongCheckedAdd");
Directory.CreateDirectory(wrongOutput);
var wrongDll = Path.Combine(wrongOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.CheckedArithmetic").Methods.Single(m => m.Name == "Add");
    method.Body.Instructions.Single(i => i.OpCode == OpCodes.Add_Ovf_Un).OpCode = OpCodes.Sub;
    module.Write(wrongDll);
}
var rejected = false;
try
{
    verification.Verify(wrongDll, "Examples", "CheckedArithmetic::Add(uint,uint)",
        At("Examples/Proofs/CheckedAdd32.lean"), wrongOutput);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrongOutput, "verified.json")))
    throw new InvalidOperationException("Incorrect sum accepted");

Console.WriteLine($"CheckedArithmetic passed: {cases} cases; universal contracts passed and incorrect sum rejected.");

var wrong64Output = Path.Combine(root, "WrongCheckedAdd64");
Directory.CreateDirectory(wrong64Output);
var wrong64Dll = Path.Combine(wrong64Output, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.CheckedArithmetic").Methods.Single(m => m.Name == "Add64");
    method.Body.Instructions.Single(i => i.OpCode == OpCodes.Add_Ovf_Un).OpCode = OpCodes.Sub;
    module.Write(wrong64Dll);
}
rejected = false;
try
{
    verification.Verify(wrong64Dll, "Examples", "CheckedArithmetic::Add64(ulong,ulong)",
        At("Examples/Proofs/CheckedAdd64.lean"), wrong64Output);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    rejected = true;
}
if (!rejected || File.Exists(Path.Combine(wrong64Output, "verified.json")))
    throw new InvalidOperationException("Checked automation accepted incorrect addition");
Console.WriteLine("PASS checked automation rejects subtraction under the unchanged universal contract");
