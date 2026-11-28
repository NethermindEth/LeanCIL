#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ContractVariants.cs
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include ../scripts/Checking/BatchVerification.cs

using System.Numerics;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/CheckedArithmetic");
Directory.CreateDirectory(root);
var queue = new GeneratedQueue(verification, assembly);
var cases = 0;

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
        claims.Add($"(CIL.Safety.invoke Extracted.program 4 0 [.scalar (.i{width} {left}), .scalar (.i{width} {right})] CIL.Safety.Memory.empty).map Prod.snd = {resultClaim}");
    }

    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nset_option maxRecDepth 4096\nnamespace ExampleProof\ntheorem correctness :\n" +
        string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩\nend ExampleProof\n");
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {operation.Name} {width}: {claims.Count} runtime comparisons and proofs");
    });
}

queue.Flush();

// The same two inputs distinguish checked addition from the compiled subtraction at either width.
foreach (var width in new[] { 32, 64 })
{
    var methodName = width == 32 ? "Add" : "Add64";
    var selector = width == 32 ? "CheckedArithmetic::Add(uint,uint)" : "CheckedArithmetic::Add64(ulong,ulong)";
    var wrongOutput = Path.Combine(root, width == 32 ? "WrongCheckedAdd" : "WrongCheckedAdd64");
    Directory.CreateDirectory(wrongOutput);
    var wrongDll = Path.Combine(wrongOutput, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.CheckedArithmetic").Methods.Single(m => m.Name == methodName);
        method.Body.Instructions.Single(i => i.OpCode == OpCodes.Add_Ovf_Un).OpCode = OpCodes.Sub;
        module.Write(wrongDll);
    }

    var contract = $$"""
        /-- Every fitting unsigned sum returns its natural-number value and preserves caller memory. -/
        def contract : MethodContract (W{{width}} × W{{width}}) where
          args input := [.scalar (.i{{width}} input.1), .scalar (.i{{width}} input.2)]
          pre input _ := input.1.toNat + input.2.toNat < 2^{{width}}
          footprint _ := []
          post input before after values := after = before ∧
            values = [.scalar (.i{{width}} (BitVec.ofNat {{width}} (input.1.toNat + input.2.toNat)))]
        """;
    var fromExample = width == 32 ? "⟨4, ExampleProof.correctness_framed memory x y fits⟩" :
        "ExampleProof.correctness memory x y fits";
    var positive = $$"""
        /-- The arbitrary-memory invocation theorem supplies the result and frame. -/
        theorem correctness : contract.Holds Extracted.program 0 := by
          rintro ⟨x, y⟩ memory fits
          have returned : ∃ fuel, invoke Extracted.program fuel 0 (contract.args (x, y)) memory =
              .ok (memory, [.scalar (.i{{width}} (BitVec.ofNat {{width}} (x.toNat + y.toNat)))]) :=
            {{fromExample}}
          obtain ⟨fuel, ran⟩ := returned
          exact ⟨fuel, _, ran, Confined.refl _ _, _, rfl, rfl, rfl⟩
        """;
    const string counterexample = """
        /-- Two minus one returns one where the checked addition contract requires three. -/
        theorem correctness : contract.Refuted Extracted.program 0 :=
          .of_return (input := (2, 1)) (initial := Memory.empty) (by dsimp [contract]; decide)
            (rfl : invoke Extracted.program 4 0 (contract.args (2, 1)) Memory.empty = .ok _)
            (by rintro ⟨-, _, rfl, -, wrong⟩; revert wrong; decide)
        """;
    verification.VerifyContractVariant(assembly, "Examples", selector, Path.Combine(root, $"CheckedAdd{width}"),
        wrongDll, selector, wrongOutput, contract, positive, counterexample,
        example: At($"Examples/Proofs/CheckedAdd{width}.lean"));
}
Console.WriteLine($"CheckedArithmetic passed {cases} boundary cases and verified the two incorrect sums.");
