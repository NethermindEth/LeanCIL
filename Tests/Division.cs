#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ContractVariants.cs
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/BatchVerification.cs

using System.Numerics;
using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Division");
Directory.CreateDirectory(root);
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

verification.Verify(assembly, "Examples", "Division::Quotient64(ulong,ulong)",
    At("Examples/Proofs/Quotient64.lean"), Path.Combine(root, "Quotient64"));

// Execute the exact same emitted CIL in .NET and in the checked Lean semantics.
foreach (var width in new[] { 32, 64 })
foreach (var operation in new[] { OpCodes.Div, OpCodes.Div_Un, OpCodes.Rem, OpCodes.Rem_Un })
{
    var output = Path.Combine(root, operation.Name.Replace('.', '_') + width);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.Division").Methods.Single(m => m.Name == (width == 32 ? "Quotient" : "Quotient64"));
        var code = method.Body.Instructions;
        code.Clear();
        code.Add(Instruction.Create(OpCodes.Ldarg_0));
        code.Add(Instruction.Create(OpCodes.Ldarg_1));
        code.Add(Instruction.Create(operation));
        code.Add(Instruction.Create(OpCodes.Ret));
        selector = method.FullName;
        module.Write(dll);
    }

    var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Division")!
        .GetMethod(width == 32 ? "Quotient" : "Quotient64")!;
    var modulus = BigInteger.One << width;
    var sign = modulus >> 1;
    BigInteger[] values = [0, 1, 2, 3, sign - 1, sign, sign + 1, modulus - 3, modulus - 1];
    var signed = operation == OpCodes.Div || operation == OpCodes.Rem;
    var remainder = operation == OpCodes.Rem || operation == OpCodes.Rem_Un;
    var claims = new List<string>();

    foreach (var left in values)
    foreach (var right in values)
    {
        var x = signed && left >= sign ? left - modulus : left;
        var y = signed && right >= sign ? right - modulus : right;
        var fault = right == 0 ? "divideByZero" : signed && x == -sign && y == -1 ? "overflow" : null;
        var expected = fault is null ? ((remainder ? x % y : x / y) + modulus) % modulus : 0;
        object Box(BigInteger bits) => width == 32 ? (object)(uint)bits : (ulong)bits;

        try
        {
            var result = runtime.Invoke(null, [Box(left), Box(right)]);
            var actual = result is uint word ? new BigInteger(word) : new BigInteger((ulong)result!);
            if (fault is not null || actual != expected)
                throw new InvalidOperationException($"Runtime mismatch: {operation} {width}: {left}, {right}");
        }
        catch (TargetInvocationException error) when (error.InnerException is DivideByZeroException or OverflowException)
        {
            var actual = error.InnerException is DivideByZeroException ? "divideByZero" : "overflow";
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

// A different actual implementation must not satisfy the same universal contract.
var wrongOutput = Path.Combine(root, "WrongQuotient");
Directory.CreateDirectory(wrongOutput);
var wrongDll = Path.Combine(wrongOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var method = module.GetType("Examples.Division").Methods.Single(m => m.Name == "Quotient");
    method.Body.Instructions.Single(i => i.OpCode == OpCodes.Div_Un).OpCode = OpCodes.Mul;
    module.Write(wrongDll);
}
uint Evaluate(string dll) => (uint)Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Division")!
    .GetMethod("Quotient")!.Invoke(null, [6u, 2u])!;
if (Evaluate(assembly) != 3 || Evaluate(wrongDll) != 12)
    throw new InvalidOperationException("The compiled quotient and product disagree with the counterexample.");

const string contractSelector = "Division::Quotient(uint,uint)";
verification.VerifyContractVariant(assembly, "Examples", contractSelector, Path.Combine(root, "Quotient32"),
    wrongDll, contractSelector, wrongOutput,
    """
    /-- Unsigned division by a nonzero divisor preserves caller memory. -/
    def quotient : MethodContract (W32 × W32) where
      args pair := [.scalar (.i32 pair.1), .scalar (.i32 pair.2)]
      pre pair _ := pair.2 ≠ 0
      footprint _ := []
      post pair before after values := after = before ∧
        values = [.scalar (.i32 (BitVec.ofNat 32 (pair.1.toNat / pair.2.toNat)))]
    """, """
    theorem correctness : quotient.Holds Extracted.program 0 := by
      rintro ⟨left, right⟩ memory nonzero
      apply MethodContract.Holds.intro (c := quotient) (input := (left, right)) memory
        [.scalar (.i32 (BitVec.ofNat 32 (left.toNat / right.toNat)))] ?_ (Confined.refl _ _) ⟨rfl, rfl⟩
      exact ⟨4, ExampleProof.correctness_framed memory left right nonzero⟩
    """, """
    /-- The changed multiplication returns 12 for 6 divided by 2. -/
    theorem correctness : quotient.Refuted Extracted.program 0 :=
      .of_return (input := (6, 2)) (initial := Memory.empty) (by dsimp [quotient]; decide)
        (rfl : invoke Extracted.program 4 0 (quotient.args (6, 2)) Memory.empty = .ok _)
        (by rintro ⟨-, _, rfl, -, wrong⟩; revert wrong; decide)
    """, example: At("Examples/Proofs/Quotient32.lean"));

Console.WriteLine($"PASS {cases} division comparisons, both universal quotients and the product refutation");
