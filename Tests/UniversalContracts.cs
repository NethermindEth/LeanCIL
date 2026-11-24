#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ContractVariants.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/UniversalContracts");

var contracts = new[]
{
    ("Arithmetic", "Choose", "Arithmetic::Choose(bool,ulong,ulong)", "Choose"),
    ("GenericMethods", "Identity64", "GenericMethods::Identity64(ulong)", "GenericIdentity"),
    ("Arithmetic", "Struct", "Arithmetic::Struct(ulong)", "Struct")
};
foreach (var (owner, name, selector, proofName) in contracts)
{
    var wrong = Path.Combine(root, "Wrong" + name);
    Directory.CreateDirectory(wrong);
    var dll = Path.Combine(wrong, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples." + owner).Methods.Single(method => method.Name == name);
        if (name == "Choose")
        {
            foreach (var instruction in method.Body.Instructions)
                if (instruction.OpCode == OpCodes.Ldarg_1) instruction.OpCode = OpCodes.Ldarg_2;
                else if (instruction.OpCode == OpCodes.Ldarg_2) instruction.OpCode = OpCodes.Ldarg_1;
        }
        else
        {
            var target = name == "Struct"
                ? method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Stfld &&
                    ((FieldReference)instruction.Operand).Name == "Payload")
                : method.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Ret);
            var il = method.Body.GetILProcessor();
            il.InsertBefore(target, Instruction.Create(OpCodes.Ldc_I8, 1L));
            il.InsertBefore(target, Instruction.Create(OpCodes.Add));
        }
        module.Write(dll);
    }

    // Confirm the mutant is executable and has an actual wrong result, including wraparound.
    var runtime = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples." + owner)!
        .GetMethod(name, BindingFlags.Public | BindingFlags.NonPublic | BindingFlags.Static)!;
    object[] inputs = name == "Choose" ? [true, ulong.MaxValue, 0UL] : [ulong.MaxValue];
    if ((ulong)runtime.Invoke(null, inputs)! == ulong.MaxValue)
        throw new InvalidOperationException("Mutation did not change the result: " + name);

    VerifyVariant(name, selector, proofName, dll, wrong);
    Console.WriteLine($"PASS universal {name} contract refuted for incorrect compiled CIL at the runtime witness");
}

// The contract each positive proof states, and the input on which the mutant returns another value.
void VerifyVariant(string name, string selector, string proofName, string wrongAssembly, string wrong)
{
    const string maximum = "18446744073709551615";
    var (input, witness, args, arguments, violation) = name switch
    {
        "Choose" => ("Bool × CIL.W64 × CIL.W64", $"(true, {maximum}, 0)",
            "[.scalar (.i32 (if input.1 then 1 else 0)), .scalar (.i64 input.2.1), .scalar (.i64 input.2.2)]",
            $"[.scalar (.i32 1), .scalar (.i64 {maximum}), .scalar (.i64 0)]", "-, out, rfl, -, wrong"),
        "Identity64" => ("CIL.W64", maximum, "[.scalar (.i64 input)]", $"[.scalar (.i64 {maximum})]",
            "-, out, rfl, -, wrong"),
        _ => ("CIL.W64", maximum, "[.scalar (.i64 input)]", $"[.scalar (.i64 {maximum})]", "-, out, rfl, wrong, -")
    };
    var (pre, post) = name == "Struct"
        ? ("pre _ memory := memory.WellFormed",
            "values = [.scalar (.i64 input)] ∧ MemoryBelow initial.nextIdentity initial final")
        : ("pre _ _ := True", name == "Choose"
            ? "final = initial ∧ values = [.scalar (.i64 (if input.1 then input.2.1 else input.2.2))]"
            : "final = initial ∧ values = [.scalar (.i64 input)]");
    var permitted = name == "Struct" ? "Memory.empty_wellFormed" : "trivial";
    var declaration = $$"""
        /-- Result and memory guarantees of the shipped implementation. -/
        def contract : MethodContract ({{input}}) where
          args input := {{args}}
          {{pre}}
          footprint _ := []
          post input initial final values := {{post}}
        """;
    var holds = name switch
    {
        "Choose" => """
            theorem correctness : contract.Holds Extracted.program 0 := by
              rintro ⟨flag, left, right⟩ memory -
              exact MethodContract.Holds.intro memory _
                (ExampleProof.correctness memory flag left right) (Confined.refl _ _) ⟨rfl, rfl⟩
            """,
        "Identity64" => """
            theorem correctness : contract.Holds Extracted.program 0 := by
              intro value memory _
              exact MethodContract.Holds.intro memory _
                (ExampleProof.correctness memory value) (Confined.refl _ _) ⟨rfl, rfl⟩
            """,
        _ => """
            theorem correctness : contract.Holds Extracted.program 0 := by
              intro value memory formed
              obtain ⟨fuel, final, ran, framed⟩ := ExampleProof.framed memory value formed
              exact MethodContract.Holds.intro final _ ⟨fuel, ran⟩ framed ⟨rfl, framed.nil_memoryBelow⟩
            """
    };
    var refutation = $$"""
        /-- The mutant returns a different value at the runtime witness. -/
        theorem correctness : contract.Refuted Extracted.program 0 :=
          .of_return (input := {{witness}}) (initial := Memory.empty) {{permitted}}
            (rfl : invoke Extracted.program 64 0 {{arguments}} Memory.empty = .ok _)
            (by rintro ⟨{{violation}}⟩; revert wrong; decide)
        """;
    verification.VerifyContractVariant(assembly, "Examples", selector, Path.Combine(root, name),
        wrongAssembly, selector, wrong, declaration, holds, refutation,
        example: At($"Examples/Proofs/{proofName}.lean"), imports: "import CIL.Safety.MemoryBelow");
}
