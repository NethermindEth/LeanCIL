#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include ../scripts/BatchVerification.cs

using System.Reflection;
using System.Text.Json;
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
var positives = new GeneratedQueue(verification, assembly);
foreach (var (_, name, selector, proofName) in contracts)
    positives.Add(new(selector, At($"Examples/Proofs/{proofName}.lean"), Path.Combine(root, name)),
        () => Console.WriteLine($"PASS universal {name}: arbitrary inputs and caller memory with preservation"));
positives.Flush();

foreach (var (owner, name, selector, _) in contracts)
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

    // Extraction must succeed: the contract is refuted for supported, incorrect CIL by a verified counterexample.
    Run(Extract("extract", dll, "Examples", selector, wrong));
    var refutation = Path.Combine(wrong, "Refutation.lean");
    File.WriteAllText(refutation, Refutation(name));
    var refuted = verification.Verify(dll, "Examples", selector, refutation, wrong, theorem: "ExampleProof.refuted",
        existingArtifacts: true).refutation;
    var entry = JsonDocument.Parse(File.ReadAllText(Path.Combine(wrong, "identity.json"))).RootElement
        .GetProperty("entry").GetString();
    if (refuted?.method.signature != entry)
        throw new InvalidOperationException("Incorrect implementation has no verified refutation: " + name);
    Console.WriteLine($"PASS universal {name} contract refuted for incorrect compiled CIL at the runtime witness");
}

// The contract each positive proof states, and the input on which the mutant returns another value.
static string Refutation(string name)
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
    return $$"""
        import Extracted
        import CIL.Safety.MethodContract
        import CIL.Safety.MemoryBelow
        open CIL.Safety
        namespace ExampleProof
        /-- The statement the universal proof of `{{name}}` makes, as a contract. -/
        def contract : MethodContract ({{input}}) where
          args input := {{args}}
          {{pre}}
          footprint _ := []
          post input initial final values := {{post}}
        /-- The mutant returns another value at the runtime witness. -/
        theorem refuted : contract.Refuted Extracted.program 0 :=
          .of_return (input := {{witness}}) (initial := Memory.empty) {{permitted}}
            (rfl : invoke Extracted.program 64 0 {{arguments}} Memory.empty = .ok _)
            (by rintro ⟨{{violation}}⟩; revert wrong; decide)
        #print axioms refuted
        end ExampleProof

        """;
}
