#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
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

// The named contract each positive example proves as `holds`, and a refutation of it at the input on which the
// mutant returns another value.
static (string Contract, string Proof) Refutation(string name)
{
    const string maximum = "18446744073709551615";
    var (contract, witness, arguments, violation, permitted) = name switch
    {
        "Choose" => ("chooseContract", $"(true, {maximum}, 0)",
            $"[.scalar (.i32 1), .scalar (.i64 {maximum}), .scalar (.i64 0)]", "-, out, rfl, -, wrong", "trivial"),
        "Identity64" => ("identityContract", maximum, $"[.scalar (.i64 {maximum})]", "-, out, rfl, -, wrong",
            "trivial"),
        _ => ("structContract", maximum, $"[.scalar (.i64 {maximum})]", "-, out, rfl, wrong, -",
            "Memory.empty_wellFormed")
    };
    return (contract, $$"""
        /-- The mutant returns a different value at the runtime witness. -/
        theorem correctness : {{contract}}.Refuted Extracted.program 0 :=
          .of_return (input := {{witness}}) (initial := Memory.empty) {{permitted}}
            (rfl : invoke Extracted.program 64 0 {{arguments}} Memory.empty = .ok _)
            (by rintro ⟨{{violation}}⟩; revert wrong; decide)
        """);
}

void VerifyVariant(string name, string selector, string proofName, string wrongAssembly, string wrong)
{
    var (contract, refutation) = Refutation(name);
    verification.VerifyExampleRefutations(assembly, "Examples", selector, At($"Examples/Proofs/{proofName}.lean"),
        contract, Path.Combine(root, name), [new(wrongAssembly, selector, wrong, refutation)]);
}

// Narrowing Choose's contract to empty memory leaves its proof valid but changes the statement it proves, so the
// unchanged refutation, which refutes the shipped contract, no longer matches it and is rejected.
const string chooseSelector = "Arithmetic::Choose(bool,ulong,ulong)";
const string everyMemory = "  pre _ _ := True\n";
var chooseExample = At("Examples/Proofs/Choose.lean");
var chooseSource = File.ReadAllText(chooseExample).ReplaceLineEndings("\n");
if (chooseSource.Split(everyMemory).Length != 2)
    throw new InvalidDataException("Ambiguous contract mutation: " + everyMemory);
var narrowedOutput = Path.Combine(root, "NarrowedChoose");
Directory.CreateDirectory(narrowedOutput);
var narrowedExample = Path.Combine(narrowedOutput, "Choose.lean");
File.WriteAllText(narrowedExample, chooseSource.Replace(everyMemory, "  pre _ memory := memory = Memory.empty\n"));
var narrowed = verification.ExampleStatement(assembly, "Examples", chooseSelector, narrowedExample, narrowedOutput);
var staleOutput = Path.Combine(root, "WrongChooseNarrowed");
Directory.CreateDirectory(staleOutput);
var (chooseContract, chooseRefutation) = Refutation("Choose");
var stale = new Program.ContractCounterexample(Path.Combine(root, "WrongChoose", "Examples.dll"), chooseSelector,
    staleOutput, chooseRefutation);
var rejected = false;
try { verification.VerifyExampleRefutation(chooseExample, chooseContract, stale, "Examples", narrowed); }
catch (Program.StatementMismatchException) { rejected = true; }
if (!rejected || File.Exists(Path.Combine(staleOutput, "verified.json")))
    throw new InvalidOperationException("A refutation of the shipped Choose contract matched a narrowed contract.");
Console.WriteLine("PASS a changed positive contract rejects the refutation of the contract it replaced");
