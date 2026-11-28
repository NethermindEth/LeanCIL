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

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Constructors");
Directory.CreateDirectory(root);
var cases = 0;
var queue = new GeneratedQueue(verification, assembly);

void Compare(string dll, string name, string suffix = "")
{
    var method = Assembly.Load(File.ReadAllBytes(dll)).GetType("Examples.Constructors")!.GetMethod(name)!;
    var output = Path.Combine(root, name + suffix);
    Directory.CreateDirectory(output);
    var claims = new List<string>();
    var values = name == "Default" ? new ulong[] { 0 } :
        [0, 1, 127, 128, 255, 65535, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue];
    foreach (var bits in values)
    {
        object[] inputs = name == "Default" ? [] : [bits];
        var invocation = $"CIL.Safety.invoke Extracted.program 128 0 [{(inputs.Length == 0 ? "" : $".scalar (.i64 {bits})")}] CIL.Safety.Memory.empty";
        try
        {
            var expected = (ulong)method.Invoke(null, inputs)!;
            claims.Add($"({invocation}).map Prod.snd = .ok [.scalar (.i64 {expected})]");
        }
        catch (TargetInvocationException error) when (error.InnerException is OverflowException)
        {
            claims.Add($"(match {invocation} with | .error fault => fault.fault = .arithmetic .overflow | .ok _ => False)");
        }
    }
    var proof = Path.Combine(output, "BoundaryProof.lean");
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nset_option maxRecDepth 8192\n" +
        "namespace ExampleProof\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact " +
        (claims.Count == 1 ? "rfl" : "⟨" + string.Join(", ", claims.Select(_ => "rfl")) + "⟩") + "\nend ExampleProof\n");
    var selector = $"Constructors::{name}({(name == "Default" ? "" : "ulong")})";
    queue.Add(new(selector, proof, output, Assembly: dll), () =>
    {
        cases += claims.Count;
        Console.WriteLine($"PASS {name}{suffix}: {claims.Count} runtime comparisons");
    });
}

foreach (var name in new[] { "Read", "Packed", "Nested", "Default", "Checked" }) Compare(assembly, name);

// newobj itself zero-initializes storage, even when a constructor does not write it.
var zeroed = Path.Combine(root, "Zeroed.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var constructor = module.GetType("Examples.Counter").Methods.Single(m => m.Name == ".ctor");
    constructor.Body.Instructions.Clear();
    constructor.Body.Instructions.Add(Instruction.Create(OpCodes.Ret));
    module.Write(zeroed);
}
Compare(zeroed, "Read", "-Zeroed");
queue.Flush();

var entries = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Constructors")!;
ulong FieldAtMax(string name)
{
    var value = entries.GetMethod(name)!.Invoke(null, [ulong.MaxValue])!;
    return (ulong)value.GetType().GetField("Value")!.GetValue(value)!;
}
if (FieldAtMax("Return") != ulong.MaxValue || FieldAtMax("WrongReturn") != 0)
    throw new InvalidOperationException("Constructors disagree with the wraparound counterexample.");

verification.VerifyContractVariant(assembly, "Examples", "Constructors::Return(ulong)",
    Path.Combine(root, "UniversalValue"),
    assembly, "Constructors::WrongReturn(ulong)", Path.Combine(root, "WrongValue"),
    """
    /-- The returned struct contains the eight little-endian bytes of its UInt64 argument. -/
    def counterValue : MethodContract W64 where
      args input := [.scalar (.i64 input)]
      pre _ memory := memory = Memory.empty
      footprint _ := []
      post input _ _ values := values = [.scalar (.aggregate (numberBytes input.toNat 8))]
    """, """
    theorem correctness : counterValue.Holds Extracted.program 0 := by
      intro input initial empty
      change initial = Memory.empty at empty
      subst initial
      have bytes := ExampleProof.correctness input
      cases returned : invoke Extracted.program 16 0 [.scalar (.i64 input)] Memory.empty with
      | error fault => rw [returned] at bytes; cases bytes
      | ok result =>
        obtain ⟨final, values⟩ := result
        rw [returned] at bytes
        have framed : Confined [] Memory.empty final := by
          constructor
          · exact Nat.zero_le _
          all_goals intro id bound; exact (Nat.not_lt_zero id bound).elim
        exact MethodContract.Holds.intro (c := counterValue) (input := input) final values
          ⟨16, returned⟩ framed (Except.ok.inj bytes)
    """, """
    /-- Adding one wraps at UInt64.MaxValue, leaving a struct whose eight bytes are zero. -/
    theorem correctness : counterValue.Refuted Extracted.program 0 :=
      .of_return (input := -1) (initial := Memory.empty) rfl
        (rfl : invoke Extracted.program 16 0 (counterValue.args (-1)) Memory.empty = .ok _)
        (by
          rintro ⟨-, _, rfl, wrong⟩
          exact (by decide : [Value.scalar (.aggregate (numberBytes 0 8))] ≠
            [Value.scalar (.aggregate (numberBytes (2^64 - 1) 8))]) wrong)
    """, example: At("Examples/Proofs/ConstructorValue.lean"));

// Writes Examples with Counter or its constructor rewritten by one named mutation.
string Mutate(string mutation, string output)
{
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using var module = ModuleDefinition.ReadModule(assembly);
    var type = module.GetType("Examples.Counter");
    var entry = module.GetType("Examples.Constructors").Methods.Single(m => m.Name == "Return");
    var instruction = entry.Body.Instructions.Single(i => i.OpCode.Code == Code.Newobj);
    var constructor = type.Methods.Single(m => m.Name == ".ctor");
    switch (mutation)
    {
        case "not-constructor": instruction.Operand = type.Methods.Single(m => m.Name == "WriteRead"); break;
        case "static": constructor.HasThis = false; constructor.IsStatic = true; break;
        case "class": type.BaseType = module.TypeSystem.Object; break;
        case "base":
            type.BaseType = new TypeReference("System", "Exception", module, module.TypeSystem.CoreLibrary);
            break;
        case "return": constructor.ReturnType = module.TypeSystem.Int32; break;
        case "cycle":
            constructor.Body.Instructions.Clear();
            var il = constructor.Body.GetILProcessor();
            il.Emit(OpCodes.Ldarg_1);
            il.Emit(OpCodes.Call, entry);
            il.Emit(OpCodes.Pop);
            il.Emit(OpCodes.Ret);
            break;
    }
    module.Write(dll);
    return dll;
}

foreach (var mutation in new[] { "not-constructor", "static", "base", "return", "cycle" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    var dll = Mutate(mutation, output);
    var result = Execute(Extract("extract", dll, "Examples", "Constructors::Return(ulong)", output));
    var marker = mutation switch
    {
        "cycle" => "Recursive managed dependency",
        "base" => "Only classes deriving from System.Object through admitted classes are modelled",
        _ => "Unsupported",
    };
    if (result.Code == 0 || !result.Output.Contains(marker) || File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException($"Invalid constructor accepted: {mutation}\n{result.Output}");
}

// Counter re-declared as a class: newobj must allocate a heap instance charged to the heap
// budget, never construct struct storage.
var classOutput = Path.Combine(root, "Class");
var classDll = Mutate("class", classOutput);
var classExtraction = Path.Combine(classOutput, "Extraction");
Run(Extract("extract", classDll, "Examples", "Constructors::Return(ulong)", classExtraction));
var classLean = File.ReadAllText(Path.Combine(classExtraction, "Extracted.lean"));
// Only a construction has an `.object` link.
if (!classLean.Contains(": Link := .object ", StringComparison.Ordinal) ||
    classLean.Contains(": Link := .aggregate ", StringComparison.Ordinal))
    throw new InvalidOperationException("Class construction was not extracted as a heap allocation:\n" + classLean);
var classProof = Path.Combine(classOutput, "ClassProof.lean");
File.WriteAllText(classProof, """
import Extracted
import CIL.Safety.Execution
set_option maxRecDepth 8192
namespace ExampleProof
open CIL.Safety

/-- Normal execution allocates the object. An explicit zero-byte budget rejects its allocation. -/
theorem correctness :
    (match invoke Extracted.program 128 0 [.scalar (.i64 5)]
        Memory.empty with
      | .ok (_, [.object (.address _)]) => true
      | _ => false) = true ∧
    (match invoke Extracted.program 128 0 [.scalar (.i64 5)]
        { Memory.empty with heapBudget := some 0 } with
      | .error failure => failure.fault = .allocationFailure 8 0
      | .ok _ => False) := ⟨rfl, rfl⟩

end ExampleProof
""");
verification.Verify(classDll, "Examples", "Constructors::Return(ulong)", classProof,
    Path.Combine(classOutput, "Verified"));
Console.WriteLine("PASS class: newobj allocates a heap instance and faults at an explicit zero-byte budget");

Console.WriteLine($"PASS {cases} constructor comparisons, universal value proof, class allocation and " +
    "five malformed constructor rejections");
