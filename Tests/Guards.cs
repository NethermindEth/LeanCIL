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

using Mono.Cecil;
using Mono.Cecil.Cil;

// Check normal and exceptional outcomes for integer and null guards. The swapped guard has a certified
// counterexample, and unsupported overloads must fail extraction with the expected member identity.
using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/Guards");
Directory.CreateDirectory(root);

foreach (var (source, entry) in new[]
{
    ("Examples/Proofs/GuardIndex.lean", "Guards::Index(System.UInt32,System.UInt32)"),
    ("Examples/Proofs/GuardRequired.lean", "Guards::Required(System.String)")
})
{
    var proof = Path.GetFileNameWithoutExtension(source);
    verification.Verify(assembly, "Examples", entry, At(source), Path.Combine(root, proof));
    Console.WriteLine($"PASS {proof}: {entry}");
}

// Zero returns under ThrowIfNegative and raises ArgumentOutOfRangeException under ThrowIfNegativeOrZero.
var swapped = Mutate("swapped", "Count",
    (module, call) => Guard(module, call, "ThrowIfNegativeOrZero", module.TypeSystem.Int32));
const string countSelector = "Guards::Count(System.Int32)";
const string countContract = """
    /-- Negative counts raise, and a nonnegative count returns unchanged in the caller's memory. -/
    def contract : OutcomeContract W32 where
      args count := [.scalar (.i32 count)]
      pre _ memory := ∃ literal, memory.literals.lookup "count" = some literal ∧
        formObject memory (.address literal) = .ok (.object (.address literal))
      footprint _ := []
      post count before after values := after = before ∧ values = [.scalar (.i32 count)]
      raises count _ := if count.toInt < 0 then some .argumentOutOfRange else none
    """;
const string positive = """
    /-- The compiled guard satisfies both branches for every count and bound parameter name. -/
    theorem correctness : contract.HoldsCLR Extracted.program 0 := by
      rintro count memory ⟨literal, bound, formed⟩
      obtain ⟨fuel, ran⟩ := ExampleProof.correctness memory literal count bound formed
      by_cases negative : count.toInt < 0
      · simp only [negative, ite_true] at ran
        simpa only [contract, negative, ite_true] using
          (RaisesCLR.of_invoke ran (exception := .argumentOutOfRange) rfl)
      · simp only [negative, ite_false] at ran
        simp only [contract, negative, ite_false]
        exact ⟨fuel, _, _, ran, Confined.refl _ _, _, rfl, rfl, rfl⟩
    """;
const string counterexample = """
    /-- The caller binds the parameter name to a live string object at allocation zero. -/
    private def literalMemory : Memory := { Memory.empty with
      allocations := fun id => if id = 0 then some
        ⟨.object ⟨.object CIL.Extraction.runtimeScope "System.String", []⟩, ⟨1, 1, []⟩, true, []⟩
        else none
      nextIdentity := 1
      literals := [("count", ⟨0, 0⟩)] }

    /-- The substituted guard throws at pc 2 on zero, which the contract requires to return. -/
    theorem correctness : contract.RefutedCLR Extracted.program 0 :=
      .of_fault (input := 0) (initial := literalMemory) ⟨⟨0, 0⟩, rfl, rfl⟩ (by decide)
        (rfl : invoke Extracted.program 8 0 (contract.args 0) literalMemory =
          .error ⟨0, 2, .thrown .argumentOutOfRange⟩) trivial
    """;
verification.VerifyContractVariant(assembly, "Examples", countSelector, Path.Combine(root, "GuardCount"),
    swapped, countSelector, Path.Combine(root, "Reject-swapped"), countContract, positive, counterexample,
    example: At("Examples/Proofs/GuardCount.lean"), imports: "import CIL.Safety.RuntimeExceptions");
Console.WriteLine("PASS GuardCount returns zero and its replacement is certified to throw at the guard");

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
// ThrowIfNull's object parameter accepts any reference, but the model tests only a class instance or null.
var arrayOutput = Path.Combine(root, "Mutant-valueArray");
Directory.CreateDirectory(arrayOutput);
var arrayDll = Path.Combine(arrayOutput, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var body = module.GetType("Examples.Guards").Methods.Single(candidate => candidate.Name == "Required").Body;
    var il = body.GetILProcessor();
    var label = body.Instructions[0];
    il.InsertBefore(label, il.Create(OpCodes.Ldc_I4_1));
    il.Replace(label, il.Create(OpCodes.Newarr, module.TypeSystem.Int32));
    module.Write(arrayDll);
}
var arrayResult = Execute(["dotnet", ExtractorPath, "extract", arrayDll, "Examples.Guards::Required(System.String)",
    Path.Combine(arrayOutput, "out")]);
if (arrayResult.Code != 1 || File.Exists(Path.Combine(arrayOutput, "out", "Extracted.lean")) ||
    !arrayResult.Output.Contains("Unsupported ThrowIfNull argument that is not a class instance",
        StringComparison.Ordinal))
    throw new InvalidOperationException("Incorrect guard rejection: valueArray\n" + arrayResult.Output);
Console.WriteLine("PASS guard rejection: valueArray");
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
