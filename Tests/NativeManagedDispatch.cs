#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Text.RegularExpressions;
using Mono.Cecil;
using Mono.Cecil.Cil;

var root = At("artifacts/NativeManagedDispatch");
Directory.CreateDirectory(root);
var dll = Path.Combine(root, "NativeManagedDispatch.dll");
string selector;
using (var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
{
    var methods = module.GetType("Examples.NativeManagedDispatch").Methods;
    foreach (var method in methods)
    {
        var call = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Calli);
        if (call.Next?.OpCode.Code != Code.Ret) throw new InvalidOperationException("Missing terminal calli");
        method.Body.GetILProcessor().InsertBefore(call, Instruction.Create(OpCodes.Tail));
    }
    var dispatch = methods.Single(method => method.Name == "Dispatch");
    // Preserve the native load/store shape while retaining a numeric native local beside the target.
    dispatch.Body.Variables[0].VariableType = module.TypeSystem.IntPtr;
    var numeric = new VariableDefinition(module.TypeSystem.IntPtr);
    dispatch.Body.Variables.Add(numeric);
    var processor = dispatch.Body.GetILProcessor();
    var first = dispatch.Body.Instructions[0];
    processor.InsertBefore(first, Instruction.Create(OpCodes.Ldc_I4_7));
    processor.InsertBefore(first, Instruction.Create(OpCodes.Conv_I));
    processor.InsertBefore(first, Instruction.Create(OpCodes.Stloc, numeric));
    processor.InsertBefore(first, Instruction.Create(OpCodes.Ldloc, numeric));
    processor.InsertBefore(first, Instruction.Create(OpCodes.Pop));
    selector = dispatch.FullName;
    module.Write(dll);
}
var output = Path.Combine(root, "extracted");
Run(["dotnet", ExtractorPath, "extract", dll, selector, output]);
var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
if (Regex.Matches(source, @"(?m)^def method\d+ : Method :=").Count != 2)
    throw new InvalidOperationException("Native dispatch did not retain a bounded cyclic catalog");
var scalar = NarrowEvidence(source, "method0_scalars_validated");
var proof = source + "\n" + CheckedEvidenceControl(source, scalar, ["method0_scalars_validated"], 0) + "\n" + """
open CIL CIL.Safety
private def nativeSignature : ManagedSignature :=
  ⟨Extracted.method1Closed.returnType, Extracted.method1Closed.parameters⟩
private def nativeIdentity : ManagedIdentity :=
  ⟨Extracted.method1Closed.owner, Extracted.method1Closed.token, []⟩
private def nativeMemory : CIL.Safety.Memory :=
  { allocations := fun index => if index == 0 then
      some { kind := .immutableStatic, layout := ⟨8, 8, []⟩ } else none
    cells := fun _ _ => ⟨0, true⟩
    views := [⟨0, 0, 8, true, false⟩]
    nextIdentity := 1
    staticBindings := [(42, ⟨0, 0⟩)] }
private def nativeTable : MethodTable :=
  ⟨nativeSignature, some #[nativeIdentity], some ⟨42, 0⟩⟩
private def nativeRun (table : MethodTable) (index : Nat) (marker : BitVec 64)
    (memory : CIL.Safety.Memory := nativeMemory) :=
  CIL.Safety.invoke Extracted.program 128 0
    [.methodTable table, .scalar (.i32 (BitVec.ofNat 32 index)), .scalar (.i32 5),
      .scalar (.i32 3), .scalar (.i64 marker)] memory
/-- A native table-selected handler revisits its indirect tail target before returning. -/
theorem native_cycle : (match nativeRun nativeTable 0 0 with
    | .ok (_, values) => some values | .error _ => none) = some [.scalar (.i32 8)] :=
  by decide +kernel
#print axioms native_cycle
/-- The same supplied native entry may terminate with its named modeled exception. -/
theorem native_throw : (match nativeRun nativeTable 0 (-1) with
    | .error fault => some fault.fault | .ok _ => none) =
      some (.thrown "System.InvalidOperationException") := by decide +kernel
#print axioms native_throw
/-- A numeric local beside the authenticated target keeps its ordinary scalar representation. -/
theorem numeric_local : Extracted.method0.localKinds[1]? = some .word64 := by decide +kernel
#print axioms numeric_local
/-- Out-of-range and uninitialized table storage cannot manufacture callable identities. -/
theorem native_invalid_storage :
    (nativeRun nativeTable 1 0).isOk = false ∧
    (nativeRun nativeTable 0 0 { nativeMemory with cells := fun _ _ => ⟨0, false⟩ }).isOk = false :=
  by decide +kernel
#print axioms native_invalid_storage
/-- The catalog reauthenticates opaque identities obtained from supplied storage. -/
theorem native_forged_identity :
    (nativeRun { nativeTable with targets := some #[{ nativeIdentity with token := 0 }] } 0 0).isOk =
      false := by decide +kernel
#print axioms native_forged_identity
""";
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution");
var evidence = new GeneratedEvidence(root);
var path = Path.Combine(root, "NativeProof.lean");
File.WriteAllText(path, proof);
evidence.Add(path, "PASS native supplied-table cycle, exception, scalar local and storage checks");
var rejected = new RejectedEvidence(root);
var load = Regex.Match(scalar, @"(?m)^  \.managed \(\.tableLoad [^\r\n]+$").Value;
if (load.Length == 0) throw new InvalidOperationException("Missing native table load");
foreach (var (name, mutated) in new[]
{
    ("signature", scalar.Replace(load, load.Replace("System.Int32", "System.UInt32", StringComparison.Ordinal),
        StringComparison.Ordinal)),
    ("raw-load", scalar.Replace("opcode := 77, operand := .none", "opcode := 76, operand := .none",
        StringComparison.Ordinal)),
    ("offset", scalar.Replace(".managed .tableOffset", ".nativeBinary (.add)", StringComparison.Ordinal)),
    ("input", scalar.Replace(".pointer (.atom Extraction.runtimeScope \"System.IntPtr\")",
        ".pointer (.atom Extraction.runtimeScope \"System.Int64\")", StringComparison.Ordinal))
})
{
    if (mutated == scalar) throw new InvalidOperationException("Ineffective native evidence mutation: " + name);
    var rejectedPath = Path.Combine(root, "Rejected-" + name + ".lean");
    File.WriteAllText(rejectedPath, mutated);
    rejected.Add(rejectedPath, "PASS independently rejected native dispatch evidence: " + name);
}
var numericDll = Path.Combine(root, "NumericTarget.dll");
using (var module = ModuleDefinition.ReadModule(dll))
{
    var dispatch = module.GetType("Examples.NativeManagedDispatch").Methods.Single(method => method.Name == "Dispatch");
    var loadNative = dispatch.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Ldind_I);
    var processor = dispatch.Body.GetILProcessor();
    loadNative.OpCode = OpCodes.Pop;
    processor.InsertAfter(loadNative, Instruction.Create(OpCodes.Ldc_I8, 0L));
    module.Write(numericDll);
}
var numericResult = Execute(["dotnet", ExtractorPath, "extract", numericDll, selector, Path.Combine(root, "Numeric")]);
if (numericResult.Code == 0 || !numericResult.Output.Contains("authenticated pointer provenance", StringComparison.Ordinal))
    throw new InvalidOperationException("Numeric target provenance was accepted: " + numericResult.Output);
evidence.Check();
rejected.Check();
