#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs

using System.Reflection;
using Mono.Cecil;
using Mono.Cecil.Cil;

// SavedLength stores its first span in a local, takes the local's address, stores the second span there and reads
// the length through the address. The CLR reads the slot when the getter runs, so the result is the second length.
var root = At("artifacts/SpanHomeReads");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var assembly = Path.Combine(root, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
{
    var type = module.GetType("Examples.MemorySpans");
    var byRef = type.Methods.Single(method => method.Name == "ByRefSpan");
    var call = byRef.Body.Instructions.Single(instruction => instruction.OpCode == OpCodes.Call);
    var getter = (MethodReference)call.Operand;
    var span = ((ByReferenceType)byRef.Parameters[0].ParameterType).ElementType;
    var savedLength = new MethodDefinition("SavedLength",
        Mono.Cecil.MethodAttributes.Public | Mono.Cecil.MethodAttributes.Static, module.TypeSystem.Int32);
    savedLength.Parameters.Add(new ParameterDefinition(span));
    savedLength.Parameters.Add(new ParameterDefinition(span));
    var local = new VariableDefinition(span);
    savedLength.Body.Variables.Add(local);
    savedLength.Body.InitLocals = true;
    var il = savedLength.Body.GetILProcessor();
    il.Emit(OpCodes.Ldarg_0);
    il.Emit(OpCodes.Stloc_0);
    il.Emit(OpCodes.Ldloca_S, local);
    il.Emit(OpCodes.Ldarg_1);
    il.Emit(OpCodes.Stloc_0);
    il.Emit(OpCodes.Call, getter);
    il.Emit(OpCodes.Ret);
    type.Methods.Add(savedLength);
    module.Write(assembly);
}
RequireLeanFixtures("CIL.Extraction.Translation");
var runtime = Assembly.LoadFile(assembly).GetType("Examples.MemorySpans")!.GetMethod("SavedLength")!
    .CreateDelegate<SavedLength>();
int[] storage = [0, 0];
(int First, int Second)[] cases = [(1, 2), (2, 1)];
foreach (var (first, second) in cases)
{
    var length = runtime(storage.AsSpan(0, first), storage.AsSpan(0, second));
    if (length != second) throw new Exception($"CLR SavedLength({first}, {second}) returned {length}");
}
var output = Path.Combine(root, "SavedLength");
Run(["dotnet", ExtractorPath, "extract", assembly,
    "MemorySpans::SavedLength(System.Span`1<System.Int32>,System.Span`1<System.Int32>)", output]);
var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
var proof = Path.Combine(root, "SavedLength.lean");
var theorems = string.Concat(cases.Select(lengths => $$"""

    theorem saved_view_length_{{lengths.First}}_{{lengths.Second}} :
        (match CIL.Safety.invoke Extracted.program 32 0
            [view {{lengths.First}}, view {{lengths.Second}}] inputMemory with
         | .ok outcome => outcome.2 == [.scalar (.i32 {{lengths.Second}})]
         | .error _ => false) = true := by decide +kernel
    #print axioms saved_view_length_{{lengths.First}}_{{lengths.Second}}
    """));
File.WriteAllText(proof, source + $$"""

    /-- One live 16-byte caller allocation; the length getter reads no element bytes. -/
    private def inputMemory : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
      allocations := fun identity => if identity == 0 then
        some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
      nextIdentity := 1 }

    /-- A writable int32 view of `length` elements at the start of allocation 0. -/
    private def view (length : Nat) : CIL.Safety.Value := .bufferSpan ⟨.address ⟨0, 0⟩, length, 4, true⟩
    """ + theorems + "\n");
evidence.Add(proof, "PASS span local read through its address after a later store: SavedLength");
evidence.Check(replay: false);

/// <summary>The rewritten SavedLength, called with spans the CLR cannot box for reflection.</summary>
delegate int SavedLength(Span<int> first, Span<int> second);
