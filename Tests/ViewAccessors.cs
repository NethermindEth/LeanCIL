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
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs
#:include MarshalModelEvidence.cs

using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/ViewAccessors");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in metadata.GetType("Examples.ViewAccessors").Methods.Where(method => method.IsPublic))
{
    var output = Path.Combine(root, method.Name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var claims = new List<string>();
    if (method.Name == "ArrayData")
    {
        foreach (var length in new[] { 0, 4 })
            claims.Add("(CIL.Safety.invoke Extracted.program 32 0 " +
                $"[.array ⟨.address ⟨0, 0⟩, {length}, .signed32⟩] memory).map Prod.snd = " +
                ".ok [.reference (.address ⟨0, 0⟩)]");
        claims.Add("(match CIL.Safety.invoke Extracted.program 32 0 [.object .null] memory with " +
            "| .error ⟨_, _, .thrown .nullReference⟩ => true | _ => false) = true");
    }
    else
    {
        var writable = (!method.Name.StartsWith("ReadOnly", StringComparison.Ordinal)).ToString().ToLowerInvariant();
        // GetReference keeps an empty view's own reference, where GetPinnableReference yields null.
        var nullOnlyWhenNull = method.Name.EndsWith("ReferenceNull", StringComparison.Ordinal);
        foreach (var (address, length) in new[] { (".null", 0), (".address ⟨0, 16⟩", 0),
            (".address ⟨0, 0⟩", 4) })
            claims.Add("(CIL.Safety.invoke Extracted.program 32 0 " +
                $"[.bufferSpan ⟨{address}, {length}, 4, {writable}⟩] memory).map Prod.snd = " +
                $".ok [.scalar (.i32 {(length == 0 && (!nullOnlyWhenNull || address == ".null") ? 1 : 0)})]");
    }
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nnamespace ExampleProof\n" + """
        /-- The caller owns an allocation with no readable bytes or access authority. -/
        def memory : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
          nextIdentity := 1 }
        /-- Empty views, readonly receivers and zero-length arrays retain their distinct results. -/
        """ + $$"""

        theorem correctness :
            {{string.Join(" ∧\n", claims)}} := by
          exact ⟨{{string.Join(", ", claims.Select(_ => "by cil_kernel_rfl"))}}⟩
        #print axioms correctness
        end ExampleProof

        """);
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS view accessor: " + method.Name));
}
queue.Flush();
CheckMarshalModels(root,
[
    ("Empty", 1, ".observeView .spanEmpty", ".observeView .spanPinnable"),
    ("PinnableNull", 1, ".observeView .spanPinnable", ".spanReference"),
    ("ReferenceNull", 1, ".spanReference", ".observeView .spanPinnable"),
    ("ArrayData", 1, ".observeView .arrayData", ".observeView .spanPinnable")
]);
