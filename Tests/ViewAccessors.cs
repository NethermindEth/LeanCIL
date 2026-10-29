#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

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
        claims.Add("(match CIL.Safety.invoke Extracted.program 32 0 [.reference .null] memory with " +
            "| .error ⟨_, _, .thrown \"System.NullReferenceException\"⟩ => true | _ => false) = true");
    }
    else
    {
        var writable = (!method.Name.StartsWith("ReadOnly", StringComparison.Ordinal)).ToString().ToLowerInvariant();
        foreach (var (address, length) in new[] { (".null", 0), (".address ⟨0, 16⟩", 0),
            (".address ⟨0, 0⟩", 4) })
            claims.Add("(CIL.Safety.invoke Extracted.program 32 0 " +
                $"[.bufferSpan ⟨{address}, {length}, 4, {writable}⟩] memory).map Prod.snd = " +
                $".ok [.scalar (.i32 {(length == 0 ? 1 : 0)})]");
    }
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        /-- Successful observations identify the checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- Existing storage has no readable bytes or access authority; observations need neither. -/
        def memory : CIL.Safety.Memory := { Examples.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
          nextIdentity := 1 }
        /-- Empty views, readonly receivers and zero-length arrays retain their distinct results. -/
        """ + "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  repeat constructor\n  all_goals first | (apply result_of_toOption; decide +kernel) | decide +kernel\n" +
        "#print axioms correctness\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS view accessor: " + method.Name));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
foreach (var (name, before, after) in new[]
{
    ("Empty", ".observeView .spanEmpty", ".observeView .spanPinnable"),
    ("PinnableNull", ".observeView .spanPinnable", ".spanReference"),
    ("ArrayData", ".observeView .arrayData", ".observeView .spanPinnable")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")),
        "method0_unsafe_validated");
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing accessor mutation");
    var path = Path.Combine(root, name + "Rejected.lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS exact accessor evidence rejection: " + name, "UnsafeCallsValid");
}
rejected.Check();
