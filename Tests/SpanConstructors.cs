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
var root = At("artifacts/SpanConstructors");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in metadata.GetType("Examples.SpanConstructors").Methods.Where(method => method.IsPublic))
foreach (var profile in method.Name == "LayoutLocal" ? new[] { "x64-sse2", "arm64-advsimd" } : ["scalar"])
{
    var name = method.Name;
    var width = name switch
    {
        "Aggregate" or "Pointer" => 32,
        "Vector" or "VectorPointer" => 16,
        "LayoutLocal" => profile == "x64-sse2" ? 64 : 48,
        _ => 4
    };
    var counted = name.Contains("Pointer", StringComparison.Ordinal) || name == "LayoutLocal";
    var writable = name is not ("ReadOnlySingle" or "Vector" or "VectorPointer");
    var length = counted ? 2 : 1;
    var output = Path.Combine(root, name + (profile == "scalar" ? "" : "-" + profile));
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var arguments = ".reference (.address ⟨0, 0⟩)" + (counted ? $", .scalar (.i32 {length})" : "");
    var expected = name.EndsWith("Local", StringComparison.Ordinal) || name == "Local"
        ? $".scalar (.i32 {length})"
        : $".bufferSpan ⟨.address ⟨0, 0⟩, {length}, {width}, {writable.ToString().ToLowerInvariant()}⟩";
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        /-- View construction needs live storage but neither readable bytes nor byte authority. -/
        def memory : CIL.Safety.Memory := { Examples.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨128, 16, []⟩, true, [128]⟩ else none
          nextIdentity := 1 }
        /-- Both constructor encodings retain the validated element layout and capability. -/
        """ + $"\ntheorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [{arguments}] memory).map " +
        $"Prod.snd = .ok [{expected}] := by rfl\n#print axioms correctness\n" +
        (name == "Single" ? """
        /-- View construction rejects expired storage, even when no bytes are read. -/
        theorem expired : CIL.Safety.memoryInstruction (.spanSingleReference 4 true)
            [.reference (.address ⟨0, 0⟩)]
            { memory with allocations := fun _ => some ⟨.callerStack, ⟨128, 16, []⟩, false, [128]⟩ } =
            .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 4) := by rfl
        #print axioms expired
        /-- An empty pointer span may start at the end of its allocation. -/
        theorem emptyAtEnd : CIL.Safety.memoryInstruction (.spanFromReference 32 true)
            [.scalar (.i32 0), .reference (.address ⟨0, 128⟩)] memory =
            .ok (memory, [.bufferSpan ⟨.address ⟨0, 128⟩, 0, 32, true⟩]) := by rfl
        #print axioms emptyAtEnd
        /-- A one-element view must fit entirely within the allocation. -/
        theorem outside : CIL.Safety.memoryInstruction (.spanSingleReference 32 true)
            [.reference (.address ⟨0, 128⟩)] memory =
            .error (.memory .outsideAllocation (.address ⟨0, 128⟩) 32) := by rfl
        #print axioms outside
        /-- A readonly reference cannot construct a writable view. -/
        theorem readOnly : CIL.Safety.memoryInstruction (.spanSingleReference 4 true)
            [.readOnlyReference (.address ⟨0, 0⟩)] memory = .error .invalidState := by rfl
        #print axioms readOnly
        /-- A negative pointer length raises the specified runtime exception. -/
        theorem negative : CIL.Safety.memoryInstruction (.spanFromReference 32 true)
            [.scalar (.i32 (-1)), .reference (.address ⟨0, 0⟩)] memory =
            .error (.thrown "System.ArgumentOutOfRangeException") := by rfl
        #print axioms negative
        """ : "") + "\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output, Profile: profile),
        () => Console.WriteLine("PASS span constructor: " + name + " (" + profile + ")"));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
foreach (var (name, before, after, theorem, marker) in new[]
{
    ("Single", ".spanSingleReference 4 true", ".spanSingleReference 8 true",
        "method0_scalars_validated", "ScalarFlowValid"),
    ("ReadOnlySingle", ".spanSingleReference 4 false", ".spanSingleReference 4 true",
        "method0_scalars_validated", "ScalarFlowValid"),
    ("Aggregate", ".spanSingleReference 32 true", ".spanSingleReference 24 true",
        "method0_layouts_validated", "MethodLayoutsValid"),
    ("Pointer", ".spanFromReference 32 true", ".spanFromReference 16 true",
        "method0_layouts_validated", "MethodLayoutsValid"),
    ("LayoutLocal-x64-sse2", ".reference 64 true", ".reference 48 true",
        "method0_layouts_validated", "MethodLayoutsValid")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), theorem);
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing constructor mutation: " + name);
    var path = Path.Combine(root, name + "Rejected.lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS constructor evidence rejection: " + name, marker);
}
rejected.Check();
