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
var root = At("artifacts/AggregateSpans");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var queue = new GeneratedQueue(verification, assembly);
string Span(int width, bool writable = true, int offset = 0, int length = 2) =>
    $".bufferSpan ⟨.address ⟨0, {offset}⟩, {length}, {width}, {writable.ToString().ToLowerInvariant()}⟩";
foreach (var method in metadata.GetType("Examples.AggregateSpans").Methods.Where(method => method.IsPublic))
foreach (var profile in method.Name.StartsWith("Layout", StringComparison.Ordinal)
    ? new[] { "x64-sse2", "arm64-advsimd" } : ["scalar"])
{
    var name = method.Name;
    var layoutWidth = profile == "x64-sse2" ? 64 : 48;
    var output = Path.Combine(root, profile == "scalar" ? name : name + "-" + profile);
    Directory.CreateDirectory(output);
    var arguments = name switch
    {
        "LayoutBytes" => Span(layoutWidth), "LayoutRead" => Span(layoutWidth, false),
        "WordsView" => Span(1, false, length: 64),
        "VectorBytes" => Span(16), "ReadVector" => Span(16, false),
        "Read" => Span(32, false),
        "Write" => Span(32) + ", .scalar (.aggregate (List.replicate 32 7))",
        "WriteVector" => Span(16) + ", .scalar (.v128 0)",
        "Copy" => Span(32, false) + ", " + Span(32, offset: 32),
        "Slice" => Span(32) + ", .scalar (.i32 1), .scalar (.i32 1)",
        _ => Span(32)
    };
    var expected = name switch
    {
        "LayoutBytes" => Span(1, length: 2 * layoutWidth),
        "LayoutRead" => $".scalar (.aggregate (List.replicate {layoutWidth} 0))",
        "Bytes" => Span(1, length: 64), "WordsView" => Span(32, false),
        "VectorBytes" => Span(1, length: 32), "ReadVector" => ".scalar (.v128 0)",
        "Read" => ".scalar (.aggregate (List.replicate 32 0))",
        "Copy" => ".scalar (.i32 1)", "Slice" => Span(32, offset: 32, length: 1), _ => ""
    };
    var proof = Path.Combine(output, "Proof.lean");
    var extra = name switch
    {
        "Write" => $"(CIL.Safety.invoke Extracted.program 64 0 [{arguments}] memory).map " +
            "(fun result => [(result.1.cells 0 0).bits, (result.1.cells 0 31).bits, " +
            "(result.1.cells 0 32).bits]) = .ok [7, 7, 0]",
        "WriteVector" => "(CIL.Safety.invoke Extracted.program 64 0 [" + Span(16) +
            ", .scalar (.snapshot .vector128 (List.replicate 8 (0, true) ++ " +
            "List.replicate 8 (0, false)))] memory).map " +
            "(fun result => (result.1.cells 0 8).initialized) = .ok false",
        "Copy" => $"(CIL.Safety.invoke Extracted.program 64 0 [{arguments}] " +
            "{ memory with cells := fun _ offset => ⟨BitVec.ofNat 8 offset, true⟩ }).map " +
            "(fun result => [(result.1.cells 0 32).bits, (result.1.cells 0 95).bits, " +
            "(result.1.cells 0 96).bits]) = .ok [0, 63, 96]",
        _ => null
    };
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        /-- Existing initialized caller storage shared by overlapping aggregate views. -/
        def memory : CIL.Safety.Memory := { Examples.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨128, 16, []⟩, true, [128]⟩ else none
          cells := fun _ _ => ⟨0, true⟩
          views := [⟨0, 0, 128, true, true⟩]
          nextIdentity := 1 }
        /-- Compiled span operations retain aggregate and vector storage identities. -/
        """ + $"\ntheorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [{arguments}] memory).map " +
        $"Prod.snd = .ok [{expected}] := by rfl\n#print axioms correctness\n" +
        (extra is null ? "" : "/-- Stores and overlapping copies preserve neighbouring bytes. -/\n" +
            "theorem contents : " + extra + " := by rfl\n#print axioms contents\n") +
        "end ExampleProof\n");
    queue.Add(new(method.FullName, proof, output, Profile: profile),
        () => Console.WriteLine("PASS aggregate span: " + name + " (" + profile + ")"));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
foreach (var (name, before, after, theorem) in new[]
{
    ("Bytes", ".spanReinterpret 32 1 true", ".spanReinterpret 16 1 true", "method0_layouts_validated"),
    ("WordsView", ".spanReinterpret 1 32 false", ".spanReinterpret 1 16 false", "method0_layouts_validated"),
    ("Copy", ".spanCopy 32 true", ".spanCopy 16 true", "method0_layouts_validated"),
    ("VectorBytes", ".spanReinterpret 16 1 true", ".spanReinterpret 32 1 true", "method0_scalars_validated")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), theorem);
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing span mutation");
    var path = Path.Combine(root, "Rejected" + name + ".lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS aggregate span evidence rejection: " + name,
        theorem.EndsWith("layouts_validated", StringComparison.Ordinal) ? "MethodLayoutsValid" : "ScalarFlowValid");
}
rejected.Check();
