#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/MemorySpans");
Directory.CreateDirectory(root);
Run(["lake", "build", "CIL.Extraction.Translation", "CIL.SymbolicExecution"]);

foreach (var (name, signature, arguments, expected) in new[]
{
    ("SliceRead", "System.ReadOnlySpan`1<System.Int32>,System.Int32,System.Int32,System.Int32",
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 3, 4, false⟩, .scalar (.i32 1), " +
        ".scalar (.i32 2), .scalar (.i32 0)]", 9),
    ("SliceWrite", "System.Span`1<System.Int32>,System.Int32,System.Int32,System.Int32,System.Int32",
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 3, 4, true⟩, .scalar (.i32 1), " +
        ".scalar (.i32 2), .scalar (.i32 0), .scalar (.i32 11)]", 11),
    ("Existing", "System.Int32&,System.Int32,System.Int32",
        "[.reference (.address ⟨0, 0⟩), .scalar (.i32 3), .scalar (.i32 1)]", 7)
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"MemorySpans::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def spanMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨12, 1, []⟩, true, []⟩ else none
          cells := fun _ offset => ⟨if offset == 4 then 7 else 0, true⟩
          views := [⟨0, 0, 12, true, true⟩]
          nextIdentity := 1 }

        theorem compiled_span_result :
            (CIL.Safety.invoke Extracted.program 64 0 {{arguments}} spanMemory).map Prod.snd =
              .ok [.scalar (.i32 {{expected}})] := rfl
        #print axioms compiled_span_result
        """);
    var result = Run(["lake", "env", "lean", proof]);
    if (result.Contains("sorryAx", StringComparison.Ordinal)) throw new Exception("Untrusted span proof");
    Console.WriteLine("PASS compiled span certificate and execution: " + name);
}

var original = File.ReadAllText(Path.Combine(root, "SliceRead", "Extracted.lean"));
foreach (var (name, before, after) in new[]
{
    ("element-width", ".span 4 false", ".span 8 false"),
    ("write-authority", ".span 4 false", ".span 4 true")
})
{
    if (!original.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing mutation: " + name);
    var proof = Path.Combine(root, "Forged-" + name + ".lean");
    File.WriteAllText(proof, original.Replace(before, after, StringComparison.Ordinal));
    var result = Execute(["lake", "env", "lean", proof]);
    if (result.Code == 0 || !result.Output.Contains("SpecializationValid", StringComparison.Ordinal))
        throw new Exception("Incorrect span evidence rejection: " + name + "\n" + result.Output);
    Console.WriteLine("PASS independent span evidence rejection: " + name);
}
