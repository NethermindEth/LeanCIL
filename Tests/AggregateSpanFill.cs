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
var root = At("artifacts/AggregateSpanFill");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in metadata.GetType("Examples.AggregateSpanFill").Methods.Where(method => method.IsPublic))
{
    var name = method.Name;
    var width = name switch { "Vector128" or "Generic" => 16, "Vector512" => 64, _ => 32 };
    var shape = name switch
    {
        "Vector128" => ".vector128", "Vector256" => ".vector256", "Vector512" => ".vector512",
        _ => $".aggregate {width}"
    };
    var value = name switch
    {
        "Vector128" => ".v128 7", "Vector256" => ".v256 7", "Vector512" => ".v512 7",
        _ => $".aggregate (List.replicate {width} 7)"
    };
    string Args(string element, int length = 2, bool writable = true) =>
        $"[.bufferSpan ⟨.address ⟨0, 16⟩, {length}, {width}, {writable.ToString().ToLowerInvariant()}⟩" +
        (name == "Aliased" ? "]" : $", .scalar ({element})]");
    string Run(string args, string memory = "memory") =>
        $"CIL.Safety.invoke Extracted.program 64 0 {args} {memory}";
    var arguments = Args(value);
    var claims = new List<string>
    {
        $"({Run(arguments)}).map Prod.snd = .ok []",
        $"({Run(arguments)}).map (fun result => [(result.1.cells 0 15).bits, " +
        $"(result.1.cells 0 16).bits, (result.1.cells 0 {16 + width}).bits, " +
        $"(result.1.cells 0 {16 + 2 * width}).bits]) = .ok [11, 7, 7, 11]",
        $"(match {Run(Args(value, writable: false))} with | .error _ => true | .ok _ => false) = true",
        $"(match {Run(arguments, "{ memory with views := [⟨0, 0, 256, true, false⟩] }")} " +
        "with | .error _ => true | .ok _ => false) = true"
    };
    if (name != "Aliased")
    {
        var partial = $".snapshot ({shape}) ((7, true) :: List.replicate {width - 1} (9, false))";
        claims.Add($"({Run(Args(partial))}).map (fun result => " +
            $"[(result.1.cells 0 16).initialized, (result.1.cells 0 17).initialized, " +
            $"(result.1.cells 0 {16 + width}).initialized, (result.1.cells 0 {17 + width}).initialized, " +
            $"(result.1.cells 0 {16 + 2 * width}).initialized]) = .ok [true, false, true, false, true]");
        claims.Add($"({Run(Args(value, length: 0), "{ memory with views := [] }")}).map Prod.snd = .ok []");
        claims.Add($"({Run(arguments, "{ memory with cells := fun _ _ => ⟨0, false⟩ }")}).map " +
            $"(fun result => [(result.1.cells 0 16).initialized, (result.1.cells 0 {15 + 2 * width}).initialized, " +
            $"(result.1.cells 0 {16 + 2 * width}).initialized]) = .ok [true, true, false]");
    }
    if (name == "Vector128")
        claims.Add($"(match {Run(Args(".v128Low64 7"))} with | .error _ => true | .ok _ => false) = true");
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        /-- Successful observations identify the checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- Writable caller storage includes sentinel bytes outside the filled view. -/
        def memory : CIL.Safety.Memory := { Examples.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨256, 16, []⟩, true, [256]⟩ else none
          cells := fun _ offset => ⟨if 16 ≤ offset && offset < 48 then 7 else 11, true⟩
          views := [⟨0, 0, 256, true, true⟩]
          nextIdentity := 1 }
        /-- Compiled fills preserve masks, neighboring cells and checked write requirements. -/
        """ + "\ntheorem correctness :\n" + string.Join(" ∧\n", claims) +
        " := by\n  repeat' apply And.intro\n" +
        "  all_goals first | decide +kernel | (apply result_of_toOption; decide +kernel)\n" +
        "#print axioms correctness\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output), () => Console.WriteLine("PASS aggregate fill: " + name));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
foreach (var (name, before, after, theorem) in new[]
{
    ("Words", ".spanFill 32 false", ".spanFill 16 false", "method0_layouts_validated"),
    ("Words", ".spanFill 32 false", ".spanFill 32 true", "method0_scalars_validated"),
    ("Vector128", ".spanFill 16 false", ".spanFill 32 false", "method0_scalars_validated")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), theorem);
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing fill mutation");
    var path = Path.Combine(root, "Rejected" + name + theorem + ".lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS aggregate fill evidence rejection: " + name,
        theorem.EndsWith("layouts_validated", StringComparison.Ordinal) ? "MethodLayoutsValid" : "ScalarFlowValid");
}
rejected.Check();
