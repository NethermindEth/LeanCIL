#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/WideProduct");
const string selector = "WideProduct::BigMul(ulong,ulong,ulong&)";
verification.Verify(assembly, "Examples", selector, At("Examples/Proofs/BigMul.lean"), Path.Combine(root, "Universal"));
Console.WriteLine("PASS universal compiled BigMul high/low contract");
var output = Path.Combine(root, "Boundaries");
Directory.CreateDirectory(output);
var claims = new List<string>();
ulong[] values = [0, 1, 2, uint.MaxValue, 1UL << 32, long.MaxValue, 1UL << 63, ulong.MaxValue];
foreach (var left in values)
foreach (var right in values)
{
    var high = Math.BigMul(left, right, out var low);
    var exact = (UInt128)left * right;
    if (low != (ulong)exact || high != (ulong)(exact >> 64)) throw new Exception("Runtime product mismatch");
    claims.Add($"(CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 {left}), .scalar (.i64 {right}), Examples.reference] memory).map " +
        $"(fun (final, result) => (result, CIL.Safety.loadValue final (.address ⟨0, 0⟩) 8)) = .ok ([.scalar (.i64 {high})], .ok (.i64 {low}))");
}
var proof = Path.Combine(output, "Proof.lean");
File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
    "def memory : CIL.Safety.Memory := { Examples.caller with cells := fun _ _ => ⟨93, false⟩ }\n" +
    "theorem correctness :\n" + string.Join(" ∧\n", claims) + " := by\n  exact ⟨" + string.Join(", ", claims.Select(_ => "by rfl")) + "⟩\nend ExampleProof\n");
verification.Verify(assembly, "Examples", selector, proof, output);
Console.WriteLine($"PASS {claims.Count} BigMul boundary comparisons with uninitialized output storage");
foreach (var (name, setup, argument, fault) in new[]
{
    ("Null", "Examples.caller", ".reference .null", "⟨0, 3, .memory .nullDereference .null 0⟩"),
    ("Bounds", "{ Examples.caller with allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨4, 1, []⟩, true, [4]⟩ else none, views := [⟨0, 0, 4, true, true⟩] }", "Examples.reference", "⟨0, 3, .memory .outsideAllocation (.address ⟨0, 0⟩) 8⟩"),
    ("Readonly", "{ Examples.caller with views := [⟨0, 0, 8, true, false⟩] }", "Examples.reference", "⟨0, 3, .memory .unwritable (.address ⟨0, 0⟩) 8⟩"),
    ("Expired", "{ Examples.caller with allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨8, 1, []⟩, false, [8]⟩ else none }", "Examples.reference", "⟨0, 0, .memory .expiredLifetime (.address ⟨0, 0⟩) 0⟩")
})
{
    var faultOutput = Path.Combine(root, name);
    Directory.CreateDirectory(faultOutput);
    var faultProof = Path.Combine(faultOutput, "Proof.lean");
    File.WriteAllText(faultProof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        $"def memory : CIL.Safety.Memory := {setup}\n" +
        $"theorem correctness : CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i64 2), .scalar (.i64 3), {argument}] memory = .error {fault} := by rfl\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", selector, faultProof, faultOutput);
    Console.WriteLine("PASS BigMul checked output fault: " + name);
}
foreach (var mutation in new[] { "signed", "return", "out", "instance", "generic", "scope", "version" })
{
    var rejected = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(rejected);
    var dll = Path.Combine(rejected, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.WideProduct").Methods.Single(m => m.Name == "BigMul");
        var call = (MethodReference)method.Body.Instructions.Single(i => i.Operand is MethodReference).Operand;
        switch (mutation)
        {
            case "signed": call.Parameters[0].ParameterType = module.TypeSystem.Int64; break;
            case "return": call.ReturnType = module.TypeSystem.Int64; break;
            case "out": call.Parameters[2].ParameterType = module.TypeSystem.UInt64; break;
            case "instance": call.HasThis = true; break;
            case "generic": call.GenericParameters.Add(new GenericParameter(call)); break;
            case "scope": call.DeclaringType.Scope = module; break;
            case "version": ((AssemblyNameReference)call.DeclaringType.Scope).Version = new Version(9, 0, 0, 0); break;
        }
        module.Write(dll);
    }
    File.Delete(Path.Combine(rejected, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples", selector, rejected));
    if (result.Code == 0 || File.Exists(Path.Combine(rejected, "Extracted.lean"))) throw new Exception("BigMul mutation accepted: " + mutation);
    Console.WriteLine("PASS BigMul rejection: " + mutation);
}
