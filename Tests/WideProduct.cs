#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Numerics;
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

// Signed BigMul(long, long, out long): universal signed high-word contract, runtime boundaries
// against an exact BigInteger product, and the unsigned contract rejected for the signed call.
const string signedSelector = "WideProduct::SignedBigMul(long,long,long&)";
verification.Verify(assembly, "Examples", signedSelector, At("Examples/Proofs/SignedBigMul.lean"),
    Path.Combine(root, "SignedUniversal"));
Console.WriteLine("PASS universal compiled signed BigMul high/low contract with Int recomposition");
var signedOutput = Path.Combine(root, "SignedBoundaries");
Directory.CreateDirectory(signedOutput);
var signedClaims = new List<string>();
long[] signedValues = [0, 1, -1, 2, int.MinValue, uint.MaxValue, long.MaxValue, long.MinValue, -3];
foreach (var left in signedValues)
foreach (var right in signedValues)
{
    var high = Math.BigMul(left, right, out var low);
    var exact = (BigInteger)left * right;
    if (((BigInteger)high << 64) + (ulong)low != exact) throw new Exception("Runtime signed product mismatch");
    signedClaims.Add("(CIL.Safety.invoke Extracted.program 8 0 " +
        $"[.scalar (.i64 {unchecked((ulong)left)}), .scalar (.i64 {unchecked((ulong)right)}), Examples.reference] " +
        "memory).map (fun (final, result) => (result, CIL.Safety.loadValue final (.address ⟨0, 0⟩) 8)) = " +
        $".ok ([.scalar (.i64 {unchecked((ulong)high)})], .ok (.i64 {unchecked((ulong)low)}))");
}
var signedProof = Path.Combine(signedOutput, "Proof.lean");
File.WriteAllText(signedProof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
    "def memory : CIL.Safety.Memory := { Examples.caller with cells := fun _ _ => ⟨93, false⟩ }\n" +
    "theorem correctness :\n" + string.Join(" ∧\n", signedClaims) + " := by\n  exact ⟨" +
    string.Join(", ", signedClaims.Select(_ => "by rfl")) + "⟩\nend ExampleProof\n");
verification.Verify(assembly, "Examples", signedSelector, signedProof, signedOutput);
Console.WriteLine($"PASS {signedClaims.Count} signed BigMul boundary comparisons with uninitialized output storage");
var unsignedForSigned = Path.Combine(root, "SignedRejectsUnsigned");
var unsignedRejected = false;
try
{
    verification.Verify(assembly, "Examples", signedSelector, At("Examples/Proofs/BigMul.lean"), unsignedForSigned);
}
catch (InvalidOperationException error) when (error.Message.Contains("Proof.lean") && error.Message.Contains("error:"))
{
    unsignedRejected = true;
}
if (!unsignedRejected || File.Exists(Path.Combine(unsignedForSigned, "verified.json")))
    throw new Exception("Unsigned high word accepted for signed BigMul");
Console.WriteLine("PASS unsigned high-word contract rejected for signed BigMul");

// BigMul(int, int) and BigMul(uint, uint) return the exact 64-bit product with a long or ulong stack type.
verification.Verify(assembly, "Examples", "WideProduct::BigMul32(int,int)", At("Examples/Proofs/BigMul32.lean"),
    Path.Combine(root, "BigMul32Universal"));
Console.WriteLine("PASS universal exact BigMul(int, int) contract");
int[] intValues = [0, 1, -1, int.MaxValue, int.MinValue, 65536];
uint[] uintValues = [0, 1, 2, uint.MaxValue, 0x80000000, 65536];
foreach (var (gridName, gridSelector, gridClaims) in new (string, string, IEnumerable<string>)[]
{
    ("Signed32", "WideProduct::BigMul32(int,int)",
        intValues.SelectMany(left => intValues.Select(right =>
        "(CIL.Safety.invoke Extracted.program 8 0 " +
        $"[.scalar (.i32 {unchecked((uint)left)}), .scalar (.i32 {unchecked((uint)right)})] " +
        "Examples.empty).map Prod.snd = " +
        $".ok [.scalar (.i64 {unchecked((ulong)Math.BigMul(left, right))})]"))),
    ("Unsigned32", "WideProduct::UnsignedBigMul32(uint,uint)",
        uintValues.SelectMany(left => uintValues.Select(right =>
        $"(CIL.Safety.invoke Extracted.program 8 0 [.scalar (.i32 {left}), .scalar (.i32 {right})] " +
        "Examples.empty).map Prod.snd = " +
        $".ok [.scalar (.i64 {Math.BigMul(left, right)})]")))
})
{
    var gridOutput = Path.Combine(root, gridName);
    Directory.CreateDirectory(gridOutput);
    var list = gridClaims.ToList();
    var gridProof = Path.Combine(gridOutput, "Proof.lean");
    File.WriteAllText(gridProof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        "theorem correctness :\n" + string.Join(" ∧\n", list) + " := by\n  exact ⟨" +
        string.Join(", ", list.Select(_ => "by rfl")) + "⟩\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", gridSelector, gridProof, gridOutput);
    Console.WriteLine($"PASS {list.Count} {gridName} BigMul boundary comparisons against the runtime");
}
