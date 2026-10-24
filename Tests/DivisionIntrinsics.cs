#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs

using System.Reflection;
using System.Text.Json;
using System.Runtime.Intrinsics;
using System.Runtime.Intrinsics.X86;
using Mono.Cecil;

using Program verification = new();
string assembly = At("Examples/Assembly/bin/Examples.dll");
using ModuleDefinition metadata = ModuleDefinition.ReadModule(assembly);
Dictionary<string, string> selectors = metadata.GetType("Examples.DivisionIntrinsics").Methods
    .ToDictionary(method => method.Name, method => method.FullName);
Type runtime = Assembly.LoadFile(assembly).GetType("Examples.DivisionIntrinsics")!;
string root = At("artifacts/DivisionIntrinsics");

foreach (var name in new[] { "DefinedLocal", "PrunedUnsafeLocal" })
{
    var method = metadata.GetType("Examples.DivisionIntrinsics").Methods.Single(method => method.Name == name);
    var local = method.Body.Variables.First(variable => variable.VariableType.FullName ==
        "System.Runtime.Intrinsics.Vector128`1<System.UInt64>").Index;
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, $$"""
import Extracted
import Examples.Support
namespace ExampleProof
theorem byte_homes : Extracted.method0.opaqueVectorLocals = [] := rfl
#print axioms byte_homes
theorem forged_opaque_rejected : ¬ CIL.Extraction.OpaqueLocalsValid Extracted.method0Closed
    { Extracted.method0 with opaqueVectorLocals := [{{local}}] } := by decide +kernel
#print axioms forged_opaque_rejected
theorem correctness :
    (CIL.Safety.invoke Extracted.program 256 0 [.scalar (.i64 7)] Examples.empty).map Prod.snd =
      .ok [.scalar (.i64 14)] := by rfl
#print axioms correctness
end ExampleProof
""");
    verification.Verify(assembly, "Examples", selectors[name], proof, output, profile: "x64-sse42");
    Console.WriteLine("PASS byte-home compatibility and forged opaque rejection: " + name);
}

// Check the boundary fault on actual extracted CIL, including an otherwise valid writable destination.
foreach (var name in new[] { "UnsafeReturn", "UnsafeCall", "UnsafeStore" })
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var arguments = name == "UnsafeStore"
        ? "[.reference (.address ⟨0, 0⟩), .scalar (.i64 7)]" : "[.scalar (.i64 7)]";
    File.WriteAllText(proof, $$"""
import Extracted
namespace ExampleProof
private def memory : CIL.Safety.Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
  cells := fun _ _ => ⟨0, true⟩
  views := [⟨0, 0, 16, true, true⟩]
  nextIdentity := 1 }
theorem correctness :
    ((CIL.Safety.invoke Extracted.program 64 0 {{arguments}} memory).mapError
      (fun fault => fault.fault)).map Prod.snd =
      .error (.unsupported "Instruction observes unspecified vector bits") := by rfl
#print axioms correctness
end ExampleProof
""");
    verification.Verify(assembly, "Examples", selectors[name], proof, output, profile: "x64-v3");
    Console.WriteLine("PASS unspecified vector boundary rejection: " + name);
}

foreach ((string name, ulong left, ulong right, ulong expected, bool wide) in new (string, ulong, ulong, ulong, bool)[]
{
    ("And", 13, 6, 4, false), ("Or", 13, 6, 15, false),
    ("Xor", 13, 6, 11, false), ("AndNot", 1, 3, 2, false),
    ("ShiftLeft", 1, 63, 1UL << 63, false), ("ShiftLeft", 1, 64, 0, false),
    ("ShiftLeft", 1, 256, 0, false), ("ShiftRight", ulong.MaxValue, 1, ulong.MaxValue >> 1, false),
    ("ShiftRight", ulong.MaxValue, ulong.MaxValue, 0, false),
    ("Less", 1, 1UL << 63, 255, true), ("Less", 1UL << 63, 1, 0, true),
    ("Greater", 1UL << 63, 1, 255, true), ("Greater", 1, 1, 0, true)
})
{
    string output = Path.Combine(root, name + "-" + right + "-" + left);
    Directory.CreateDirectory(output);
    string proof = Path.Combine(output, "Proof.lean");
    string word = wide ? "i32" : "i64";
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        (wide ? "private theorem ok_of_toOption {error value : Type} {result : Except error value} {expected : value}\n" +
            "    (observed : result.toOption = some expected) : result = .ok expected := by\n" +
            "  cases result <;> simp_all [Except.toOption]\n" : "") +
        "theorem correctness : (CIL.Safety.invoke Extracted.program 256 0 [.scalar (.i64 " + left +
        "), .scalar (.i64 " + right + ")] Examples.empty).map Prod.snd = .ok [.scalar (." + word + " " + expected +
        ")] := by " + (wide ? "\n  apply ok_of_toOption\n  decide +kernel" : "rfl") + "\nend ExampleProof\n");
    verification.Verify(assembly, "Examples", selectors[name], proof, output, profile: wide ? "x64-v4" : "x64-v3");
    RequireRuntimeGroups(output, wide);
    if (wide ? Avx512DQ.IsSupported && Avx512F.IsSupported : Avx2.IsSupported)
    {
        object result = runtime.GetMethod(name)!.Invoke(null, [left, right])!;
        ulong actual = wide ? (ulong)(int)result : (ulong)result;
        if (actual != expected) throw new InvalidOperationException("Runtime mismatch: " + name);
    }
    Console.WriteLine("PASS compiled division intrinsic: " + name);
}

string rejectedEncoding = Path.Combine(root, "Reject-Vector512Encoding");
Directory.CreateDirectory(rejectedEncoding);
string malformedAssembly = Path.Combine(rejectedEncoding, "Examples.dll");
using (ModuleDefinition module = ModuleDefinition.ReadModule(assembly))
{
    MethodDefinition less = module.GetType("Examples.DivisionIntrinsics").Methods.Single(method => method.Name == "Less");
    MethodReference combine = less.Body.Instructions.Select(instruction => instruction.Operand).OfType<MethodReference>()
        .First(method => method.DeclaringType.FullName == "System.Runtime.Intrinsics.Vector512");
    ((GenericInstanceType)combine.ReturnType).IsValueType = false;
    module.Write(malformedAssembly);
}
File.Delete(Path.Combine(rejectedEncoding, "Extracted.lean"));
(int Code, string Output, string Stdout, string Stderr) rejected = Execute(
    Extract("extract", malformedAssembly, "Examples", selectors["Less"], rejectedEncoding, "x64-v4"));
if (rejected.Code == 0 || File.Exists(Path.Combine(rejectedEncoding, "Extracted.lean")) ||
    !rejected.Output.Contains("Unsupported vector type encoding", StringComparison.Ordinal))
    throw new InvalidOperationException("Malformed Vector512 signature was not rejected by the raw metadata check: " + rejected.Output);
Console.WriteLine("PASS malformed Vector512 signature rejection");

foreach ((string name, int width, object initial) in new (string, int, object)[]
{
    ("Init128", 16, Vector128.Create(ulong.MaxValue)),
    ("Init256", 32, Vector256.Create(ulong.MaxValue)),
    ("Init512", 64, Vector512.Create(ulong.MaxValue))
})
{
    string output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    string proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, $$"""
import Extracted
import Examples.Support
namespace ExampleProof
private def memory (size : Nat) : CIL.Safety.Memory := {
  allocations := fun id => if id = 0 then some ⟨.callerStack, ⟨size, 1, []⟩, true, [size]⟩ else none
  cells := fun _ _ => ⟨255, true⟩
  views := [⟨0, 0, size, true, true⟩]
  nextIdentity := 1 }
theorem correctness :
    (CIL.Safety.invoke Extracted.program 16 0 [Examples.reference] (memory {{width}})).map
      (fun result => ((List.range {{width}}).map (fun offset => result.1.cells 0 offset), result.2)) =
      .ok (List.replicate {{width}} (⟨0, true⟩ : CIL.Safety.Cell), []) ∧
    (CIL.Safety.invoke Extracted.program 16 0 [Examples.reference] (memory {{width - 1}})).map Prod.snd =
      .error ⟨0, 1, .memory .outsideAllocation (.address ⟨0, 0⟩) {{width}}⟩ := by
  exact ⟨rfl, rfl⟩
end ExampleProof
""");
    verification.Verify(assembly, "Examples", selectors[name], proof, output);
    object[] arguments = [initial];
    runtime.GetMethod(name)!.Invoke(null, arguments);
    bool zero = arguments[0] switch
    {
        Vector128<ulong> vector => vector.Equals(Vector128<ulong>.Zero),
        Vector256<ulong> vector => vector.Equals(Vector256<ulong>.Zero),
        Vector512<ulong> vector => vector.Equals(Vector512<ulong>.Zero),
        _ => false
    };
    if (!zero) throw new InvalidOperationException("Runtime vector initialization did not clear every lane: " + name);
    Console.WriteLine("PASS vector initialization, exact zero bytes and bounds: " + name);
}

// .NET 10 reports AVX2 only with BMI1/BMI2 and AVX-512 F/DQ/VL only together; any other profile certifies no runtime.
static void RequireRuntimeGroups(string output, bool wide)
{
    using JsonDocument identity = JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "identity.json")));
    JsonElement profile = identity.RootElement.GetProperty("profile");
    bool Flag(string name) => profile.GetProperty(name).GetBoolean();
    bool v3 = Flag("Avx2") && Flag("Bmi1") && Flag("Bmi2");
    bool v4 = Flag("Avx512F") && Flag("Avx512FVL") && Flag("Avx512DQ") && Flag("Avx512DQVL");
    if (!v3 || v4 != wide)
        throw new InvalidOperationException("Division profile matches no .NET 10 x64 ISA level: " + profile);
}
