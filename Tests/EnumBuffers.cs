#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var root = At("artifacts/EnumBuffers");
Directory.CreateDirectory(root);
var assembly = Path.Combine(root, "Examples.dll");
using (var module = ModuleDefinition.ReadModule(At("Examples/Assembly/bin/Examples.dll")))
{
    var owner = module.GetType("Examples.EnumBuffers");
    foreach (var name in new[] { "Roundtrip", "Wide" })
    {
        var method = owner.Methods.Single(method => method.Name == name);
        foreach (var instruction in method.Body.Instructions)
        {
            if (instruction.OpCode.Code is Code.Ldelem_I1 or Code.Ldelem_I8)
                instruction.OpCode = OpCodes.Ldelem_Any;
            else if (instruction.OpCode.Code == Code.Stelem_I1) instruction.OpCode = OpCodes.Stelem_Any;
            else continue;
            instruction.Operand = method.ReturnType;
        }
    }
    module.Write(assembly);
}
using var metadata = ModuleDefinition.ReadModule(assembly);
var methods = metadata.GetType("Examples.EnumBuffers").Methods.ToDictionary(method => method.Name);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.EnumBuffers")!;
var small = runtime.GetNestedType("Small")!;
var values = Array.CreateInstance(small, 3);
var minus = Enum.ToObject(small, -1);
var seven = Enum.ToObject(small, 7);
var large = runtime.GetNestedType("Large")!;
var wideValues = Array.CreateInstance(large, 2);
var high = Enum.ToObject(large, 0x8000000000000001UL);
wideValues.SetValue(high, 1);
if (!Equals(runtime.GetMethod("Wide")!.Invoke(null, [wideValues, 1]), high))
    throw new InvalidOperationException("Wide enum runtime read mismatch");
foreach (var name in new[] { "Roundtrip", "Address", "SpanRoundtrip" })
    if (!Equals(runtime.GetMethod(name)!.Invoke(null, [values, 1, minus]), minus))
        throw new InvalidOperationException("Enum runtime roundtrip mismatch: " + name);
if (!Equals(runtime.GetMethod("Loop")!.Invoke(null, [values, 2]), seven))
    throw new InvalidOperationException("Enum runtime loop mismatch");
if (!Equals(runtime.GetMethod("FillClear")!.Invoke(null, [values]), seven) ||
    values.Cast<object>().Any(value => Convert.ToInt32(value) != 0))
    throw new InvalidOperationException("Enum runtime Fill/Clear mismatch");

string Element(string name, string storage) =>
    $".enumeration {JsonSerializer.Serialize(metadata.Assembly.Name.FullName + "::Examples.EnumBuffers/" + name)} " +
    $".{storage}";
var narrow = Element("Small", "signed8");
var wide = Element("Large", "unsigned64");
var array = $".array ⟨.address ⟨0, 0⟩, 3, ({narrow})⟩";
var queue = new GeneratedQueue(verification, assembly);
Run(["lake", "env", "lean", At("Tests/EnumBufferEvidence.lean")], cwd: FixturePackage());
foreach (var (name, arguments, result, width) in new[]
{
    ("Roundtrip", $"[{array}, .scalar (.i32 1), .scalar (.i32 4294967295)]", 4294967295UL, 1),
    ("Address", $"[{array}, .scalar (.i32 1), .scalar (.i32 7)]", 7UL, 1),
    ("SpanRoundtrip", $"[{array}, .scalar (.i32 1), .scalar (.i32 7)]", 7UL, 1),
    ("Loop", $"[{array}, .scalar (.i32 2)]", 7UL, 1),
    ("FillClear", $"[{array}]", 7UL, 1),
    ("Read", "[.bufferSpan ⟨.address ⟨0, 0⟩, 3, 1, false⟩]", 7UL, 1),
    ("Wide", $"[.array ⟨.address ⟨0, 0⟩, 3, ({wide})⟩, .scalar (.i32 1)]", 9223372036854775809UL, 8)
})
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var initialBytes = width == 8 ? "if offset == 8 then 1 else if offset == 15 then 128 else 0" : "7";
    File.WriteAllText(proof, $$"""
        import Extracted
        namespace ExampleProof
        private def memory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.managedHeap, ⟨24, 8, []⟩, true, [24]⟩ else none
          cells := fun _ offset => ⟨{{initialBytes}}, true⟩
          views := [⟨0, 0, 24, true, true⟩]
          nextIdentity := 1 }
        /-- The compiled enum operation agrees with the observed CLR result. -/
        theorem correctness :
            (match CIL.Safety.invoke Extracted.program 256 0 {{arguments}} memory with
             | .ok result => result.2 == [.scalar (.i{{(width == 8 ? 64 : 32)}} {{result}})]
                 {{(name == "FillClear" ? "&& (result.1.cells 0 0).bits == 0 && (result.1.cells 0 2).bits == 0" : "")}}
             | .error _ => false) = true := by decide +kernel
        #print axioms correctness
        end ExampleProof
        """);
    queue.Add(new(methods[name].FullName, proof, output),
        () => Console.WriteLine("PASS enum buffer execution: " + name));
}
queue.Flush();

var rejected = new RejectedEvidence(root);
foreach (var (name, obligation) in new[]
{
    ("Roundtrip", "method0_scalars_validated"), ("SpanRoundtrip", "method0_scalars_validated"),
    ("Loop", "method0_scalars_validated")
})
{
    var baseline = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var control = Path.Combine(root, name + "-control.lean");
    File.WriteAllText(control, NarrowEvidence(baseline, obligation));
    Run(["lake", "env", "lean", control], cwd: verification.CheckoutPackage());
    var marker = "def method0ScalarStates";
    var start = baseline.IndexOf(marker, StringComparison.Ordinal);
    var end = baseline.IndexOf('\n', start);
    var original = baseline[start..end];
    var changed = original.Replace("EnumBuffers/Small", "EnumBuffers/OtherSmall", StringComparison.Ordinal);
    if (changed == original) throw new InvalidOperationException("Missing enum stack identity: " + name);
    var path = Path.Combine(root, name + "-wrong-enum.lean");
    File.WriteAllText(path, NarrowEvidence(baseline[..start] + changed + baseline[end..], obligation));
    rejected.Add(path, "PASS distinct enum identity rejected: " + name,
        "Extraction.ScalarFlowValid", "is false");
}
rejected.Check();
