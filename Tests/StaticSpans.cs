#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs

using Mono.Cecil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var queue = new GeneratedQueue(verification, assembly);
var root = At("artifacts/StaticSpans");
void Prove(string name, string dll, string selector, string claim)
{
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        "theorem correctness : " + claim + " := by rfl\nend ExampleProof\n");
    queue.Add(new(selector, proof, output, Assembly: dll),
        () => Console.WriteLine("PASS checked static byte span: " + name));
}
string Result(string value) => $"(CIL.Safety.invoke Extracted.program 16 0 [] Examples.empty).map Prod.snd = {value}";
Prove("First", assembly, "StaticSpans::First()", Result(".ok [.scalar (.i32 1)]"));
Prove("Last", assembly, "StaticSpans::Last()", Result(".ok [.scalar (.i32 16)]"));
Prove("PastEnd", assembly, "StaticSpans::PastEnd()",
    Result(".error ⟨0, 4, .memory .outsideAllocation (.address ⟨0, 16⟩) 1⟩"));
Prove("Write", assembly, "StaticSpans::Write()",
    Result(".error ⟨0, 3, .memory .unwritable (.address ⟨0, 0⟩) 1⟩"));

// The proved value must come from the assembly's RVA blob, so changing the blob changes the theorem.
var tampered = Path.Combine(root, "Tampered", "Examples.dll");
Directory.CreateDirectory(Path.GetDirectoryName(tampered)!);
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var blob = module.Types.Single(t => t.Name == "<PrivateImplementationDetails>").Fields.Single(f => f.InitialValue.Length == 16);
    var bytes = blob.InitialValue.ToArray();
    bytes[0] = 99;
    blob.InitialValue = bytes;
    module.Write(tampered);
}
Prove("Tampered", tampered, "StaticSpans::First()", Result(".ok [.scalar (.i32 99)]"));

queue.Flush();

// Spans are accepted only as a by-value return; every other position or identity stays rejected.
var byteSpan = "Unsupported type: System.ReadOnlySpan`1<System.Byte>";
foreach (var (mutation, marker) in new[]
{
    ("element", "Unsupported type: System.ReadOnlySpan`1<System.Double>"), ("scope", "Unresolved aggregate"),
    ("value-type", "Unsupported type identity"), ("byref-return", byteSpan), ("parameter", byteSpan), ("local", byteSpan)
})
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var owner = module.GetType("Examples.StaticSpans");
        var getter = owner.Methods.Single(m => m.Name == "get_Lookup");
        var entry = owner.Methods.Single(m => m.Name == "First");
        var span = (GenericInstanceType)getter.ReturnType;
        switch (mutation)
        {
            case "element": span.GenericArguments[0] = module.TypeSystem.Double; break;
            case "scope": span.ElementType.Scope = new AssemblyNameReference("Foreign.Runtime", new Version(10, 0, 0, 0)); break;
            case "value-type": span.IsValueType = false; break;
            case "byref-return": getter.ReturnType = new ByReferenceType(span); break;
            case "parameter": entry.Parameters.Add(new ParameterDefinition(span)); break;
            case "local": entry.Body.Variables.Add(new Mono.Cecil.Cil.VariableDefinition(span)); break;
        }
        selector = entry.FullName;
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(Extract("extract", dll, "Examples", selector, output));
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new InvalidOperationException($"Static span mutation {mutation} was not rejected with '{marker}':\n{result.Output}");
    Console.WriteLine("PASS static span rejection: " + mutation);
}
