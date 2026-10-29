#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Text.Json;
using Mono.Cecil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/AggregateArrays");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var methods = metadata.GetType("Examples.AggregateArrays").Methods.Where(method => method.IsPublic).ToArray();
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
CheckLeanFixture("Tests.AggregateArrayStorage");
ExtractBatch("extract", null, methods.Select(method => new GeneratedExtraction(assembly,
    method.FullName, Path.Combine(root, method.Name))));
foreach (var method in methods)
{
    var name = method.Name;
    var vector = name.Contains("Vector", StringComparison.Ordinal);
    var aggregateIdentity = metadata.Assembly.Name.FullName + "::Examples.AggregateArrays/Pair";
    if (name == "ReadGeneric")
    {
        var owner = (GenericInstanceType)((ArrayType)method.Parameters[0].ParameterType).ElementType;
        var argument = owner.GenericArguments[0];
        aggregateIdentity = metadata.Assembly.Name.FullName + "::" + owner.ElementType.FullName + "<" +
            ((AssemblyNameReference)argument.Scope).FullName + "::" + argument.FullName + ">";
    }
    var element = vector ? ".vector \"System.Runtime.Intrinsics.Vector128`1<System.UInt64>\" 16"
        : ".aggregate " + JsonSerializer.Serialize(aggregateIdentity) + " 16";
    var array = $".array ⟨.address ⟨0, 0⟩, 2, ({element})⟩";
    var store = name.StartsWith("Write", StringComparison.Ordinal);
    var indexed = store || name.StartsWith("Read", StringComparison.Ordinal) && name != "ReadOnlyView" || name == "Address";
    var value = vector ? ".v128 0" : ".aggregate (List.replicate 16 0)";
    var arguments = array + (indexed ? ", .scalar (.i32 1)" : "") +
        (store ? $", .scalar ({value})" : "") +
        (name is "Slice" or "ConstructedLength" ? ", .scalar (.i32 1), .scalar (.i32 1)" : "");
    var expected = name switch
    {
        "Address" => ".reference (.address ⟨0, 16⟩)", "Data" => ".reference (.address ⟨0, 0⟩)",
        "View" or "VectorView" => ".bufferSpan ⟨.address ⟨0, 0⟩, 2, 16, true⟩",
        "ReadOnlyView" => ".bufferSpan ⟨.address ⟨0, 0⟩, 2, 16, false⟩",
        "Slice" => ".bufferSpan ⟨.address ⟨0, 16⟩, 1, 16, true⟩",
        "ConstructedLength" => ".scalar (.i32 1)",
        _ => store ? "" : $".scalar ({value})"
    };
    var source = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        /-- Supplied live array storage; typed views do not create authority. -/
        private def memory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.managedHeap, ⟨48, 16, []⟩, true, [48]⟩ else none
          cells := fun _ _ => ⟨0, true⟩
          views := [⟨0, 0, 48, true, true⟩]
          nextIdentity := 1 }
        /-- Compiled array operations preserve typed contents and storage identity. -/
        theorem result : (CIL.Safety.invoke Extracted.program 64 0 [{{arguments}}] memory).map
            Prod.snd = .ok [{{expected}}] := by rfl
        #print axioms result
        """);
    evidence.Add(proof, "PASS aggregate array: " + name);
}
foreach (var (name, before, after, theorem) in new[]
{
    ("Read", " 16) false)", " 8) false)", "method0_layouts_validated"),
    ("Read", " 16) false)", " 16) true)", "method0_scalars_validated"),
    ("ReadVector", ".vector " + JsonSerializer.Serialize("System.Runtime.Intrinsics.Vector128`1<System.UInt64>") +
        " 16) false)", ".vector " + JsonSerializer.Serialize("System.Runtime.Intrinsics.Vector128`1<System.Int64>") +
        " 16) false)", "method0_scalars_validated"),
    ("ReadOnlyView", " 16) false .whole)", " 16) true .whole)", "method0_scalars_validated"),
    ("View", " 16) true .whole)", " 8) true .whole)", "method0_layouts_validated")
})
{
    var original = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var source = NarrowEvidence(original, theorem);
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing array mutation: " + name);
    var path = Path.Combine(root, "Rejected" + name + theorem + ".lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS aggregate array evidence rejection: " + name,
        theorem.EndsWith("layouts_validated", StringComparison.Ordinal) ? "MethodLayoutsValid" : "ScalarFlowValid");
}
evidence.Check();
rejected.Check();
