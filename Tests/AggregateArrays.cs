#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;

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
var pairIdentity = metadata.Assembly.Name.FullName + "::Examples.AggregateArrays/Pair";
foreach (var method in methods)
{
    var name = method.Name;
    var vector = name.Contains("Vector", StringComparison.Ordinal);
    var aggregateIdentity = pairIdentity;
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
    AddResult(name, File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), arguments, expected);
}
// A readonly prefix makes the struct element address read-only; the next loop forges its flag.
var readOnlyAssembly = Path.Combine(root, "ReadOnlyAddress.dll");
using (var module = ModuleDefinition.ReadModule(assembly))
{
    var address = module.GetType("Examples.AggregateArrays").Methods.Single(method => method.Name == "Address");
    var element = address.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Ldelema);
    address.Body.GetILProcessor().InsertBefore(element, Instruction.Create(OpCodes.Readonly));
    module.Write(readOnlyAssembly);
}
Run(["dotnet", ExtractorPath, "extract", readOnlyAssembly,
    "AggregateArrays::Address(Examples.AggregateArrays/Pair[],System.Int32)", Path.Combine(root, "ReadOnlyAddress")]);
AddResult("ReadOnlyAddress", File.ReadAllText(Path.Combine(root, "ReadOnlyAddress", "Extracted.lean")),
    $".array ⟨.address ⟨0, 0⟩, 2, (.aggregate {JsonSerializer.Serialize(pairIdentity)} 16)⟩, .scalar (.i32 1)",
    ".readOnlyReference (.address ⟨0, 16⟩)");

void AddResult(string name, string source, string arguments, string expected)
{
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        /-- A successful observation identifies the exact checked execution result. -/
        private theorem result_of_toOption {error value : Type} {result : Except error value}
            {expected : value} (observed : result.toOption = some expected) : result = .ok expected := by
          cases result <;> simp_all [Except.toOption]
        #print axioms result_of_toOption
        /-- Supplied live array storage; typed views do not create authority. -/
        private def memory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.managedHeap, ⟨48, 16, []⟩, true, [48]⟩ else none
          cells := fun _ _ => ⟨0, true⟩
          views := [⟨0, 0, 48, true, true⟩]
          nextIdentity := 1 }
        /-- Compiled array operations preserve typed contents and storage identity. -/
        theorem result : (CIL.Safety.invoke Extracted.program 64 0 [{{arguments}}] memory).map
            Prod.snd = .ok [{{expected}}] := by apply result_of_toOption; decide +kernel
        #print axioms result
        """);
    evidence.Add(proof, "PASS aggregate array: " + name);
}
var pairToken = ".type (.aggregate " + JsonSerializer.Serialize(pairIdentity) + " ";
foreach (var (name, before, after, theorem) in new[]
{
    // A typed element access is decoded from its body, so a forgery names another element at its raw token, which
    // the certified stack states bind; the element's width is the one its checked layout gives.
    ("Read", "/Pair\" 0) }", "/Other\" 0) }", "method0_scalars_validated"),
    // The raw token names the struct's checked layout by index, which the layout coverage binds.
    ("Read", pairToken + "0)", pairToken + "1)", "method0_coverage_validated"),
    ("ReadVector", "\"System.UInt64\")) }", "\"System.Int64\")) }", "method0_scalars_validated"),
    // The address flag is decoded from the raw prefix, so a writable forgery drops the prefix from the raw body,
    // which its bytes bind.
    ("ReadOnlyAddress", "opcode := 65054, operand := .none }", "opcode := 0, operand := .none }",
        "method0_body_validated")
})
{
    var original = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    if (name is "Read" or "ReadVector" or "ReadOnlyAddress" &&
        !original.Contains("cil_decoded_method method0 ", StringComparison.Ordinal))
        throw new Exception("Typed element access is not decoded from its body: " + name);
    var source = NarrowEvidence(original, theorem);
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing array mutation: " + name);
    Reject(name, theorem, source.Replace(before, after, StringComparison.Ordinal));
}
// A span over an array is a kept call whose runtime model forms the view from the checked layout. A view forged at
// the decoded call, pc 1, is refused by the scalar flow when it is writable and by the model agreement when narrower.
var pairElement = ".aggregate " + JsonSerializer.Serialize(pairIdentity);
foreach (var (name, view, theorem) in new[]
{
    ("ReadOnlyView", $".arraySpan ({pairElement} 16) true .whole", "method0_scalars_validated"),
    ("View", $".arraySpan ({pairElement} 8) true .whole", "method0_models_validated")
})
{
    var original = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var forged = ForgeDecodedInstruction(original, 0, 1, $"fun _ => .memory ({view})");
    Reject(name, theorem, NarrowEvidence(forged, theorem));
}
evidence.Check();
rejected.Check();

void Reject(string name, string theorem, string source)
{
    var path = Path.Combine(root, "Rejected" + name + theorem + ".lean");
    File.WriteAllText(path, source);
    rejected.Add(path, "PASS aggregate array evidence rejection: " + name, theorem switch
    {
        "method0_layouts_validated" => "MethodLayoutsValid",
        "method0_coverage_validated" => "LayoutUsesComplete",
        "method0_body_validated" => "the decoded method does not match its body bytes or metadata",
        "method0_models_validated" => "RuntimeModelsAgree",
        _ => "ScalarFlowValid"
    });
}
