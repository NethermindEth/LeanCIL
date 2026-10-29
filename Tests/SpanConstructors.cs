#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using Mono.Cecil;
using Mono.Cecil.Cil;
using System.Text.RegularExpressions;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/SpanConstructors");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var queue = new GeneratedQueue(verification, assembly);
foreach (var method in metadata.GetType("Examples.SpanConstructors").Methods.Where(method => method.IsPublic))
foreach (var profile in method.Name == "LayoutLocal" ? new[] { "x64-sse2", "arm64-advsimd" } : ["scalar"])
{
    var name = method.Name;
    var width = name switch
    {
        "Aggregate" or "AggregateLocal" or "Pointer" or "ReadOnlyEmpty" or "ReadOnlyDefaultReset" => 32,
        "Vector" or "VectorPointer" => 16,
        "LayoutLocal" => profile == "x64-sse2" ? 64 : 48,
        _ => 4
    };
    var counted = name.Contains("Pointer", StringComparison.Ordinal) || name == "LayoutLocal";
    var writable = name is not ("ReadOnlySingle" or "AggregateLocal" or "Vector" or "VectorPointer" or
        "ReadOnlyEmpty" or "ReadOnlyDefaultReset");
    var length = counted ? 2 : 1;
    var output = Path.Combine(root, name + (profile == "scalar" ? "" : "-" + profile));
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    var empty = name.EndsWith("Empty", StringComparison.Ordinal) || name.EndsWith("Reset", StringComparison.Ordinal);
    var arguments = name.EndsWith("Empty", StringComparison.Ordinal) ? "" :
        ".reference (.address ⟨0, 0⟩)" + (counted ? $", .scalar (.i32 {length})" : "");
    var expected = empty ? $".bufferSpan ⟨.null, 0, {width}, {writable.ToString().ToLowerInvariant()}⟩" :
        name.EndsWith("Local", StringComparison.Ordinal) || name == "Local"
        ? $".scalar (.i32 {length})"
        : $".bufferSpan ⟨.address ⟨0, 0⟩, {length}, {width}, {writable.ToString().ToLowerInvariant()}⟩";
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + """
        /-- View construction needs live storage but neither readable bytes nor byte authority. -/
        def memory : CIL.Safety.Memory := { Examples.empty with
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨128, 16, []⟩, true, [128]⟩ else none
          nextIdentity := 1 }
        /-- Both constructor encodings retain the validated element layout and capability. -/
        """ + $"\ntheorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [{arguments}] memory).map " +
        $"Prod.snd = .ok [{expected}] := by rfl\n#print axioms correctness\n" +
        (name == "Empty" ? """
        /-- No element is addressable through an empty view, regardless of its write capability. -/
        theorem emptyIndex : CIL.Safety.memoryInstruction (.spanItem 4)
            [.scalar (.i32 0), .bufferSpan ⟨.null, 0, 4, true⟩] memory =
            .error (.thrown "System.IndexOutOfRangeException") := by rfl
        #print axioms emptyIndex
        """ : "") + (name == "Single" ? """
        /-- View construction rejects expired storage, even when no bytes are read. -/
        theorem expired : CIL.Safety.memoryInstruction (.spanSingleReference 4 true)
            [.reference (.address ⟨0, 0⟩)]
            { memory with allocations := fun _ => some ⟨.callerStack, ⟨128, 16, []⟩, false, [128]⟩ } =
            .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 4) := by rfl
        #print axioms expired
        /-- An empty pointer span may start at the end of its allocation. -/
        theorem emptyAtEnd : CIL.Safety.memoryInstruction (.spanFromReference 32 true)
            [.scalar (.i32 0), .reference (.address ⟨0, 128⟩)] memory =
            .ok (memory, [.bufferSpan ⟨.address ⟨0, 128⟩, 0, 32, true⟩]) := by rfl
        #print axioms emptyAtEnd
        /-- A one-element view must fit entirely within the allocation. -/
        theorem outside : CIL.Safety.memoryInstruction (.spanSingleReference 32 true)
            [.reference (.address ⟨0, 128⟩)] memory =
            .error (.memory .outsideAllocation (.address ⟨0, 128⟩) 32) := by rfl
        #print axioms outside
        /-- A readonly reference cannot construct a writable view. -/
        theorem readOnly : CIL.Safety.memoryInstruction (.spanSingleReference 4 true)
            [.readOnlyReference (.address ⟨0, 0⟩)] memory = .error .invalidState := by rfl
        #print axioms readOnly
        /-- A negative pointer length raises the specified runtime exception. -/
        theorem negative : CIL.Safety.memoryInstruction (.spanFromReference 32 true)
            [.scalar (.i32 (-1)), .reference (.address ⟨0, 0⟩)] memory =
            .error (.thrown "System.ArgumentOutOfRangeException") := by rfl
        #print axioms negative
        """ : "") + "\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output, Profile: profile),
        () => Console.WriteLine("PASS span constructor: " + name + " (" + profile + ")"));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
foreach (var (name, before, after, theorem, marker) in new[]
{
    ("Empty", ".spanEmpty 4 true", ".spanEmpty 8 true",
        "method0_scalars_validated", "ScalarFlowValid"),
    ("ReadOnlyEmpty", ".spanEmpty 32 false", ".spanEmpty 32 true",
        "method0_scalars_validated", "ScalarFlowValid"),
    ("ReadOnlyEmpty", ".spanEmpty 32 false", ".spanEmpty 24 false",
        "method0_layouts_validated", "MethodLayoutsValid"),
    ("DefaultReset", ".empty 4 true", ".empty 8 true",
        "method0_features_validated", "FeatureFlowValid"),
    ("Single", ".spanSingleReference 4 true", ".spanSingleReference 8 true",
        "method0_scalars_validated", "ScalarFlowValid"),
    ("ReadOnlySingle", ".spanSingleReference 4 false", ".spanSingleReference 4 true",
        "method0_scalars_validated", "ScalarFlowValid"),
    ("Aggregate", ".spanSingleReference 32 true", ".spanSingleReference 24 true",
        "method0_layouts_validated", "MethodLayoutsValid"),
    ("Pointer", ".spanFromReference 32 true", ".spanFromReference 16 true",
        "method0_layouts_validated", "MethodLayoutsValid"),
    ("LayoutLocal-x64-sse2", ".reference 64 true", ".reference 48 true",
        "method0_layouts_validated", "MethodLayoutsValid"),
    ("AggregateLocal", ".spanSingleReference 32 false", ".spanSingleReference 16 false",
        "method0_layouts_validated", "MethodLayoutsValid"),
    ("AggregateLocal", ".spanSingleReference 32 false", ".spanSingleReference 32 true",
        "method0_scalars_validated", "ScalarFlowValid")
})
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")), theorem);
    if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing constructor mutation: " + name);
    var path = Path.Combine(root, name + theorem + "Rejected.lean");
    File.WriteAllText(path, source.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(path, "PASS constructor evidence rejection: " + name, marker, "is false");
}
foreach (var name in new[] { "ReadOnlyEmpty", "ReadOnlyDefaultReset" })
{
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")),
        "method0_coverage_validated");
    var changed = Regex.Replace(source, @"\.aggregate ""[^""]+"" 0", ".aggregate \"Wrong.Identity\" 0");
    if (changed == source) throw new InvalidOperationException("Missing aggregate identity: " + name);
    var path = Path.Combine(root, name + "IdentityRejected.lean");
    File.WriteAllText(path, changed);
    rejected.Add(path, "PASS empty span identity rejection: " + name, "LayoutUsesComplete", "is false");
}
rejected.Check();

foreach (var mutation in new[] { "reset-scope", "reset-interior" })
{
    using var altered = ModuleDefinition.ReadModule(assembly);
    var method = altered.GetType("Examples.SpanConstructors").Methods.Single(method => method.Name == "DefaultReset");
    var reset = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Initobj);
    if (mutation == "reset-scope")
    {
        var original = (GenericInstanceType)reset.Operand;
        var owner = new TypeReference("System", "Span`1", altered,
            new AssemblyNameReference("System.Runtime", new Version(9, 0, 0, 0)), true);
        var changed = new GenericInstanceType(owner);
        changed.GenericArguments.Add(original.GenericArguments[0]);
        reset.Operand = changed;
    }
    else
    {
        var branch = method.Body.Instructions.Single(instruction => instruction.Operand == reset.Previous);
        branch.Operand = reset;
    }
    var path = Path.Combine(root, mutation + ".dll");
    altered.Write(path);
    var result = Execute(Extract("extract", path, null, method.FullName, Path.Combine(root, mutation)));
    var expected = mutation == "reset-interior" ? "Branch into a folded span receiver" :
        "Span default type does not match its local";
    if (result.Code == 0 || !result.Output.Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException("Wrong empty span rejection: " + result.Output);
    Console.WriteLine("PASS empty span extraction rejection: " + mutation);
}
