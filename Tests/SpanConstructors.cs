#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
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
// The fixtures whose generated model fact is stated, at the pc of their construction or Empty read.
string[] modelled = ["Single", "ReadOnlySingle", "Aggregate", "Pointer", "AggregateLocal", "Empty", "ReadOnlyEmpty"];
var modelSites = modelled.ToDictionary(name => name, name =>
{
    var code = metadata.GetType("Examples.SpanConstructors").Methods.Single(method => method.Name == name)
        .Body.Instructions;
    return code.IndexOf(code.Single(instruction => instruction.OpCode.Code is Code.Newobj or Code.Call &&
        instruction.Operand is MethodReference { Name: ".ctor" or "get_Empty" }));
}, StringComparer.Ordinal);
foreach (var method in metadata.GetType("Examples.SpanConstructors").Methods.Where(method => method.IsPublic))
foreach (var profile in method.Name == "LayoutLocal" ? new[] { "x64-sse42", "arm64-advsimd" } : ["scalar"])
{
    var name = method.Name;
    var width = name switch
    {
        "Aggregate" or "AggregateLocal" or "Pointer" or "ReadOnlyEmpty" or "ReadOnlyDefaultReset" => 32,
        "Vector" or "VectorPointer" => 16,
        "LayoutLocal" => profile == "x64-sse42" ? 64 : 48,
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
    File.WriteAllText(proof, "import Extracted\nimport CIL.Safety.Execution\nnamespace ExampleProof\n" + """
        /-- View construction needs live storage but neither readable bytes nor byte authority. -/
        def memory : CIL.Safety.Memory := { CIL.Safety.Memory.empty with
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
            .error (.thrown .indexOutOfRange) := by rfl
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
            .error (.thrown .argumentOutOfRange) := by rfl
        #print axioms negative
        """ : "") + "\nend ExampleProof\n");
    if (modelSites.TryGetValue(name, out var modelPc))
    {
        var capability = writable ? "true" : "false";
        var form = empty ? "spanEmpty" : counted ? "spanFromReference" : "spanSingleReference";
        File.AppendAllText(proof, StatedModelFact(modelPc, $".memory (.{form} {width} {capability})"));
    }
    queue.Add(new(method.FullName, proof, output, Profile: profile),
        () => Console.WriteLine("PASS span constructor: " + name + " (" + profile + ")"));
}
queue.Flush();
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
{
    // A reset and an in-place constructor take their width from the home's slot, whose kind the closed
    // method's declared locals fix.
    const string name = "DefaultReset";
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")),
        "method0_specialization_validated");
    const string kinds = "locals := [.span 4 true, .span 4 true]";
    var changed = source.Replace(kinds, "locals := [.span 8 true, .span 4 true]", StringComparison.Ordinal);
    if (changed == source) throw new InvalidOperationException("Missing span local kinds");
    var path = Path.Combine(root, "DefaultResetRejected.lean");
    File.WriteAllText(path, changed);
    rejected.Add(path, "PASS span home width rejection",
        ClosedArgumentsMismatch);
}
{
    // The checked layouts give an in-place constructor its width, so the site admits only the modelled call.
    const string name = "LayoutLocal-x64-sse42";
    var body = metadata.GetType("Examples.SpanConstructors").Methods.Single(method => method.Name == "LayoutLocal")
        .Body;
    var pc = body.Instructions.IndexOf(body.Instructions.Single(instruction =>
        instruction.OpCode.Code == Code.Call && instruction.Operand is MethodReference { Name: ".ctor" }));
    var source = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var path = Path.Combine(root, "LayoutLocalRejected.lean");
    File.WriteAllText(path, ForgeConstructorOpcode(source, pc));
    rejected.Add(path, "PASS forged in-place constructor refused", "RuntimeModelsAgree", "is false");
}
// Each forgery changes the width or capability of a generated model fact, so it elaborates exactly when the
// runtime table resolves the site to the forged model.
foreach (var (name, model) in new[]
{
    ("Single", ".memory (.spanSingleReference 8 true)"), ("ReadOnlySingle", ".memory (.spanSingleReference 4 true)"),
    ("Aggregate", ".memory (.spanSingleReference 24 true)"), ("Pointer", ".memory (.spanFromReference 16 true)"),
    ("AggregateLocal", ".memory (.spanSingleReference 16 false)"),
    ("AggregateLocal", ".memory (.spanSingleReference 32 true)"),
    ("Empty", ".memory (.spanEmpty 8 true)"), ("ReadOnlyEmpty", ".memory (.spanEmpty 32 true)"),
    ("ReadOnlyEmpty", ".memory (.spanEmpty 24 false)")
})
{
    var source = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var path = Path.Combine(root, $"{name}-{model}-rejected.lean");
    File.WriteAllText(path, ForgeModelFact(source, modelSites[name], model));
    rejected.Add(path, $"PASS forged span model fact refused: {name} {model}", ModelFactMismatch(modelSites[name]));
}
{
    // The constructor operand must retain its original opcode.
    var source = File.ReadAllText(Path.Combine(root, "Single", "Extracted.lean"));
    var path = Path.Combine(root, "Single-substituted-rejected.lean");
    File.WriteAllText(path, ForgeConstructorOpcode(source, modelSites["Single"]));
    rejected.Add(path, "PASS substituted constructor opcode refused: Single", "RuntimeModelsAgree", "is false");
}
{
    // A reset takes its width from its home and its operand from the decoded body, so a forged element identity
    // names no operand the body decodes.
    const string name = "ReadOnlyDefaultReset";
    var source = NarrowEvidence(File.ReadAllText(Path.Combine(root, name, "Extracted.lean")),
        "method0_scalars_validated");
    var operand = source.Split('\n').Single(line => line.StartsWith("def valueType0 :", StringComparison.Ordinal));
    var changed = source.Replace(operand,
        AggregateIdentity.Replace(operand, ".aggregate \"Wrong.Identity\" 0"), StringComparison.Ordinal);
    if (changed == source) throw new InvalidOperationException("Missing aggregate identity: " + name);
    var path = Path.Combine(root, name + "IdentityRejected.lean");
    File.WriteAllText(path, changed);
    rejected.Add(path, "PASS empty span identity rejection: " + name,
        "cil_decoded_method: the decoded method has no type operand");
}
rejected.Check();

foreach (var mutation in new[] { "reset-scope", "reset-unscoped", "reset-interior" })
{
    using var altered = ModuleDefinition.ReadModule(assembly);
    var method = altered.GetType("Examples.SpanConstructors").Methods.Single(method => method.Name == "DefaultReset");
    var reset = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Initobj);
    if (mutation is "reset-scope" or "reset-unscoped")
    {
        var original = (GenericInstanceType)reset.Operand;
        // The forged scope is written as an AssemblyRef row; a null scope needs an ExportedType row the image lacks.
        AssemblyNameReference? scope = null;
        if (mutation == "reset-scope")
        {
            scope = new AssemblyNameReference("System.Runtime", new Version(9, 0, 0, 0));
            altered.AssemblyReferences.Add(scope);
        }
        var owner = new TypeReference("System", "Span`1", altered, scope, true);
        var changed = new GenericInstanceType(owner);
        changed.GenericArguments.Add(original.GenericArguments[0]);
        reset.Operand = changed;
    }
    else
    {
        // The branch carries the same home the fall-through path pushes, so only the reset's target check refuses it.
        var processor = method.Body.GetILProcessor();
        var address = processor.Create(OpCodes.Ldloca_S, (VariableDefinition)reset.Previous.Operand);
        processor.InsertBefore(method.Body.Instructions[0], address);
        processor.InsertAfter(address, processor.Create(OpCodes.Br, reset));
    }
    var path = Path.Combine(root, mutation + ".dll");
    altered.Write(path);
    var result = Execute(Extract("extract", path, null, method.FullName, Path.Combine(root, mutation)));
    var expected = mutation switch
    {
        "reset-interior" => "Unsupported span reset",
        "reset-unscoped" => "Unresolved aggregate",
        _ => "Unsupported type identity"
    };
    if (result.Code == 0 || !result.Output.Contains(expected, StringComparison.Ordinal))
        throw new InvalidOperationException("Wrong empty span rejection: " + result.Output);
    Console.WriteLine("PASS empty span extraction rejection: " + mutation);
}

partial class Program
{
    [GeneratedRegex(@"\.aggregate ""[^""]+"" 0")]
    private static partial Regex AggregateIdentity { get; }
}
