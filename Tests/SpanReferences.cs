#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include ../scripts/BatchVerification.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/SpanReferences");
Directory.CreateDirectory(root);
using var metadata = ModuleDefinition.ReadModule(assembly);
var owner = metadata.GetType("Examples.SpanReferences");
MethodDefinition Method(ModuleDefinition module, string name) =>
    module.GetType("Examples.SpanReferences").Methods.Single(method => method.Name == name);

// Bytes 0..31 hold their own offsets, so every expected value is a closed numeral.
const string memory = """
    /-- Readable and writable caller storage whose byte at offset `i` is `i`. -/
    def memory : CIL.Safety.Memory := { Examples.empty with
      allocations := fun identity => if identity == 0 then
        some ⟨.callerStack, ⟨32, 8, []⟩, true, [32]⟩ else none
      cells := fun _ offset => ⟨BitVec.ofNat 8 offset, true⟩
      views := [⟨0, 0, 32, true, true⟩]
      nextIdentity := 1 }
    /-- The same storage after its owner returned. -/
    def expired : CIL.Safety.Memory := { memory with
      allocations := fun identity => if identity == 0 then
        some ⟨.callerStack, ⟨32, 8, []⟩, false, [32]⟩ else none }
    """;
const string bytes = ".bufferSpan ⟨.address ⟨0, 1⟩, 4, 1, false⟩";
var cases = new (string Name, string Arguments, string Results, string Extra)[]
{
    ("Sum", bytes, ".scalar (.i32 10)", $$"""
        /-- A span over expired storage is rejected when the reference is passed. -/
        theorem expiredStorage : (CIL.Safety.invoke Extracted.program 200 0 [{{bytes}}] expired).map
            Prod.snd = .error ⟨0, 0, .memory .expiredLifetime (.address ⟨0, 1⟩) 0⟩ := by rfl
        #print axioms expiredStorage
        /-- A plain reference is not a span view, so a forged home address cannot be read as one. -/
        theorem forgedHome : (CIL.Safety.invoke Extracted.program 200 0
            [.reference (.address ⟨0, 1⟩)] memory).map Prod.snd = .error ⟨0, 18, .invalidState⟩ := by rfl
        #print axioms forgedHome
        """),
    ("Length", ".bufferSpan ⟨.address ⟨0, 0⟩, 5, 4, false⟩", ".scalar (.i32 5)", ""),
    ("First", ".bufferSpan ⟨.address ⟨0, 4⟩, 2, 4, true⟩", ".scalar (.i32 0x07060504)", ""),
    ("WriteFirst", ".bufferSpan ⟨.address ⟨0, 0⟩, 1, 4, true⟩, .scalar (.i32 7)", "", """
        /-- The element store reaches the caller's storage through the referenced view. -/
        theorem stored : ((CIL.Safety.invoke Extracted.program 64 0
            [.bufferSpan ⟨.address ⟨0, 0⟩, 1, 4, true⟩, .scalar (.i32 7)] memory).map
              fun result => (result.1.cells 0 0, result.1.cells 0 1, result.1.cells 0 4)) =
            .ok (⟨7, true⟩, ⟨0, true⟩, ⟨4, true⟩) := by rfl
        #print axioms stored
        /-- A readonly view yields a readonly element reference, so the store faults. -/
        theorem readOnlyElement : (CIL.Safety.invoke Extracted.program 64 0
            [.bufferSpan ⟨.address ⟨0, 0⟩, 1, 4, false⟩, .scalar (.i32 7)] memory).map Prod.snd =
            .error ⟨0, 4, .memory .unwritable (.address ⟨0, 0⟩) 4⟩ := by rfl
        #print axioms readOnlyElement
        """),
    ("Forward", bytes, ".scalar (.i32 10)", ""),
    ("Tail", bytes, ".scalar (.i32 9)", ""),
    ("Copy", ".bufferSpan ⟨.address ⟨0, 0⟩, 7, 1, false⟩", ".scalar (.i32 7)", ""),
    ("At", ".bufferSpan ⟨.address ⟨0, 0⟩, 4, 1, false⟩, .scalar (.i32 2)", ".scalar (.i32 2)", ""),
    ("Caller", ".array ⟨.address ⟨0, 1⟩, 4, .unsigned8⟩", ".scalar (.i32 10)", ""),
    ("Argument", bytes, ".scalar (.i32 10)", ""),
    ("Temporary", bytes, ".scalar (.i32 9)", ""),
    // Limbs 0 and 3 are the little-endian words at offsets 0 and 24.
    ("Construct", ".bufferSpan ⟨.address ⟨0, 0⟩, 4, 8, false⟩",
        ".scalar (.i64 (0x0706050403020100 + 0x1F1E1D1C1B1A1918))", "")
};
var queue = new GeneratedQueue(verification, assembly);
foreach (var (name, arguments, results, extra) in cases)
{
    var method = owner.Methods.Single(candidate => candidate.Name == name);
    var output = Path.Combine(root, name);
    Directory.CreateDirectory(output);
    var proof = Path.Combine(output, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" + memory +
        "\n/-- A readonly span reference reads and writes exactly as the referenced view. -/\n" +
        $"theorem correctness : (CIL.Safety.invoke Extracted.program 200 0 [{arguments}] memory).map " +
        $"Prod.snd = .ok [{results}] := by rfl\n#print axioms correctness\n" + extra + "\nend ExampleProof\n");
    queue.Add(new(method.FullName, proof, output),
        () => Console.WriteLine("PASS readonly span reference: " + name));
}
var contract = Path.Combine(root, "AtContract");
queue.Add(new(owner.Methods.Single(method => method.Name == "At").FullName,
        At("Tests/SpanReferenceContracts.lean"), contract, Theorem: "Tests.SpanReferenceContracts.read_holds"),
    () => Console.WriteLine("PASS readonly span reference contract: At"));
queue.Flush();

// The raw argument stays a managed reference bound to the closed signature, never a span value.
var rejected = new RejectedEvidence(Path.Combine(root, "RejectedEvidence"));
var source = File.ReadAllText(Path.Combine(root, "Sum", "Extracted.lean"));
const string argumentEvidence = "arguments := [.reference]";
if (!source.Contains(argumentEvidence, StringComparison.Ordinal))
    throw new InvalidOperationException("Missing span reference argument evidence");
var forged = Path.Combine(root, "Forged-argument.lean");
File.WriteAllText(forged, source.Replace(argumentEvidence, "arguments := [.span 1 false]", StringComparison.Ordinal));
rejected.Add(forged, "PASS span reference argument evidence rejection",
    "⊢ Extraction.closedArguments rawLayouts method0Closed = some method0RawArguments");
// A span copy may emit only the empty operation; any load would reinterpret the view as bytes.
var copy = NarrowEvidence(File.ReadAllText(Path.Combine(root, "Copy", "Extracted.lean")),
    "method0_features_validated");
const string copied = "  .arg 0,\n  .nop,";
if (!copy.Contains(copied, StringComparison.Ordinal)) throw new InvalidOperationException("Missing span copy");
var loaded = Path.Combine(root, "Forged-copy.lean");
File.WriteAllText(loaded, copy.Replace(copied, "  .arg 0,\n  .loadScalar 8,", StringComparison.Ordinal));
rejected.Add(loaded, "PASS span copy evidence rejection", "FeatureFlowValid", "is false");
rejected.Check();

foreach (var (name, marker) in new[]
{
    ("Alias", "Unsupported by-reference span"),
    ("Replace", "Unsupported writable by-reference span parameter")
})
{
    var result = Execute(Extract("extract", assembly, null, Method(metadata, name).FullName, Path.Combine(root, name)));
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new InvalidOperationException("Wrong span reference rejection: " + name + "\n" + result.Output);
    Console.WriteLine("PASS span reference signature rejection: " + name);
}

// Each mutation is valid IL that C# never emits for a readonly span parameter.
foreach (var (mutation, marker) in new[]
{
    ("store", "Unsupported store to a span home"),
    ("reset", "Unsupported store to a span home"),
    ("rebind", "Unsupported store to or address of a readonly span reference"),
    ("address", "Unsupported store to or address of a readonly span reference"),
    ("writable", "Unsupported writable by-reference span parameter"),
    ("copy-source", "Unsupported span copy source")
})
{
    using var altered = ModuleDefinition.ReadModule(assembly);
    var method = Method(altered, mutation == "copy-source" ? "Copy" : "Length");
    var parameter = method.Parameters[0];
    var spanType = ((ByReferenceType)parameter.ParameterType).ElementType;
    var processor = method.Body.GetILProcessor();
    var head = method.Body.Instructions[0];
    Instruction[] prefix = mutation switch
    {
        "store" => [processor.Create(OpCodes.Ldarg_0), processor.Create(OpCodes.Ldarg_0),
            processor.Create(OpCodes.Ldobj, spanType), processor.Create(OpCodes.Stobj, spanType)],
        "reset" => [processor.Create(OpCodes.Ldarg_0), processor.Create(OpCodes.Initobj, spanType)],
        "rebind" => [processor.Create(OpCodes.Ldarg_0), processor.Create(OpCodes.Starg_S, parameter)],
        "address" => [processor.Create(OpCodes.Ldarga_S, parameter), processor.Create(OpCodes.Pop)],
        _ => []
    };
    foreach (var instruction in prefix) processor.InsertBefore(head, instruction);
    if (mutation == "writable")
    {
        parameter.Attributes &= ~ParameterAttributes.In;
        parameter.CustomAttributes.Clear();
    }
    if (mutation == "copy-source")
        processor.InsertAfter(head, processor.Create(OpCodes.Nop));
    var path = Path.Combine(root, mutation + ".dll");
    altered.Write(path);
    var result = Execute(Extract("extract", path, null, method.FullName, Path.Combine(root, "Rejected-" + mutation)));
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new InvalidOperationException("Wrong span reference rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS span reference extraction rejection: " + mutation);
}
