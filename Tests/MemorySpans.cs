#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using Mono.Cecil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/MemorySpans");
Directory.CreateDirectory(root);
foreach (var mutation in new[] { "scope", "version" })
{
    var output = Path.Combine(root, "Rejected-ReadonlyModifier-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var read = module.GetType("Examples.MemorySpans").Methods.Single(method => method.Name == "Read");
        var getter = (MethodReference)read.Body.Instructions.Single(instruction =>
            instruction.Operand is MethodReference { Name: "get_Item" }).Operand;
        if (getter.ReturnType is not RequiredModifierType modifier ||
            modifier.ModifierType.FullName != "System.Runtime.InteropServices.InAttribute" ||
            modifier.ModifierType.Scope is not AssemblyNameReference originalScope)
            throw new InvalidOperationException("Missing readonly span modifier fixture");
        var forgedScope = new AssemblyNameReference(mutation == "scope" ? "Forged.Runtime" : originalScope.Name,
            mutation == "version" ? new Version(9, 0, 0, 0) : originalScope.Version)
        {
            PublicKeyToken = originalScope.PublicKeyToken,
            Culture = originalScope.Culture
        };
        module.AssemblyReferences.Add(forgedScope);
        modifier.ModifierType.Scope = forgedScope;
        module.Write(dll);
    }
    File.Delete(Path.Combine(output, "Extracted.lean"));
    var result = Execute(["dotnet", ExtractorPath, "extract", dll,
        "MemorySpans::Read(System.ReadOnlySpan`1<System.Int32>,System.Int32)", output]);
    if (result.Code == 0 || File.Exists(Path.Combine(output, "Extracted.lean")) ||
        !result.Output.Contains("Unsupported type identity: System.Runtime.InteropServices.InAttribute",
            StringComparison.Ordinal))
        throw new InvalidOperationException("Readonly modifier identity was not rejected: " + mutation +
            "\n" + result.Output);
    Console.WriteLine("PASS readonly span modifier identity rejection: " + mutation);
}
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
var spanProofs = new Dictionary<string, string>(StringComparer.Ordinal);
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution");

foreach (var (name, signature, arguments, expected) in new[]
{
    ("SliceRead", "System.ReadOnlySpan`1<System.Int32>,System.Int32,System.Int32,System.Int32",
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 3, 4, false⟩, .scalar (.i32 1), " +
        ".scalar (.i32 2), .scalar (.i32 0)]", 9),
    ("SliceWrite", "System.Span`1<System.Int32>,System.Int32,System.Int32,System.Int32,System.Int32",
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 3, 4, true⟩, .scalar (.i32 1), " +
        ".scalar (.i32 2), .scalar (.i32 0), .scalar (.i32 11)]", 11),
    ("Existing", "System.Int32&,System.Int32,System.Int32",
        "[.reference (.address ⟨0, 0⟩), .scalar (.i32 3), .scalar (.i32 1)]", 7),
    ("ArraySliceWrite", "System.Int32[],System.Int32,System.Int32,System.Int32",
        "[.array ⟨.address ⟨0, 0⟩, 3, .signed32⟩, .scalar (.i32 1), " +
        ".scalar (.i32 2), .scalar (.i32 11)]", 11)
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"MemorySpans::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def spanMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨12, 1, []⟩, true, []⟩ else none
          cells := fun _ offset => ⟨if offset == 4 then 7 else 0, true⟩
          views := [⟨0, 0, 12, true, true⟩]
          nextIdentity := 1 }

        theorem compiled_span_result :
            (CIL.Safety.invoke Extracted.program 64 0 {{arguments}} spanMemory).map Prod.snd =
              .ok [.scalar (.i32 {{expected}})] := rfl
        #print axioms compiled_span_result
        """);
    spanProofs.Add(name, proof);
}

var original = File.ReadAllText(Path.Combine(root, "SliceRead", "Extracted.lean"));
foreach (var (name, signature, width, arguments, expected) in new[]
{
    ("NativeRead", "System.ReadOnlySpan`1<System.IntPtr>,System.Int32", 8,
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 2, 8, false⟩, .scalar (.i32 1)]", ".i64 7"),
    ("NativeWrite", "System.Span`1<System.UIntPtr>,System.Int32,System.UIntPtr", 8,
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 2, 8, true⟩, .scalar (.i32 1), .scalar (.i64 11)]", ".i64 11"),
    ("CharacterWrite", "System.Span`1<System.Char>,System.Int32,System.Char", 2,
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 2, 2, true⟩, .scalar (.i32 1), .scalar (.i32 65535)]", ".i32 65535"),
    ("BooleanWrite", "System.Span`1<System.Boolean>,System.Int32,System.Boolean", 1,
        "[.bufferSpan ⟨.address ⟨0, 0⟩, 2, 1, true⟩, .scalar (.i32 1), .scalar (.i32 1)]", ".i32 1")
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"MemorySpans::{name}({signature})", output]);
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, File.ReadAllText(Path.Combine(output, "Extracted.lean")) + $$"""

        private def primitiveMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨{{2 * width}}, 1, []⟩, true, []⟩ else none
          cells := fun _ offset => ⟨if offset == {{width}} then 7 else 0, true⟩
          views := [⟨0, 0, {{2 * width}}, true, true⟩]
          nextIdentity := 1 }

        theorem compiled_primitive_span_result :
            (CIL.Safety.invoke Extracted.program 64 0 {{arguments}} primitiveMemory).map Prod.snd =
              .ok [.scalar ({{expected}})] := rfl
        #print axioms compiled_primitive_span_result
        """);
    if (name == "BooleanWrite")
        File.AppendAllText(proof, """

            -- Boolean storage is a byte; it does not imply canonical zero-or-one contents.
            theorem compiled_boolean_raw_byte :
                (CIL.Safety.invoke Extracted.program 64 0
                  [.bufferSpan ⟨.address ⟨0, 0⟩, 2, 1, true⟩,
                    .scalar (.i32 1), .scalar (.i32 2)] primitiveMemory).map Prod.snd =
                  .ok [.scalar (.i32 2)] := rfl
            #print axioms compiled_boolean_raw_byte
            """);
    spanProofs.Add(name, proof);
}

var argumentStart = original.IndexOf("def method0RawArguments :", StringComparison.Ordinal);
foreach (var (name, signature, element, width, writable, range) in new[]
{
    ("ArrayWritable", "System.Int32[]", "signed32", 4, true, 0),
    ("ArrayReadOnly", "System.Int32[]", "signed32", 4, false, 0),
    ("ArrayConstructor", "System.Char[]", "character", 2, true, 0),
    ("ArrayRange", "System.Int32[],System.Int32,System.Int32", "signed32", 4, false, 2),
    ("ArrayAsSpan", "System.Boolean[]", "boolean", 1, true, 0),
    ("ArrayAsSpanStart", "System.IntPtr[],System.Int32", "nativeInt", 8, true, 1),
    ("ArrayAsSpanRange", "System.UIntPtr[],System.Int32,System.Int32", "nativeUInt", 8, true, 2)
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"MemorySpans::{name}({signature})", output]);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var capability = writable ? "true" : "false";
    var suffix = range == 0 ? "" : range == 1 ? ", .scalar (.i32 1)" : ", .scalar (.i32 1), .scalar (.i32 2)";
    var zeros = string.Concat(Enumerable.Repeat(", .scalar (.i32 0)", range));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def arrayMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨{{3 * width}}, 1, []⟩, true, []⟩ else none
          cells := fun _ _ => ⟨0, false⟩
          views := []
          nextIdentity := 1 }

        -- Forming a view needs neither initialized bytes nor write authority.
        theorem compiled_array_span_result :
            (CIL.Safety.invoke Extracted.program 64 0
              [.array ⟨.address ⟨0, 0⟩, 3, .{{element}}⟩{{suffix}}] arrayMemory).map Prod.snd =
              .ok [.bufferSpan ⟨.address ⟨0, {{(range == 0 ? 0 : width)}}⟩,
                {{(range == 0 ? 3 : 2)}}, {{width}}, {{capability}}⟩] := rfl
        #print axioms compiled_array_span_result

        theorem compiled_null_array_span :
            (CIL.Safety.invoke Extracted.program 64 0
              [.reference .null{{zeros}}] arrayMemory).map Prod.snd =
              .ok [.bufferSpan ⟨.null, 0, {{width}}, {{capability}}⟩] := rfl
        #print axioms compiled_null_array_span
        """);
    if (range > 0)
    {
        var tail = range == 1 ? "" : ", .scalar (.i32 0)";
        File.AppendAllText(proof, $$"""

            theorem compiled_empty_end_slice :
                (CIL.Safety.invoke Extracted.program 64 0
                  [.array ⟨.address ⟨0, 0⟩, 3, .{{element}}⟩,
                    .scalar (.i32 3){{tail}}] arrayMemory).map Prod.snd =
                  .ok [.bufferSpan ⟨.address ⟨0, {{3 * width}}⟩, 0,
                    {{width}}, {{capability}}⟩] := rfl
            #print axioms compiled_empty_end_slice

            theorem compiled_negative_start :
                (CIL.Safety.invoke Extracted.program 64 0
                  [.array ⟨.address ⟨0, 0⟩, 3, .{{element}}⟩,
                    .scalar (.i32 (-1)){{tail}}] arrayMemory).map Prod.snd =
                  .error ⟨0, {{range + 1}}, .thrown "System.ArgumentOutOfRangeException"⟩ := rfl
            #print axioms compiled_negative_start

            theorem compiled_null_invalid_start :
                (CIL.Safety.invoke Extracted.program 64 0
                  [.reference .null, .scalar (.i32 1){{tail}}] arrayMemory).map Prod.snd =
                  .error ⟨0, {{range + 1}}, .thrown "System.ArgumentOutOfRangeException"⟩ := rfl
            #print axioms compiled_null_invalid_start
            """);
    }
    if (range == 2)
    {
        File.AppendAllText(proof, $$"""

            theorem compiled_overflowing_range :
                (CIL.Safety.invoke Extracted.program 64 0
                  [.array ⟨.address ⟨0, 0⟩, 3, .{{element}}⟩,
                    .scalar (.i32 2147483647), .scalar (.i32 2147483647)] arrayMemory).map Prod.snd =
                  .error ⟨0, {{range + 1}}, .thrown "System.ArgumentOutOfRangeException"⟩ := rfl
            #print axioms compiled_overflowing_range

            theorem compiled_negative_length :
                (CIL.Safety.invoke Extracted.program 64 0
                  [.array ⟨.address ⟨0, 0⟩, 3, .{{element}}⟩,
                    .scalar (.i32 0), .scalar (.i32 (-1))] arrayMemory).map Prod.snd =
                  .error ⟨0, {{range + 1}}, .thrown "System.ArgumentOutOfRangeException"⟩ := rfl
            #print axioms compiled_negative_length

            theorem expired_array_is_not_a_range_exception :
                (CIL.Safety.memoryInstruction (.arraySpan .{{element}} {{capability}} .counted)
                  [.scalar (.i32 0), .scalar (.i32 0), .array ⟨.address ⟨0, 0⟩, 3, .{{element}}⟩]
                  { arrayMemory with
                    allocations := fun _ => some ⟨.callerStack, ⟨{{3 * width}}, 1, []⟩, false, []⟩
                  }).map Prod.snd =
                  .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 0) := rfl
            #print axioms expired_array_is_not_a_range_exception
            """);
    }
    spanProofs.Add(name, proof);
    if (name == "ArrayReadOnly")
    {
        foreach (var (mutation, before, after) in new[]
        {
            ("array-element", ".arraySpan .signed32 false .whole", ".arraySpan .unsigned32 false .whole"),
            ("array-writability", ".arraySpan .signed32 false .whole", ".arraySpan .signed32 true .whole")
        })
        {
            if (!source.Contains(before, StringComparison.Ordinal)) throw new Exception("Missing " + mutation);
            var forged = Path.Combine(root, "Forged-" + mutation + ".lean");
            File.WriteAllText(forged, source.Replace(before, after, StringComparison.Ordinal));
            rejected.Add(forged, "PASS independent span call rejection: " + mutation,
                "Extraction.ScalarFlowValid method0Closed method0FeatureStates method0ScalarStates method0.code");
        }
    }
}

if (argumentStart < 0) throw new Exception("Missing span argument evidence");
var argumentEnd = original.IndexOf('\n', argumentStart);
var argumentDefinition = original[argumentStart..argumentEnd];
foreach (var (name, before, after) in new[]
{
    ("element-width", ".span 4 false", ".span 8 false"),
    ("write-authority", ".span 4 false", ".span 4 true")
})
{
    if (!argumentDefinition.Contains(before, StringComparison.Ordinal))
        throw new Exception("Missing span argument mutation: " + name);
    var proof = Path.Combine(root, "Forged-" + name + ".lean");
    // Keep both raw methods intact: rejection must bind argument evidence to the closed signature.
    File.WriteAllText(proof, original[..argumentStart] +
        argumentDefinition.Replace(before, after, StringComparison.Ordinal) + original[argumentEnd..]);
    var rejectedGoal = "⊢ Extraction.closedArguments rawLayouts method0Closed = some method0RawArguments";
    rejected.Add(proof, "PASS independent span evidence rejection: " + name, rejectedGoal);
}
rejected.Check();

RequireLeanFixtures("CIL.Safety.MethodContract", "CIL.Safety.BufferContents");
foreach (var (method, proof) in new[]
{
    ("SliceRead", "Tests/MemorySpanContracts.lean"),
    ("SliceWrite", "Tests/MemorySpanWriteContracts.lean")
})
{
    // The contract import also checks the concrete execution theorem, so this extraction
    // does not need a second certificate proof in the later positive batch.
    var contractOutput = Path.Combine(root, method, "Contract");
    Directory.CreateDirectory(contractOutput);
    var contractExtraction = Path.Combine(contractOutput, "Extracted.lean");
    File.Copy(spanProofs[method], contractExtraction, overwrite: true);
    var checkedExtraction = Run(["lake", "env", "lean", "--root=" + contractOutput, "-o",
        Path.Combine(contractOutput, "Extracted.olean"), contractExtraction], cwd: FixturePackage());
    if (checkedExtraction.Contains("sorryAx", StringComparison.Ordinal))
        throw new Exception("Untrusted span certificate or execution");
    var contracts = Run(["lake", "env", "lean", At(proof)], cwd: FixturePackage(), leanPath: contractOutput);
    if (contracts.Contains("sorryAx", StringComparison.Ordinal)) throw new Exception("Untrusted span contract");
    spanProofs.Remove(method);
    Console.WriteLine("PASS compiled span certificate and execution: " + method);
}
Console.WriteLine("PASS compiled span helper contract and caller composition");

foreach (var (signature, marker) in new[]
{
    ("ByRefSpan(System.Span`1<System.Int32>&)", "Unsupported by-reference span"),
    ("FloatingSpan(System.ReadOnlySpan`1<System.Double>)", "Unsupported type"),
    ("InPlaceArrayConstructor(System.Int32[],System.Int32,System.Int32)", "Unsupported in-place span constructor")
})
{
    var result = Execute(["dotnet", ExtractorPath, "extract", assembly, "MemorySpans::" + signature,
        Path.Combine(root, "Rejected-" + signature.Split('(')[0])]);
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.Ordinal))
        throw new Exception("Incorrect unsupported span signature rejection: " + signature + "\n" + result.Output);
    Console.WriteLine("PASS unsupported span signature: " + signature);
}

foreach (var (name, proof) in spanProofs)
    evidence.Add(proof, "PASS compiled span certificate and execution: " + name);
evidence.Check();

