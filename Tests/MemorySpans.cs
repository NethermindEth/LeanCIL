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
foreach (var mutation in new[] { "alias", "branch" })
{
    var output = Path.Combine(root, "Rejected-Constructor-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.MemorySpans").Methods.Single(method =>
            method.Name == "InPlaceArrayConstructor");
        var head = method.Body.Instructions[0];
        if (head.OpCode.Code is not (Mono.Cecil.Cil.Code.Ldloca or Mono.Cecil.Cil.Code.Ldloca_S))
            throw new InvalidOperationException("Missing in-place constructor receiver");
        var processor = method.Body.GetILProcessor();
        if (mutation == "alias")
            processor.InsertAfter(head, processor.Create(Mono.Cecil.Cil.OpCodes.Dup));
        else
            processor.InsertBefore(head, processor.Create(Mono.Cecil.Cil.OpCodes.Br, head.Next));
        module.Write(dll);
    }
    var result = Execute(["dotnet", ExtractorPath, "extract", dll,
        "MemorySpans::InPlaceArrayConstructor(System.Int32[],System.Int32,System.Int32)", output]);
    var marker = mutation == "alias" ? "Unsupported in-place span constructor" : "folded span";
    if (result.Code == 0 || !result.Output.Contains(marker, StringComparison.OrdinalIgnoreCase))
        throw new InvalidOperationException("Incorrect constructor rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS in-place constructor rejection: " + mutation);
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
        ".scalar (.i32 2), .scalar (.i32 11)]", 11),
    ("InPlaceArrayConstructor", "System.Int32[],System.Int32,System.Int32",
        "[.array ⟨.address ⟨0, 0⟩, 3, .signed32⟩, .scalar (.i32 1), .scalar (.i32 2)]", 7),
    ("InPlaceArrayLength", "System.Int32[],System.Int32,System.Int32",
        "[.reference .null, .scalar (.i32 0), .scalar (.i32 0)]", 0),
    ("ReinitializeArraySpan", "System.Int32[],System.Int32,System.Int32",
        "[.array ⟨.address ⟨0, 0⟩, 3, .signed32⟩, .scalar (.i32 1), .scalar (.i32 2)]", 9),
    ("InPlacePointerSpan", "System.Int32*,System.Int32",
        "[.reference (.address ⟨0, 0⟩), .scalar (.i32 3)]", 3)
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
    if (name == "InPlaceArrayLength")
        File.AppendAllText(proof, """

            theorem constructor_fault_keeps_call_pc :
                (CIL.Safety.invoke Extracted.program 64 0
                  [.reference .null, .scalar (.i32 1), .scalar (.i32 0)] spanMemory).map Prod.snd =
                  .error ⟨0, 4, .thrown "System.ArgumentOutOfRangeException"⟩ := rfl
            #print axioms constructor_fault_keeps_call_pc

            theorem uninitialized_span_local_rejected :
                CIL.Safety.step Extracted.method0 (.local 0) 0 []
                  ⟨0, [.span 4 false none], [], [], 0⟩ [] spanMemory = .error .invalidState := rfl
            #print axioms uninitialized_span_local_rejected

            theorem constructor_expired_storage_rejected :
                CIL.Safety.step Extracted.method0
                  (.initializeSpanLocal 0 (.array .signed32 false .counted)) 4 []
                  ⟨0, [.span 4 false none], [], [], 0⟩
                  [.scalar (.i32 0), .scalar (.i32 0), .array ⟨.address ⟨0, 0⟩, 3, .signed32⟩]
                  { spanMemory with
                    allocations := fun _ => some ⟨.callerStack, ⟨12, 1, []⟩, false, []⟩ } =
                  .error (.memory .expiredLifetime (.address ⟨0, 0⟩) 0) := rfl
            #print axioms constructor_expired_storage_rejected
            """);
    if (name == "InPlaceArrayConstructor")
    {
        const string operation = ".initializeSpanLocal 0 (.array .signed32 true .counted)";
        if (!source.Contains(operation, StringComparison.Ordinal))
            throw new InvalidOperationException("Missing compiled in-place span constructor");
        var forged = Path.Combine(root, "Forged-constructor-local.lean");
        File.WriteAllText(forged, source.Replace(operation,
            ".initializeSpanLocal 1 (.array .signed32 true .counted)", StringComparison.Ordinal));
        rejected.Add(forged, "PASS independent constructor destination rejection",
            "Extraction.FeatureFlowValid rawLayouts.toArray method0Closed");
    }
}

foreach (var (name, signature, width, arguments, bytes) in new[]
{
    ("ClearBytes", "System.Span`1<System.Byte>", 1, "", "[0, 0]"),
    ("FillCharacters", "System.Span`1<System.Char>,System.Char", 2,
        ", .scalar (.i32 4660)", "[52, 18, 52, 18]"),
    ("FillIntegers", "System.Span`1<System.Int32>,System.Int32", 4,
        ", .scalar (.i32 4294967295)", "List.replicate 8 255"),
    ("FillLongSlice", "System.Span`1<System.Int64>,System.Int32,System.Int32,System.Int64", 8,
        ", .scalar (.i32 1), .scalar (.i32 2), .scalar (.i64 9223372036854775808)",
        "[0, 0, 0, 0, 0, 0, 0, 128, 0, 0, 0, 0, 0, 0, 0, 128]")
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"MemorySpans::{name}({signature})", output]);
    var proof = Path.Combine(root, name + ".lean");
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    if (name == "FillIntegers")
    {
        var forged = Path.Combine(root, "Forged-fill-width.lean");
        if (!source.Contains(".spanFill 4 false", StringComparison.Ordinal))
            throw new Exception("Missing fill-width mutation");
        File.WriteAllText(forged, source.Replace(".spanFill 4 false", ".spanFill 8 false",
            StringComparison.Ordinal));
        rejected.Add(forged, "PASS independent span fill width rejection",
            "Extraction.ScalarFlowValid rawLayouts.toArray method0Closed " +
                "method0FeatureStates method0ScalarStates method0.code");
    }
    var start = name == "FillLongSlice" ? width : 0;
    var count = name == "FillLongSlice" ? 4 : 2;
    File.WriteAllText(proof, source + $$"""

        private def fillMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨{{(count + 2) * width}}, 1, []⟩, true, []⟩ else none
          cells := fun _ _ => ⟨99, false⟩
          views := [⟨0, 0, {{(count + 2) * width}}, false, true⟩]
          nextIdentity := 1 }

        theorem compiled_fill_contents :
            (do let (memory, result) ← CIL.Safety.invoke Extracted.program 64 0
                  [.bufferSpan ⟨.address ⟨0, {{width}}⟩, {{count}}, {{width}}, true⟩{{arguments}}]
                  fillMemory
                let contents := CIL.Safety.read memory ⟨0, {{width + start}}⟩ {{2 * width}} 1
                pure (contents, memory.cells 0 {{width + start - 1}},
                  memory.cells 0 {{width + start + 2 * width}}, result)) =
              .ok (.ok ({{bytes}}), ⟨99, false⟩, ⟨99, false⟩, []) := rfl
        #print axioms compiled_fill_contents
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
                "Extraction.ScalarFlowValid rawLayouts.toArray method0Closed " +
                "method0FeatureStates method0ScalarStates method0.code");
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
    ("FloatingSpan(System.ReadOnlySpan`1<System.Double>)", "Unsupported type")
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
