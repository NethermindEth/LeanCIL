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
#:include BulkCallEvidence.cs
#:include RejectedEvidence.cs

using System.Globalization;
using System.Reflection;
using Mono.Cecil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/PrimitiveArrays");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root, args.Contains("--measure", StringComparer.Ordinal));
var rejected = new RejectedEvidence(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.PrimitiveArrays")!;
RequireLeanFixtures("CIL.Extraction.Translation", "Tests.PrimitiveArrays");
var elements = new (Type Type, string Lean, int Width)[]
{
    (typeof(sbyte), "signed8", 1), (typeof(byte), "unsigned8", 1),
    (typeof(short), "signed16", 2), (typeof(ushort), "unsigned16", 2),
    (typeof(int), "signed32", 4), (typeof(uint), "unsigned32", 4),
    (typeof(long), "signed64", 8), (typeof(ulong), "unsigned64", 8),
    (typeof(nint), "nativeInt", 8), (typeof(nuint), "nativeUInt", 8),
    (typeof(bool), "boolean", 1), (typeof(char), "character", 2)
};
var accessors = elements.SelectMany(element => new[] { false, true }.Select(store =>
    (element.Type, element.Lean, element.Width, Store: store,
        Name: (store ? "Write" : "Read") + element.Type.Name,
        Signature: $"{element.Type.FullName}[],System.Int32" + (store ? $",{element.Type.FullName}" : ""))))
    .ToArray();
ExtractBatch("extract", null, accessors.Select(accessor => new GeneratedExtraction(assembly,
    $"PrimitiveArrays::{accessor.Name}({accessor.Signature})", Path.Combine(root, accessor.Name))));
foreach (var accessorsByType in accessors.GroupBy(accessor => accessor.Type))
{
    var type = accessorsByType.Key;
    var values = Array.CreateInstance(type, 2);
    var value = type == typeof(nint) ? (object)(nint)1 : type == typeof(nuint) ? (nuint)1 :
        Convert.ChangeType(1, type);
    runtime.GetMethod("Write" + type.Name)!.Invoke(null, [values, 1, value]);
    var actual = runtime.GetMethod("Read" + type.Name)!.Invoke(null, [values, 1]);
    if (!Equals(actual, value)) throw new Exception("Runtime array mismatch: " + type);
    foreach (var (_, element, width, store, name, _) in accessorsByType)
    {
        var output = Path.Combine(root, name);
        var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
        var scalar = width == 8 ? "i64" : "i32";
        var arguments = $".array ⟨.address ⟨0, 0⟩, 2, .{element}⟩, .scalar (.i32 1)" +
            (store ? $", .scalar (.{scalar} 1)" : "");
        var observation = store
            ? $"result.2 == [] && (result.1.cells 0 {width}).bits == 1 && " +
                $"(result.1.cells 0 {width}).initialized && (result.1.cells 0 0).bits == 0"
            : $"result.2 == [.scalar (.{scalar} 1)]";
        var proof = Path.Combine(root, name + ".lean");
        File.WriteAllText(proof, source + $$"""

            private def inputMemory : CIL.Safety.Memory := {
              allocations := fun identity => if identity == 0 then
                some ⟨.managedHeap, ⟨{{width * 2}}, 8, []⟩, true, [{{width * 2}}]⟩ else none
              cells := fun _ offset => ⟨{{(store ? "0" : $"if offset == {width} then 1 else 0")}},
                {{(store ? $"!(offset >= {width})" : "true")}}⟩
              views := [⟨0, 0, {{width * 2}}, true, true⟩]
              nextIdentity := 1 }
            theorem array_result :
                (match CIL.Safety.invoke Extracted.program 64 0 [{{arguments}}] inputMemory with
                 | .ok result => {{observation}}
                 | .error _ => false) = true := by decide +kernel
            #print axioms array_result
            """);
        if (name == "ReadInt32")
        {
            File.AppendAllText(proof, """

                theorem null_array_fault :
                    (match CIL.Safety.invoke Extracted.program 64 0
                      [.object .null, .scalar (.i32 0)] inputMemory with
                     | .error fault => fault.fault == .thrown .nullReference
                     | .ok _ => false) = true := by decide +kernel
                #print axioms null_array_fault
                theorem array_bounds_fault :
                    (match CIL.Safety.invoke Extracted.program 64 0
                      [.array ⟨.address ⟨0, 0⟩, 2, .signed32⟩, .scalar (.i32 2)] inputMemory with
                     | .error fault => fault.fault == .thrown .indexOutOfRange
                     | .ok _ => false) = true := by decide +kernel
                #print axioms array_bounds_fault
                """);
            foreach (var (input, index, exception) in new (int[]? Input, int Index, Type Exception)[]
                { (null, 0, typeof(NullReferenceException)), (new int[2], 2, typeof(IndexOutOfRangeException)) })
            {
                try
                {
                    runtime.GetMethod(name)!.Invoke(null, [input, index]);
                    throw new Exception("Expected runtime array fault");
                }
                catch (TargetInvocationException fault) when (fault.InnerException?.GetType() == exception) { }
            }
        }
        evidence.Add(proof, "PASS runtime, certificate and checked array execution: " + name);
        // The decoder reads each element access from the body, so no emitted kind is left to forge; the
        // mutations of Tests/ValueDecoding.lean reject another sign or width at the opcode.
        if (!source.Contains("cil_decoded_method method0 ", StringComparison.Ordinal))
            throw new Exception("Element accessor is not decoded from its body: " + name);
    }
}
var compositions = new (string Name, string Signature, string Arguments, string Expected)[]
{
    ("Length", "System.Int32[]", ".array inputArray", "[.scalar (.i32 2)]"),
    ("ReadHelper", "System.Int32[],System.Int32", ".array inputArray, .scalar (.i32 1)",
        "[.scalar (.i32 1)]"),
    ("ReadGenericHelper", "System.Int32[],System.Int32", ".array inputArray, .scalar (.i32 1)",
        "[.scalar (.i32 1)]"),
    ("WriteGenericHelper", "System.Int32[],System.Int32,System.Int32",
        ".array inputArray, .scalar (.i32 1), .scalar (.i32 7)", "[.scalar (.i32 7)]"),
    ("Identity", "System.Int32[]", ".array inputArray", "[.array inputArray]"),
    ("ReadAlias", "System.Int32[],System.Int32,System.Int32",
        ".array inputArray, .scalar (.i32 1), .scalar (.i32 7)", "[.scalar (.i32 7)]")
};
ExtractBatch("extract", null, compositions.Select(composition => new GeneratedExtraction(assembly,
    $"PrimitiveArrays::{composition.Name}({composition.Signature})", Path.Combine(root, composition.Name))));
foreach (var (name, _, arguments, expected) in compositions)
{
    var output = Path.Combine(root, name);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def inputArray : CIL.Safety.ArrayView := ⟨.address ⟨0, 0⟩, 2, .signed32⟩
        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.managedHeap, ⟨8, 8, []⟩, true, [8]⟩ else none
          cells := fun _ offset => ⟨if offset == 4 then 1 else 0, true⟩
          views := [⟨0, 0, 8, true, true⟩]
          nextIdentity := 1 }
        theorem array_composition :
            (match CIL.Safety.invoke Extracted.program 128 0 [{{arguments}}] inputMemory with
             | .ok result => result.2 == {{expected}}
             | .error _ => false) = true := by decide +kernel
        #print axioms array_composition
        """);
    evidence.Add(proof, "PASS certified array composition: " + name);
}
var allocations = new List<(string Name, string Element, int Width)>
{
    (Name: "Allocate", Element: "signed32", Width: 4),
    (Name: "AllocateBytes", Element: "unsigned8", Width: 1),
    (Name: "AllocateShorts", Element: "signed16", Width: 2),
    (Name: "AllocateLongs", Element: "signed64", Width: 8),
    (Name: "AllocateAndWrite", Element: "signed32", Width: 4)
};
foreach (var (name, type, width) in new[]
{
    ("AllocatePacked", "PackedLeaf", 5), ("AllocateNested", "NestedRecord", 32),
    ("AllocatePackedAndWrite", "PackedLeaf", 5)
})
{
    var identity = System.Text.Json.JsonSerializer.Serialize(runtime.Assembly.FullName + "::Examples." + type);
    allocations.Add((name, $"aggregate {identity} {width}", width));
}
allocations.Add(("AllocateVector",
    "vector \"System.Runtime.Intrinsics.Vector256`1<System.UInt64>\" 32", 32));
foreach (var (type, storage, width) in new[]
{
    ("Signed8", "signed8", 1), ("Unsigned8", "unsigned8", 1),
    ("Signed16", "signed16", 2), ("Unsigned16", "unsigned16", 2),
    ("Signed32", "signed32", 4), ("Unsigned32", "unsigned32", 4),
    ("Signed64", "signed64", 8), ("Unsigned64", "unsigned64", 8),
    ("AllocationTag", "unsigned8", 1)
})
{
    var identity = System.Text.Json.JsonSerializer.Serialize(runtime.Assembly.FullName + "::Examples." + type);
    allocations.Add((type == "AllocationTag" ? "AllocateUnnamedZero" : "Allocate" + type,
        $"enumeration {identity} .{storage}", width));
}
ExtractBatch("extract", null, allocations.Select(allocation => new GeneratedExtraction(assembly,
    $"PrimitiveArrays::{allocation.Name}(System.Int32" +
        (allocation.Name.EndsWith("AndWrite", StringComparison.Ordinal) ? ",System.Int32,System.Int32)" : ")"),
    Path.Combine(root, allocation.Name))));
foreach (var (name, element, width) in allocations)
{
    var source = File.ReadAllText(Path.Combine(root, name, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    var composition = name.EndsWith("AndWrite", StringComparison.Ordinal);
    var composite = name is "AllocatePacked" or "AllocateNested" or "AllocateVector";
    var alignment = composite ? 8 : width;
    var observation = composition ? "result.2 == [.scalar (.i32 7)]" : $$"""
        (match result.2 with
        | [.array view] => view.length == 2 && view.elementType == .{{element}} &&
            view.reference != .null && (view.validate result.1).toOption == some () &&
            (result.1.allocations 0).map (fun allocation => allocation.layout.alignment) == some {{alignment}} &&
            (view.read result.1 1).toOption == some (List.replicate {{width}} 0)
        | _ => false)
        """.Replace("\n", "\n        ", StringComparison.Ordinal);
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun _ => none
          cells := fun _ _ => ⟨0, false⟩
          views := []
          nextIdentity := 0 }
        theorem fresh_array_result :
            (match CIL.Safety.invoke Extracted.program 128 0
              [.scalar (.i32 2){{(composition ? ", .scalar (.i32 1), .scalar (.i32 7)" : "")}}]
              inputMemory with
             | .ok result => {{observation}}
             | .error _ => false) = true := by decide +kernel
        #print axioms fresh_array_result
        """);
    if (name is "Allocate" or "AllocatePacked")
    {
        File.AppendAllText(proof, """

            theorem empty_array_is_live :
                (match CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i32 0)] inputMemory with
                 | .ok (memory, [.array view]) => view.reference != .null &&
                     view.length == 0 && (view.validate memory).toOption == some ()
                 | _ => false) = true := by decide +kernel
            #print axioms empty_array_is_live
            theorem negative_array_overflows :
                (match CIL.Safety.invoke Extracted.program 32 0 [.scalar (.i32 (-1))] inputMemory with
                 | .error fault => fault.fault == .thrown .overflow
                 | .ok _ => false) = true := by decide +kernel
            #print axioms negative_array_overflows
            """);
        try
        {
            runtime.GetMethod(name)!.Invoke(null, [-1]);
            throw new Exception("Expected negative array length rejection");
        }
        catch (TargetInvocationException fault) when (fault.InnerException is OverflowException) { }
    }
    // The decoder reads each allocation from the body, so a forgery names another element type at its raw token,
    // which the certified stack states bind.
    if (name is "Allocate" or "AllocateSigned8" or "AllocatePacked" &&
        !source.Contains("cil_decoded_method method0 ", StringComparison.Ordinal))
        throw new Exception("Allocation is not decoded from its body: " + name);
    if (name == "Allocate")
    {
        foreach (var (mutation, replacement) in new[]
            { ("element", ".type (.atom Extraction.runtimeScope \"System.UInt32\")") })
        {
            const string target = ".type (.atom Extraction.runtimeScope \"System.Int32\")";
            if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing newarr mutation");
            var forged = Path.Combine(root, "ForgedAllocation-" + mutation + ".lean");
            File.WriteAllText(forged, source.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS forged array allocation: " + mutation, "ScalarFlowValid");
        }
    }
    if (name == "AllocateSigned8")
    {
        // The token names the enum and its underlying type; its storage is resolved from them.
        var identity = System.Text.Json.JsonSerializer.Serialize(runtime.Assembly.FullName + "::Examples.Signed8");
        const string underlying = ".atom Extraction.runtimeScope \"System.SByte\"";
        var target = $".type (.enum {identity} ({underlying}))";
        foreach (var (mutation, replacement) in new[]
        {
            ("identity", target.Replace("Examples.Signed8", "Examples.Unsigned8", StringComparison.Ordinal)),
            ("underlying", target.Replace("System.SByte", "System.Byte", StringComparison.Ordinal)),
            ("width", target.Replace("System.SByte", "System.Int16", StringComparison.Ordinal)),
            ("primitive", $".type ({underlying})")
        })
        {
            if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing enum newarr target");
            if (replacement == target) throw new Exception("Enum allocation mutation changes nothing: " + mutation);
            var forged = Path.Combine(root, "ForgedEnumAllocation-" + mutation + ".lean");
            File.WriteAllText(forged, source.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS forged enum allocation: " + mutation, "ScalarFlowValid");
        }
    }
    if (name == "AllocatePacked")
    {
        var identity = System.Text.Json.JsonSerializer.Serialize(runtime.Assembly.FullName + "::Examples.PackedLeaf");
        var otherIdentity = identity.Replace("PackedLeaf", "Leaf", StringComparison.Ordinal);
        // The token names the struct by identity and layout index; its stride is the checked layout's.
        var prefix = $".type (.aggregate {identity} ";
        var start = source.IndexOf(prefix, StringComparison.Ordinal);
        if (start < 0) throw new Exception("Missing composite newarr token");
        var index = int.Parse(source.AsSpan(start + prefix.Length,
            source.IndexOf(')', start) - start - prefix.Length), CultureInfo.InvariantCulture);
        var target = $"{prefix}{index})";
        var controls = new HashSet<string>(StringComparer.Ordinal);
        foreach (var (mutation, before, after, obligation, diagnostic) in new[]
        {
            ("identity", target, target.Replace("PackedLeaf", "Leaf", StringComparison.Ordinal),
                "method0_scalars_validated", "ScalarFlowValid"),
            ("index", target, $"{prefix}{index + 1})", "method0_coverage_validated", "LayoutUsesComplete"),
            ("layout-identity", $".aggregate {identity}", $".aggregate {otherIdentity}",
                "method0_coverage_validated", "LayoutUsesComplete")
        })
        {
            if (before == after) throw new Exception("Composite allocation mutation changes nothing: " + mutation);
            var narrowed = NarrowEvidence(source, obligation);
            if (controls.Add(obligation))
                File.AppendAllText(proof,
                    "\n" + CheckedEvidenceControl(source, narrowed, [obligation], controls.Count));
            if (!narrowed.Contains(before, StringComparison.Ordinal))
                throw new Exception("Missing composite allocation mutation: " + mutation);
            var forged = Path.Combine(root, "ForgedCompositeAllocation-" + mutation + ".lean");
            File.WriteAllText(forged, narrowed.Replace(before, after, StringComparison.Ordinal));
            rejected.Add(forged, "PASS forged composite allocation: " + mutation, diagnostic);
        }
    }
    var actual = runtime.GetMethod(name)!.Invoke(null, composition ? [2, 1, 7] : [2]);
    if (composition ? !Equals(actual, 7) : actual is not Array { Length: 2 } values ||
        !Equals(values.GetValue(1), Activator.CreateInstance(values.GetType().GetElementType()!)))
        throw new Exception("Runtime allocation mismatch: " + name);
    evidence.Add(proof, "PASS runtime, certificate and heap array return: " + name);
}
var fillEnum = System.Text.Json.JsonSerializer.Serialize(runtime.Assembly.FullName + "::Examples.AllocationTag");
var fills = new (string Name, string Signature, string Element, int Width, bool Counted)[]
{
    ("FillIntegers", "System.Int32[],System.Int32", "signed32", 4, false),
    ("FillEnums", "Examples.AllocationTag[],Examples.AllocationTag",
        $"enumeration {fillEnum} .unsigned8", 1, false),
    ("FillRangeIntegers", "System.Int32[],System.Int32,System.Int32,System.Int32", "signed32", 4, true),
    ("FillRangeEnums", "Examples.AllocationTag[],Examples.AllocationTag,System.Int32,System.Int32",
        $"enumeration {fillEnum} .unsigned8", 1, true)
};
ExtractBatch("extract", null, fills.Select(fill => new GeneratedExtraction(assembly,
    $"PrimitiveArrays::{fill.Name}({fill.Signature})", Path.Combine(root, fill.Name))));
foreach (var (name, _, element, width, counted) in fills)
{
    var output = Path.Combine(root, name);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, $$"""
        import CIL.Safety.StepComposition
        {{source}}

        private def fillMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.managedHeap, ⟨32, 8, []⟩, true, [32]⟩ else none
          cells := fun _ _ => ⟨11, true⟩
          views := [⟨0, 0, 32, true, true⟩]
          nextIdentity := 1 }
        /-- The generic helper fills both elements and preserves neighboring bytes. -/
        theorem array_fill :
            (match CIL.Safety.invoke Extracted.program 128 0
              [.array ⟨.address ⟨0, {{(counted ? 8 - width : 8)}}⟩, {{(counted ? 4 : 2)}},
                .{{element}}⟩, .scalar (.i32 7){{(counted ? ", .scalar (.i32 1), .scalar (.i32 2)" : "")}}]
              fillMemory with
             | .ok result => result.2 == [] &&
               [7, 7, 11, 11] == [result.1.cells 0 8 |>.bits,
                 result.1.cells 0 {{8 + width}} |>.bits, result.1.cells 0 7 |>.bits,
                 result.1.cells 0 {{8 + 2 * width}} |>.bits]
             | .error _ => false) = true := by decide +kernel
        #print axioms array_fill
        """);
    if (name == "FillRangeIntegers")
    {
        File.AppendAllText(proof, """

            /-- Range filling checks null first and rejects negative or overflowing bounds. -/
            theorem range_fill_faults :
                ([(0, 0), (4, 0)].all fun (start, count) =>
                  match CIL.Safety.invoke Extracted.program 128 0
                    [.array ⟨.address ⟨0, 4⟩, 4, .signed32⟩, .scalar (.i32 7),
                      .scalar (.i32 start), .scalar (.i32 count)] { fillMemory with views := [] } with
                  | .ok result => result.2 == [] | .error _ => false) = true ∧
                ([(-1, 0), (0, -1), (5, 0), (3, 2), (1, 2147483647)].all fun (start, count) =>
                  match CIL.Safety.invoke Extracted.program 128 0
                    [.array ⟨.address ⟨0, 4⟩, 4, .signed32⟩, .scalar (.i32 7),
                      .scalar (.i32 start), .scalar (.i32 count)] fillMemory with
                  | .error fault => fault.fault == .thrown .argumentOutOfRange
                  | .ok _ => false) = true ∧
                ([.object .null, .array ⟨.null, 0, .signed32⟩].all fun input =>
                  match CIL.Safety.invoke Extracted.program 128 0
                    [input, .scalar (.i32 7), .scalar (.i32 (-1)), .scalar (.i32 (-1))] fillMemory with
                  | .error fault => fault.fault == .thrown .argumentNull
                  | .ok _ => false) = true ∧
                (match CIL.Safety.invoke Extracted.program 128 0
                  [.array ⟨.address ⟨0, 4⟩, 4, .signed32⟩, .scalar (.i32 7),
                    .scalar (.i32 1), .scalar (.i32 2)] { fillMemory with views := [] } with
                 | .error _ => true | .ok _ => false) = true := by
              repeat' apply And.intro
              all_goals decide +kernel
            #print axioms range_fill_faults

            /-- Invalid model storage cannot discharge a named runtime exception obligation. -/
            theorem malformed_fill_states :
                ([⟨.address ⟨0, 4⟩, 9, .signed32⟩, ⟨.address ⟨1, 0⟩, 4, .signed32⟩,
                  ⟨.null, 1, .signed32⟩].all fun view =>
                  [false, true].all fun counted =>
                    let operands := [.scalar (.i32 7), .array view]
                    match CIL.Safety.arrayFillInstruction .signed32 counted
                      (if counted then [.scalar (.i32 (-1)), .scalar (.i32 (-1))] ++ operands
                        else operands) fillMemory with
                    | .error (.thrown _) => false | .error _ => true | .ok _ => false) = true ∧
                (match CIL.Safety.arrayFillInstruction .signed32 true
                  [.scalar (.i32 (-1)), .scalar (.i32 (-1)), .scalar (.i32 7),
                    .array ⟨.address ⟨0, 4⟩, 4, .signed32⟩]
                  { fillMemory with allocations := fun identity =>
                      if identity == 0 then some ⟨.managedHeap, ⟨32, 8, []⟩, false, [32]⟩ else none } with
                 | .error (.thrown _) => false | .error _ => true | .ok _ => false) = true := by
              constructor <;> decide +kernel
            #print axioms malformed_fill_states
            """);
        foreach (var (start, count) in new[]
            { (1, 2), (0, 0), (4, 0), (-1, 0), (0, -1), (5, 0), (3, 2), (1, int.MaxValue) })
        {
            var values = new[] { 1, 2, 3, 4 };
            var valid = (uint)start <= values.Length && (uint)count <= values.Length - start;
            try
            {
                runtime.GetMethod(name)!.Invoke(null, [values, 7, start, count]);
                if (!valid || !values.SequenceEqual(start == 1 ? [1, 7, 7, 4] : [1, 2, 3, 4]))
                    throw new Exception("Runtime range fill mismatch");
            }
            catch (TargetInvocationException fault) when (
                !valid && fault.InnerException is ArgumentOutOfRangeException) { }
        }
        try
        {
            runtime.GetMethod(name)!.Invoke(null, [null, 7, -1, -1]);
            throw new Exception("Expected null array fill rejection");
        }
        catch (TargetInvocationException fault) when (fault.InnerException is ArgumentNullException) { }
    }
    else if (name == "FillIntegers")
    {
        File.AppendAllText(proof, """

            /-- Empty arrays require no write authority, while both null representations throw. -/
            theorem empty_and_null_fill :
                (match CIL.Safety.invoke Extracted.program 128 0
                  [.array ⟨.address ⟨0, 8⟩, 0, .signed32⟩, .scalar (.i32 7)]
                  { fillMemory with views := [] } with
                 | .ok result => result.2 == [] | .error _ => false) = true ∧
                ([.object .null, .array ⟨.null, 0, .signed32⟩].all fun input =>
                  match CIL.Safety.invoke Extracted.program 128 0 [input, .scalar (.i32 7)] fillMemory with
                  | .error fault => fault.fault == .thrown .argumentNull
                  | .ok _ => false) = true ∧
                (match CIL.Safety.invoke Extracted.program 128 0
                  [.array ⟨.address ⟨0, 8⟩, 2, .signed32⟩, .scalar (.i32 7)]
                  { fillMemory with views := [⟨0, 0, 32, true, false⟩] } with
                 | .error _ => true | .ok _ => false) = true := by
              repeat' apply And.intro
              all_goals decide +kernel
            #print axioms empty_and_null_fill
            """);
        var values = new[] { 1, 2 };
        runtime.GetMethod(name)!.Invoke(null, [values, 7]);
        if (!values.SequenceEqual([7, 7])) throw new Exception("Runtime array fill mismatch");
        runtime.GetMethod(name)!.Invoke(null, [Array.Empty<int>(), 7]);
        try
        {
            runtime.GetMethod(name)!.Invoke(null, [null, 7]);
            throw new Exception("Expected null array fill rejection");
        }
        catch (TargetInvocationException fault) when (fault.InnerException is ArgumentNullException) { }
    }
    else
    {
        var type = runtime.Assembly.GetType("Examples.AllocationTag")!;
        var values = Array.CreateInstance(type, 2);
        var value = Enum.ToObject(type, 7);
        runtime.GetMethod(name)!.Invoke(null, counted ? [values, value, 0, 2] : [values, value]);
        if (!Equals(values.GetValue(0), value) || !Equals(values.GetValue(1), value))
            throw new Exception("Runtime enum array fill mismatch");
    }
    var shape = element.StartsWith("enumeration", StringComparison.Ordinal) ? $"(.{element})" : $".{element}";
    var mode = counted ? "true" : "false";
    File.AppendAllText(proof, BulkCallEvidence(1, counted ? 4 : 2, $".arrayFill {shape} {mode}"));
    evidence.Add(proof, "PASS generic array fill: " + name);
}
evidence.Check();
rejected.Check();
foreach (var mutation in new[]
    { "byref-like", "supplied-byref-like", "wrong-marker-scope", "vararg-marker", "nested-byref-like", "oversized" })
{
    using var module = ModuleDefinition.ReadModule(assembly);
    var element = module.GetType("Examples.PackedLeaf");
    var signature = "PrimitiveArrays::AllocatePacked(System.Int32)";
    if (mutation == "supplied-byref-like")
    {
        element = module.GetType("Examples.AggregateArrays/Pair");
        signature = "AggregateArrays::Read(Examples.AggregateArrays/Pair[],System.Int32)";
    }
    if (mutation == "oversized") element.ClassSize = ushort.MaxValue + 1;
    else
    {
        var scope = module.AssemblyReferences.Single(reference => reference.Name == "System.Runtime");
        if (mutation == "wrong-marker-scope")
        {
            scope = new AssemblyNameReference("Forged.Runtime", scope.Version);
            module.AssemblyReferences.Add(scope);
        }
        var marker = new TypeReference("System.Runtime.CompilerServices", "IsByRefLikeAttribute", module, scope);
        var constructor = new MethodReference(".ctor", module.TypeSystem.Void, marker) { HasThis = true };
        if (mutation == "vararg-marker") constructor.CallingConvention = MethodCallingConvention.VarArg;
        element.CustomAttributes.Add(new CustomAttribute(constructor));
        if (mutation == "nested-byref-like")
        {
            var pair = module.GetType("Examples.AggregateArrays/Pair");
            pair.Fields.Single(field => field.Name == "First").FieldType = element;
            signature = "AggregateArrays::Read(Examples.AggregateArrays/Pair[],System.Int32)";
        }
    }
    var changed = Path.Combine(root, mutation + ".dll");
    module.Write(changed);
    var result = Execute(Extract("extract", changed, null, signature, Path.Combine(root, mutation)));
    var expected = mutation switch
    {
        "wrong-marker-scope" or "vararg-marker" => "byref-like marker",
        "nested-byref-like" => "Byref-like field",
        "oversized" => "Unsupported instruction",
        _ => "Unsupported array"
    };
    if (result.Code == 0 || !result.Output.Contains(expected, StringComparison.Ordinal))
        throw new Exception("Unexpected composite array rejection: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS unsupported composite array metadata: " + mutation);
}
foreach (var signature in new[]
{
    "AllocateSingles(System.Int32)", "ReadObject(System.Object[],System.Int32)",
    "ReadSingle(System.Single[],System.Int32)", "ReadJagged(System.Int32[][],System.Int32)",
    "ReadRectangular(System.Int32[0...,0...],System.Int32,System.Int32)"
})
{
    var rejection = Execute(["dotnet", ExtractorPath, "extract", assembly,
        "PrimitiveArrays::" + signature, Path.Combine(root, "Rejected")]);
    if (rejection.Code == 0 || !rejection.Output.Contains("unsupported", StringComparison.OrdinalIgnoreCase))
        throw new Exception("Expected unsupported array rejection: " + signature + "\n" + rejection.Output);
    Console.WriteLine("PASS unsupported array rejection: " + signature);
}
