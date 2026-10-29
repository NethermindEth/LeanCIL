#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

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
                      [.reference .null, .scalar (.i32 0)] inputMemory with
                     | .error fault => fault.fault == .thrown "System.NullReferenceException"
                     | .ok _ => false) = true := by decide +kernel
                #print axioms null_array_fault
                theorem array_bounds_fault :
                    (match CIL.Safety.invoke Extracted.program 64 0
                      [.array ⟨.address ⟨0, 0⟩, 2, .signed32⟩, .scalar (.i32 2)] inputMemory with
                     | .error fault => fault.fault == .thrown "System.IndexOutOfRangeException"
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
        if (name != "ReadSByte") continue;
        foreach (var (mutation, replacement) in new[]
            { ("signedness", ".arrayLoad 1 false"), ("width", ".arrayLoad 2 true") })
        {
            const string target = ".arrayLoad 1 true";
            if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing mutation target");
            var forged = Path.Combine(root, "ForgedArray-" + mutation + ".lean");
            File.WriteAllText(forged, source.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS forged array operation: " + replacement, "ScalarFlowValid");
        }
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
                 | .error fault => fault.fault == .thrown "System.OverflowException"
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
    if (name == "Allocate")
    {
        foreach (var (mutation, replacement) in new[]
            { ("element", ".newArray .unsigned32"), ("operation", ".nop") })
        {
            const string target = ".newArray .signed32";
            if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing newarr mutation");
            var forged = Path.Combine(root, "ForgedAllocation-" + mutation + ".lean");
            File.WriteAllText(forged, source.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS forged array allocation: " + mutation, "ScalarFlowValid");
        }
    }
    if (name == "AllocateSigned8")
    {
        var target = $".newArray (.{element})";
        foreach (var (mutation, replacement) in new[]
        {
            ("identity", target.Replace("Examples.Signed8", "Examples.Unsigned8", StringComparison.Ordinal)),
            ("storage", target.Replace(".signed8)", ".unsigned8)", StringComparison.Ordinal)),
            ("width", target.Replace(".signed8)", ".signed16)", StringComparison.Ordinal)),
            ("primitive", ".newArray .signed8")
        })
        {
            if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing enum newarr target");
            var forged = Path.Combine(root, "ForgedEnumAllocation-" + mutation + ".lean");
            File.WriteAllText(forged, source.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS forged enum allocation: " + mutation, "ScalarFlowValid");
        }
    }
    if (name == "AllocatePacked")
    {
        var target = $".newArray (.{element})";
        var identity = System.Text.Json.JsonSerializer.Serialize(runtime.Assembly.FullName + "::Examples.PackedLeaf");
        var otherIdentity = identity.Replace("PackedLeaf", "Leaf", StringComparison.Ordinal);
        var controls = new HashSet<string>(StringComparer.Ordinal);
        foreach (var (mutation, before, after, obligation, diagnostic) in new[]
        {
            ("width", target, target.Replace(" 5)", " 6)", StringComparison.Ordinal),
                "method0_layouts_validated", "MethodLayoutsValid"),
            ("identity", target, target.Replace("PackedLeaf", "Leaf", StringComparison.Ordinal),
                "method0_scalars_validated", "ScalarFlowValid"),
            ("layout-identity", $".aggregate {identity}", $".aggregate {otherIdentity}",
                "method0_coverage_validated", "LayoutUsesComplete"),
            ("byref-like", $"identity := {identity},", $"identity := {identity}, byRefLike := true,",
                "method0_layouts_validated", "MethodLayoutsValid"),
            ("zero-width", target, target.Replace(" 5)", " 0)", StringComparison.Ordinal),
                "method0_scalars_validated", "ScalarFlowValid"),
            ("oversized", target, target.Replace(" 5)", " 65536)", StringComparison.Ordinal),
                "method0_scalars_validated", "ScalarFlowValid")
        })
        {
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
