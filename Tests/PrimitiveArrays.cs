#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs

using System.Reflection;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/PrimitiveArrays");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root, args.Contains("--measure", StringComparer.Ordinal));
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
foreach (var (type, element, width) in elements)
{
    var values = Array.CreateInstance(type, 2);
    var value = type == typeof(nint) ? (object)(nint)1 : type == typeof(nuint) ? (nuint)1 :
        Convert.ChangeType(1, type);
    runtime.GetMethod("Write" + type.Name)!.Invoke(null, [values, 1, value]);
    var actual = runtime.GetMethod("Read" + type.Name)!.Invoke(null, [values, 1]);
    if (!Equals(actual, value)) throw new Exception("Runtime array mismatch: " + type);
    foreach (var store in new[] { false, true })
    {
        var name = (store ? "Write" : "Read") + type.Name;
        var signature = $"{type.FullName}[],System.Int32" + (store ? $",{type.FullName}" : "");
        var output = Path.Combine(root, name);
        Run(["dotnet", ExtractorPath, "extract", assembly, $"PrimitiveArrays::{name}({signature})", output]);
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
        foreach (var replacement in new[] { ".arrayLoad 1 false", ".arrayLoad 2 true" })
        {
            const string target = ".arrayLoad 1 true";
            if (!source.Contains(target, StringComparison.Ordinal)) throw new Exception("Missing mutation target");
            var forged = Path.Combine(root, "ForgedArray.lean");
            File.WriteAllText(forged, source.Replace(target, replacement, StringComparison.Ordinal));
            var rejection = Execute(["lake", "env", "lean", forged], cwd: FixturePackage());
            if (rejection.Code == 0 || !rejection.Output.Contains("ScalarFlowValid", StringComparison.Ordinal))
                throw new Exception("Forged array operation was not rejected: " + rejection.Output);
        }
    }
}
foreach (var (name, signature, arguments, expected) in new[]
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
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"PrimitiveArrays::{name}({signature})", output]);
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
evidence.Check();
foreach (var signature in new[]
{
    "Allocate(System.Int32)", "ReadObject(System.Object[],System.Int32)",
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
