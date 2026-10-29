#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AllowUnsafeBlocks=true
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs
#:include RejectedEvidence.cs

using System.Reflection;
using Mono.Cecil;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/PointerOperations");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
var rejected = new RejectedEvidence(root);
var runtime = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.PointerOperations")!;
RequireLeanFixtures("CIL.Extraction.Translation", "Tests.PointerOperations");
var storageBytes = new byte[16];
foreach (var name in new[]
    { "Subtract", "SubtractNative", "Difference", "Less", "Greater", "LessEqual", "GreaterEqual" })
{
    var subtraction = name.StartsWith("Subtract", StringComparison.Ordinal);
    var native = name == "SubtractNative";
    var signature = subtraction ? "System.Byte*," + (native ? "System.IntPtr" : "System.Int32") :
        "System.Byte*,System.Byte*";
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"PointerOperations::{name}({signature})", output]);
    var expected = 0L;
    unsafe
    {
        fixed (byte* storage = storageBytes)
        {
            var second = subtraction ? native ? (object)(nint)3 : 3 : Pointer.Box(storage + 2, typeof(byte*));
            var result = runtime.GetMethod(name)!.Invoke(null, [Pointer.Box(storage + 5, typeof(byte*)), second])!;
            expected = subtraction ? (byte*)Pointer.Unbox(result) - storage :
                result is bool condition ? condition ? 1 : 0 : (long)result;
        }
    }
    var arguments = subtraction ? $".scalar (.{(native ? "i64" : "i32")} 3)" :
        ".reference (.address ⟨0, 2⟩)";
    var resultValue = subtraction ? $".reference (.address ⟨0, {expected}⟩)" :
        $".scalar (.{(name == "Difference" ? "i64" : "i32")} {expected})";
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var differenceEvidence = name == "Difference" ? NarrowEvidence(source, "method0_scalars_validated") : null;
    var control = differenceEvidence is null ? "" : CheckedEvidenceControl(source, differenceEvidence,
        ["method0_scalars_validated"], 0);
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨16, 1, []⟩, true, [16]⟩ else none
          cells := fun _ _ => ⟨0, false⟩
          views := []
          nextIdentity := 1 }
        theorem pointer_result :
            CIL.Safety.invoke Extracted.program 64 0
              [.reference (.address ⟨0, 5⟩), {{arguments}}] inputMemory =
              .ok (inputMemory, [{{resultValue}}]) := rfl
        #print axioms pointer_result
        """ + "\n" + control);
    evidence.Add(proof, "PASS runtime, certificate and checked pointer execution: " + name);
    if (name != "Difference") continue;
    if (!source.Contains(".sub", StringComparison.Ordinal)) throw new Exception("Missing difference mutation target");
    var forged = Path.Combine(root, "ForgedDifference.lean");
    File.WriteAllText(forged, differenceEvidence!.Replace(".sub", ".add", StringComparison.Ordinal));
    rejected.Add(forged, "PASS independent forged pointer difference rejection", "ScalarFlowValid");
}

foreach (var (name, parameters) in new[]
{
    ("ReadCharacter", "System.Char*,System.Int32"), ("ReadEnum", "Examples.Signed16*,System.Int32"),
    ("WriteEnum", "Examples.Unsigned64*,System.UInt64")
})
{
    var output = Path.Combine(root, name);
    Run(["dotnet", ExtractorPath, "extract", assembly, $"PointerOperations::{name}({parameters})", output]);
    var write = name == "WriteEnum";
    const ulong highBitValue = 0x8000000000000001;
    var method = runtime.GetMethod(name)!;
    var storage = Enumerable.Repeat((byte)255, 24).ToArray();
    ulong expected;
    unsafe
    {
        fixed (byte* start = storage)
        {
            var result = method.Invoke(null, [Pointer.Box(start, method.GetParameters()[0].ParameterType),
                write ? (object)highBitValue : 1])!;
            expected = write ? (ulong)result : unchecked((uint)Convert.ToInt64(result));
        }
    }
    if (storage[0] != 255 || storage[16] != 255 || write && expected != highBitValue)
        throw new InvalidOperationException("Pointer storage changed neighboring bytes: " + name);
    var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var proof = Path.Combine(root, name + ".lean");
    File.WriteAllText(proof, source + $$"""

        private def inputMemory : CIL.Safety.Memory := {
          allocations := fun identity => if identity == 0 then
            some ⟨.callerStack, ⟨24, 1, []⟩, true, [24]⟩ else none
          cells := fun _ _ => ⟨255, true⟩
          views := [⟨0, 0, 24, true, true⟩]
          nextIdentity := 1 }
        theorem pointer_storage_result :
            ((CIL.Safety.invoke Extracted.program 32 0
              [.reference (.address ⟨0, 0⟩), .scalar (.i{{(write ? 64 : 32)}} {{(write ? highBitValue : 1)}})]
              inputMemory).map (fun result =>
                let first := result.1.cells 0 0
                let last := result.1.cells 0 16
                (result.2, first.bits, first.initialized, last.bits, last.initialized))).toOption =
                some ([.scalar (.i{{(write ? 64 : 32)}} {{expected}})], 255, true, 255, true) :=
          by decide +kernel
        #print axioms pointer_storage_result
        """);
    if (!write)
    {
        var storageEvidence = NarrowEvidence(source, "method0_specialization_validated");
        File.AppendAllText(proof, "\n" + CheckedEvidenceControl(source, storageEvidence,
            ["method0_specialization_validated"], 0));
        var pointee = name == "ReadCharacter" ? "System.Char" : "System.Int16";
        var target = $".atom Extraction.runtimeScope \"{pointee}\"";
        foreach (var (mutation, replacement) in new[]
        {
            ("scope", $".atom \"forged\" \"{pointee}\""),
            ("storage", ".atom Extraction.runtimeScope \"System.Boolean\"")
        })
        {
            if (!storageEvidence.Contains(target, StringComparison.Ordinal))
                throw new InvalidOperationException("Missing pointee storage evidence: " + name);
            var forged = Path.Combine(output, "Forged-" + mutation + ".lean");
            File.WriteAllText(forged, storageEvidence.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS independent pointee storage rejection: " + name + "/" + mutation,
                "closedArguments");
        }
    }
    if (name == "ReadEnum")
    {
        var returnEvidence = NarrowEvidence(source, "method0_shape_validated");
        File.AppendAllText(proof, "\n" + CheckedEvidenceControl(source, returnEvidence,
            ["method0_shape_validated"], 1));
        foreach (var replacement in new[] { ".ret (some .signed8)", ".ret (some .unsigned16)" })
        {
            const string target = ".ret (some .signed16)";
            if (!returnEvidence.Contains(target, StringComparison.Ordinal))
                throw new InvalidOperationException("Missing enum return narrowing");
            var widthChanged = replacement.Contains("signed8", StringComparison.Ordinal);
            var forged = Path.Combine(output, "ForgedReturn" + widthChanged + ".lean");
            File.WriteAllText(forged, returnEvidence.Replace(target, replacement, StringComparison.Ordinal));
            rejected.Add(forged, "PASS independent enum return width/signedness rejection", "MethodShapeValid");
        }
    }
    evidence.Add(proof, "PASS runtime, certificate and checked pointee storage: " + name);
}

foreach (var mutation in new[] { "float", "nested", "reference-field", "enum-storage", "enum-identity", "enum-scope" })
{
    var output = Path.Combine(root, "Reject-" + mutation);
    Directory.CreateDirectory(output);
    var dll = Path.Combine(output, "Examples.dll");
    string selector;
    using (var module = ModuleDefinition.ReadModule(assembly))
    {
        var method = module.GetType("Examples.PointerOperations").Methods.Single(method => method.Name == "ReadEnum");
        var element = module.GetType("Examples.Signed16");
        switch (mutation)
        {
            case "float": method.Parameters[0].ParameterType = new PointerType(module.TypeSystem.Double); break;
            case "nested":
                method.Parameters[0].ParameterType = new PointerType(new PointerType(module.TypeSystem.Int32));
                break;
            case "reference-field":
                var aggregate = module.GetType("Examples.FourLimbs");
                aggregate.Fields[0].FieldType = module.TypeSystem.Object;
                method.Parameters[0].ParameterType = new PointerType(aggregate);
                break;
            case "enum-storage":
                element.Fields.Single(field => !field.IsStatic).FieldType = module.TypeSystem.Boolean;
                break;
            case "enum-identity":
                module.Types.Add(new TypeDefinition("Examples", "Signed16", Mono.Cecil.TypeAttributes.Public));
                break;
            case "enum-scope":
                method.Parameters[0].ParameterType = new PointerType(new TypeReference("Examples", "Signed16", module,
                    module.TypeSystem.Int32.Scope, true));
                break;
        }
        selector = $"PointerOperations::ReadEnum({method.Parameters[0].ParameterType.FullName},System.Int32)";
        module.Write(dll);
    }
    var result = Execute(["dotnet", ExtractorPath, "extract", dll, selector, output]);
    var diagnostic = mutation switch
    {
        "enum-storage" => "Unsupported enum underlying type",
        "enum-identity" => "Unsupported enum metadata",
        "reference-field" => "Unsupported field type",
        _ => "Unsupported stack-storage pointer element type"
    };
    if (result.Code == 0 || !result.Output.Contains(diagnostic, StringComparison.Ordinal) ||
        File.Exists(Path.Combine(output, "Extracted.lean")))
        throw new InvalidOperationException("Unsupported pointee accepted: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS unsupported pointer storage rejected: " + mutation);
}

evidence.Check(replay: false);
rejected.Check();
