#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AllowUnsafeBlocks=true
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include GeneratedEvidence.cs

using System.Reflection;

var assembly = At("Examples/Assembly/bin/Examples.dll");
var root = At("artifacts/PointerOperations");
Directory.CreateDirectory(root);
var evidence = new GeneratedEvidence(root);
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
    var rejection = Execute(["lake", "env", "lean", forged], cwd: FixturePackage());
    if (rejection.Code == 0 || !rejection.Output.Contains("ScalarFlowValid", StringComparison.Ordinal))
        throw new Exception("Forged difference was not rejected by scalar evidence: " + rejection.Output);
    Console.WriteLine("PASS independent forged pointer difference rejection");
}

evidence.Check(replay: false);
