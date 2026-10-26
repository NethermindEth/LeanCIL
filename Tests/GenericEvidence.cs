#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../Extractor/ExternalIdentityEvidence.cs

using System.Text;
using System.Text.Json;
using Nethermind.LeanCIL;

if (args is not ([] or ["--external-identities"] or ["--measure"]))
    throw new ArgumentException("Usage: GenericEvidence.cs [--external-identities|--measure]");
var output = At("artifacts/GenericEvidence");
Directory.CreateDirectory(output);
var rejected = new RejectedEvidence(output);
var evidence = new GeneratedEvidence(output, args.Contains("--measure", StringComparer.Ordinal));
CheckExternalIdentities();
if (args is ["--external-identities"]) return;
RequireLeanFixtures("CIL.Extraction.Translation", "CIL.SymbolicExecution", "CIL.Safety.Execution");
var assembly = At("Examples/Assembly/bin/Examples.dll");
var samples = new[]
{
    "Identity64(ulong)", "Nested(ulong)", "Repeated(ulong)", "Mixed(int,byte)",
    "Select(bool,ulong,ulong)", "PackedSize()", "VectorSize()", "Swap32(int&,int&)",
    "SwapRecord(Examples.PackedLeaf&,Examples.PackedLeaf&)", "EnumIdentity(Examples.Signed8)",
    "NativeIdentity(nint)", "TwoTypes(ulong,uint)", "ClearPacked(uint)",
    "NextPacked(Examples.PackedLeaf&,int)", "Instance(ulong)"
};
foreach (var (selector, index) in samples.Select((selector, index) => (selector, index)))
{
    var folder = Path.Combine(output, index.ToString());
    Run(Extract("extract", assembly, "Examples", "GenericMethods::" + selector, folder));
    evidence.Add(Path.Combine(folder, "Extracted.lean"), "PASS structural specialization " + selector);
}

evidence.Check();
CheckEvidenceBatchFailures();
CheckLeanFixture("Tests.ExtractionGenerics");
CheckExternalCallTargets();
string ChangeDefinition(string source, string name, Func<string, string> change)
{
    var start = source.IndexOf("def " + name + " :", StringComparison.Ordinal);
    if (start < 0) throw new InvalidOperationException("Missing definition " + name);
    var end = source.IndexOf('\n', start);
    return source[..start] + change(source[start..end]) + source[end..];
}
void Reject(int sample, string name, Func<string, string> mutate)
{
    var baseline = File.ReadAllText(Path.Combine(output, sample.ToString(), "Extracted.lean"));
    var source = mutate(baseline);
    if (source == baseline) throw new InvalidOperationException("Mutation did not change source: " + name);
    var path = Path.Combine(output, name + ".lean");
    File.WriteAllText(path, source);
    rejected.Add(path, "PASS generic evidence rejects " + name, "error:");
}
foreach (var (name, scope) in new[]
{
    ("wrong-runtime-version", "System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"),
    ("wrong-runtime-token", "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=0000000000000000")
})
    Reject(0, name, source => ChangeDefinition(source, "method1Closed", line =>
        line.Replace("Extraction.runtimeScope", System.Text.Json.JsonSerializer.Serialize(scope))));
Reject(0, "wrong-type-argument", source => ChangeDefinition(source, "method1TypeArgumentsRaw", line => line.Replace("System.UInt64", "System.UInt32")));
Reject(0, "wrong-closed-signature", source => ChangeDefinition(source, "method1Closed", line => line.Replace("System.UInt64", "System.UInt32")));
Reject(7, "wrong-closed-local", source => ChangeDefinition(source, "method1Closed", line => line.Replace("locals := [.atom", "locals := [.byref (.atom").Replace("], initLocals", ")], initLocals")));
Reject(12, "wrong-type-operand", source => ChangeDefinition(source, "method1Closed", line => line.Replace("operand := .type (.aggregate", "operand := .type (.byref (.aggregate").Replace(" 0) }", " 0)) }")));
Reject(0, "altered-opcode", source => ChangeDefinition(source, "method1Closed", line => line.Replace("opcode := 2,", "opcode := 3,")));
Reject(4, "altered-branch", source => ChangeDefinition(source, "method1Closed", line => line.Replace("operand := .target 4", "operand := .target 3")));
Reject(0, "wrong-managed-target", source => source.Replace(".call 1 1", ".call 0 1"));
Console.WriteLine("PASS original-metadata generic substitution, complete managed-call binding and malformed evidence rejection");
Reject(0, "omitted-method-evidence", source => ChangeDefinition(source, "methodEvidence", _ => "def methodEvidence : List Extraction.MethodEvidence := []"));
Reject(0, "reordered-method-evidence", source => ChangeDefinition(source, "methodEvidence", line => line.Replace("method0", "swapped").Replace("method1", "method0").Replace("swapped", "method1")));
Reject(0, "wrong-emitted-return", source => ChangeDefinition(source, "method1", line => line.Replace("returnsValue := true", "returnsValue := false")).Replace("method1.returnsValue = (true)", "method1.returnsValue = (false)"));
Reject(7, "wrong-local-initializer", source => source.Replace("[.i32 0]", "[.i32 1]"));
Reject(7, "wrong-initlocals-flag", source => source.Replace("initLocals := true", "initLocals := false"));
Reject(9, "missing-return-narrowing", source => source.Replace(".ret (some .signed8)", ".ret none"));
Reject(9, "wrong-return-signedness", source => source.Replace(".ret (some .signed8)", ".ret (some .unsigned8)"));

rejected.Check();
void CheckExternalIdentities()
{
    var evidence = new ExternalIdentityEvidence();
    var identities = new[]
    {
        "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a::" +
            "System.UInt64 Namespace.Type::Method(System.UInt64)",
        "Unicode::Namespace.λ漢字::Method(\"quoted\",\\path)",
        "System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=0000000000000000::" +
            "System.UInt64 Namespace.Type::Method(System.UInt64)"
    };
    var lean = new StringBuilder("import Lean\nset_option maxRecDepth 4096\n");
    if (evidence.Reference("unreachable only", false) != JsonSerializer.Serialize("unreachable only"))
        throw new InvalidOperationException("Unreachable identity was materialized.");
    evidence.Emit(lean);
    if (lean.ToString().Contains("externalIdentity", StringComparison.Ordinal))
        throw new InvalidOperationException("Unreachable identity emitted proof declarations.");
    foreach (var (identity, index) in identities.Select((identity, index) => (identity, index)))
    {
        var name = "externalIdentity" + index;
        if (evidence.Reference(identity, true) != name || evidence.Reference(identity, true) != name)
            throw new InvalidOperationException("Exact identity deduplication changed.");
    }
    evidence.Emit(lean);
    var baseline = lean.ToString();
    evidence.Emit(lean);
    if (lean.ToString() != baseline)
        throw new InvalidOperationException("Repeated identity emission duplicated declarations.");
    // Literal equality is an independent encoding oracle, not part of the generated certificate.
    foreach (var (identity, index) in identities.Select((identity, index) => (identity, index)))
    {
        lean.AppendLine($"theorem exactIdentity{index} : externalIdentity{index} = " +
            $"{JsonSerializer.Serialize(identity)} := by rfl");
        lean.AppendLine($"#print axioms exactIdentity{index}");
    }
    baseline = lean.ToString();
    var path = Path.Combine(output, "ExactExternalIdentities.lean");
    File.WriteAllText(path, baseline);
    Run(["lake", "env", "lean", path]);
    var rejectedIdentities = new RejectedEvidence(Path.Combine(output, "IdentityMutations"));
    foreach (var (name, source) in new[]
    {
        ("changed-byte", baseline.Replace("#[83,", "#[84,", StringComparison.Ordinal)),
        ("changed-version", baseline.Replace("Version=10.0.0.0", "Version=11.0.0.0", StringComparison.Ordinal)),
        ("changed-token", baseline.Replace("b03f5f7f11d50a3a", "b03f5f7f11d50a3b", StringComparison.Ordinal))
    })
    {
        if (source == baseline) throw new InvalidOperationException("Identity mutation was not applied: " + name);
        var rejectedPath = Path.Combine(output, "Identity-" + name + ".lean");
        File.WriteAllText(rejectedPath, "import Lean\nnamespace Extracted\n" +
            source.Replace("import Lean\n", "", StringComparison.Ordinal) + "\nend Extracted\n");
        rejectedIdentities.Add(rejectedPath, "PASS exact identity mutation: " + name,
            diagnostic => diagnostic.Contains("rfl", StringComparison.Ordinal) ||
                diagnostic.Contains("Type mismatch", StringComparison.Ordinal));
    }
    rejectedIdentities.Check();
    Console.WriteLine("PASS exact external identities: deduplication, unreachable calls, Unicode and mutations");
}

void CheckEvidenceBatchFailures()
{
    var original = Path.Combine(output, "0", "Extracted.lean");
    var source = File.ReadAllText(original);
    foreach (var (name, suffix, marker) in new[]
    {
        ("invalid-proof", "\ntheorem invalid_evidence : False := by decide +kernel\n" +
            "#print axioms invalid_evidence\n", "error:"),
        ("unchecked-declaration", """

            import Lean
            set_option debug.skipKernelTC true
            run_cmd Lean.Elab.Command.liftCoreM <| Lean.addDecl (.thmDecl {
              name := `forged_evidence
              levelParams := []
              type := Lean.mkConst ``False
              value := Lean.mkConst ``True.intro
            })
            #print axioms forged_evidence
            """, "declaration type mismatch")
    })
    {
        var directory = Path.Combine(output, "BatchFailure-" + name);
        Directory.CreateDirectory(directory);
        var invalid = Path.Combine(directory, "Invalid.lean");
        File.WriteAllText(invalid, source + suffix);
        var rejected = new GeneratedEvidence(directory);
        rejected.Add(original, "Unexpected success before rejected evidence");
        rejected.Add(invalid, "Unexpected invalid evidence success");
        var command = name == "unchecked-declaration" ? "leanchecker PositiveBatch" : "lake env lean";
        try
        {
            rejected.Check();
            throw new Exception("Invalid generated evidence batch was accepted: " + name);
        }
        catch (InvalidOperationException exception) when (
            exception.Message.Contains(marker, StringComparison.Ordinal) &&
            exception.Message.Contains(command, StringComparison.Ordinal))
        {
            Console.WriteLine("PASS evidence batch rejects " + name);
        }
    }
}

void CheckExternalCallTargets()
{
    var folder = Path.Combine(output, "ExternalCalls");
    Run(Extract("extract", assembly, "Examples", "DivisionIntrinsics::UnsafeEquals(ulong)", folder, "x64-v3"));
    var path = Path.Combine(folder, "Extracted.lean");
    Run(["lake", "env", "lean", path]);
    var baseline = File.ReadAllText(path);
    foreach (var (name, source) in new[]
    {
        ("wrong-raw-target", baseline.Replace("target := .external externalIdentity0",
            "target := .external externalIdentity1", StringComparison.Ordinal)),
        ("wrong-emitted-intrinsic", baseline.Replace(".vector .createScalarUnsafe64",
            ".avx2 .band", StringComparison.Ordinal))
    })
    {
        if (source == baseline) throw new InvalidOperationException("Call mutation was not applied: " + name);
        var rejectedPath = Path.Combine(folder, name + ".lean");
        File.WriteAllText(rejectedPath, source);
        rejected.Add(rejectedPath, "PASS materialized external call rejects " + name,
            "Extraction.DivisionIntrinsicsValid", "is false");
    }
}
