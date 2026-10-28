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
var controls = new Dictionary<int, List<string>>();
var controlSources = new HashSet<string>(StringComparer.Ordinal);
CheckExternalIdentities();
if (args is ["--external-identities"])
{
    evidence.Check();
    rejected.Check();
    return;
}
const string controlBaseline = """
    import CIL.Extraction.Translation
    namespace Extracted
    def controlValue : Nat := 1
    def storedName : String := "Extracted.controlValue"
    theorem control_valid : controlValue = 1 := rfl
    #print axioms control_valid
    end Extracted

    """;
var controlPath = Path.Combine(output, "Control-unchanged.lean");
File.WriteAllText(controlPath, controlBaseline + CheckedEvidenceControl(controlBaseline,
    NarrowEvidence(controlBaseline, "control_valid"), ["control_valid"], 0));
evidence.Add(controlPath, "PASS unchanged evidence projection and literal namespace name", "control_valid");
foreach (var (name, declaration, diagnostic) in new[]
{
    ("missing-declaration", "", "Unknown identifier"),
    ("changed-declaration", "def controlValue : Nat := 2\n", "Type mismatch")
})
{
    var narrowed = controlBaseline.Replace("def controlValue : Nat := 1\n", declaration, StringComparison.Ordinal);
    var path = Path.Combine(output, "Control-" + name + ".lean");
    File.WriteAllText(path, controlBaseline + CheckedEvidenceControl(controlBaseline, narrowed, ["control_valid"], 0));
    rejected.Add(path, "PASS checked control rejects " + name, diagnostic);
}
foreach (var (name, declarations) in new[]
{
    ("theorem-dependent-definition", """
        def dependentWitness : controlValue = 1 := control_valid
        theorem second_valid : controlValue = 1 := dependentWitness
        #print axioms second_valid
        """),
    ("theorem-dependent-type", """
        theorem second_valid : control_valid = control_valid := rfl
        #print axioms second_valid
        """)
})
{
    var baseline = controlBaseline.Replace("end Extracted", declarations + "\nend Extracted",
        StringComparison.Ordinal);
    var path = Path.Combine(output, "Control-" + name + ".lean");
    File.WriteAllText(path, baseline + CheckedEvidenceControl(baseline, NarrowEvidence(baseline, "second_valid"),
        ["second_valid"], 0));
    rejected.Add(path, "PASS checked control rejects " + name, "Unknown identifier", "control_valid");
}
foreach (var (name, control) in new[]
{
    ("qualified-reference", NarrowEvidence(controlBaseline, "control_valid").Replace("Nat := 1",
        "Nat := Extracted.controlValue", StringComparison.Ordinal)),
    ("opened-namespace", "open Extracted\n" + NarrowEvidence(controlBaseline, "control_valid"))
})
{
    try
    {
        CheckedEvidenceControl(controlBaseline, control, ["control_valid"], 0);
        throw new InvalidOperationException("Explicit reference escaped the evidence projection: " + name);
    }
    catch (InvalidOperationException failure) when
        (failure.Message == "Evidence controls require namespace-relative references.")
    {
        Console.WriteLine("PASS checked control rejects " + name);
    }
}
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
ExtractBatch("extract", "Examples", samples.Select((selector, index) =>
    new GeneratedExtraction(assembly, "GenericMethods::" + selector, Path.Combine(output, index.ToString()))));

string ChangeDefinition(string source, string name, Func<string, string> change)
{
    var start = source.IndexOf("def " + name + " :", StringComparison.Ordinal);
    if (start < 0) throw new InvalidOperationException("Missing definition " + name);
    var end = source.IndexOf('\n', start);
    return source[..start] + change(source[start..end]) + source[end..];
}
void Reject(int sample, string name, Func<string, string> mutate,
    string? theorem = "method1_specialization_validated")
{
    var baseline = File.ReadAllText(Path.Combine(output, sample.ToString(), "Extracted.lean"));
    var source = mutate(baseline);
    if (source == baseline) throw new InvalidOperationException("Mutation did not change source: " + name);
    if (theorem is not null)
    {
        var control = NarrowEvidence(baseline, theorem);
        if (controlSources.Add(control))
        {
            if (!controls.TryGetValue(sample, out var sampleControls)) controls[sample] = sampleControls = [];
            sampleControls.Add(CheckedEvidenceControl(baseline, control, [theorem], controlSources.Count));
        }
        source = NarrowEvidence(source, theorem);
    }
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
Reject(0, "wrong-type-argument", source => ChangeDefinition(source, "method1TypeArgumentsRaw",
    line => line.Replace("System.UInt64", "System.UInt32")));
Reject(0, "wrong-closed-signature", source => ChangeDefinition(source, "method1Closed",
    line => line.Replace("System.UInt64", "System.UInt32")));
Reject(7, "wrong-closed-local", source => ChangeDefinition(source, "method1Closed", line =>
    line.Replace("locals := [.atom", "locals := [.byref (.atom").Replace("], initLocals", ")], initLocals")));
Reject(12, "wrong-type-operand", source => ChangeDefinition(source, "method1Closed", line =>
    line.Replace("operand := .type (.aggregate", "operand := .type (.byref (.aggregate").Replace(" 0) }", " 0)) }")));
Reject(0, "altered-opcode", source => ChangeDefinition(source, "method1Closed",
    line => line.Replace("opcode := 2,", "opcode := 3,")));
Reject(4, "altered-branch", source => ChangeDefinition(source, "method1Closed",
    line => line.Replace("operand := .target 4", "operand := .target 3")));
Reject(0, "wrong-managed-target", source => source.Replace(".call 1 1", ".call 0 1"), "method0_calls_validated");
Console.WriteLine("PASS original-metadata generic substitution, complete managed-call binding and malformed evidence rejection");
Reject(0, "omitted-method-evidence", source => ChangeDefinition(source, "methodEvidence",
    _ => "def methodEvidence : List Extraction.MethodEvidence := []"), null);
Reject(0, "reordered-method-evidence", source => ChangeDefinition(source, "methodEvidence",
    line => line.Replace("method0", "swapped").Replace("method1", "method0").Replace("swapped", "method1")), null);
Reject(0, "wrong-emitted-return", source => ChangeDefinition(source, "method1",
    line => line.Replace("returnsValue := true", "returnsValue := false"))
        .Replace("method1.returnsValue = (true)", "method1.returnsValue = (false)"), "method1_shape_validated");
Reject(7, "wrong-local-initializer", source => source.Replace("[.i32 0]", "[.i32 1]"), "method1_shape_validated");
Reject(7, "wrong-initlocals-flag", source => source.Replace("initLocals := true", "initLocals := false"), "method1_shape_validated");
Reject(9, "missing-return-narrowing", source => source.Replace(".ret (some .signed8)", ".ret none"), "method1_shape_validated");
Reject(9, "wrong-return-signedness", source => source.Replace(".ret (some .signed8)", ".ret (some .unsigned8)"),
    "method1_shape_validated");

foreach (var (selector, index) in samples.Select((selector, index) => (selector, index)))
{
    var source = File.ReadAllText(Path.Combine(output, index.ToString(), "Extracted.lean"));
    var path = Path.Combine(output, "Checked-" + index + ".lean");
    File.WriteAllText(path, source + "\n" + string.Join('\n', controls.GetValueOrDefault(index) ?? []));
    evidence.Add(path, "PASS structural specialization and unchanged obligations " + selector);
}
CheckExternalCallTargets();
evidence.Check();
CheckLeanFixture("Tests.ExtractionGenerics");
rejected.Check();
void CheckExternalIdentities()
{
    var identityEvidence = new ExternalIdentityEvidence();
    var identities = new[]
    {
        "System.Runtime, Version=10.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a::" +
            "System.UInt64 Namespace.Type::Method(System.UInt64)",
        "Unicode::Namespace.λ漢字::Method(\"quoted\",\\path)",
        "System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=0000000000000000::" +
            "System.UInt64 Namespace.Type::Method(System.UInt64)"
    };
    var lean = new StringBuilder("import Lean\nset_option maxRecDepth 4096\n");
    if (identityEvidence.Reference("unreachable only", false) != JsonSerializer.Serialize("unreachable only"))
        throw new InvalidOperationException("Unreachable identity was materialized.");
    identityEvidence.Emit(lean);
    if (lean.ToString().Contains("externalIdentity", StringComparison.Ordinal))
        throw new InvalidOperationException("Unreachable identity emitted proof declarations.");
    foreach (var (identity, index) in identities.Select((identity, index) => (identity, index)))
    {
        var name = "externalIdentity" + index;
        if (identityEvidence.Reference(identity, true) != name || identityEvidence.Reference(identity, true) != name)
            throw new InvalidOperationException("Exact identity deduplication changed.");
    }
    identityEvidence.Emit(lean);
    var baseline = lean.ToString();
    identityEvidence.Emit(lean);
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
    File.WriteAllText(path, "import Lean\nnamespace Extracted\n" +
        baseline.Replace("import Lean\n", "", StringComparison.Ordinal) + "\nend Extracted\n");
    evidence.Add(path, "PASS exact external identities: deduplication, unreachable calls and Unicode",
        "exactIdentity2");
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
        rejected.Add(rejectedPath, "PASS exact identity mutation: " + name,
            diagnostic => diagnostic.Contains("rfl", StringComparison.Ordinal) ||
                diagnostic.Contains("Type mismatch", StringComparison.Ordinal));
    }
}

void CheckExternalCallTargets()
{
    var folder = Path.Combine(output, "ExternalCalls");
    Run(Extract("extract", assembly, "Examples", "DivisionIntrinsics::UnsafeEquals(ulong)", folder, "x64-v3"));
    var path = Path.Combine(folder, "Extracted.lean");
    var baseline = File.ReadAllText(path);
    const string theorem = "method0_division_validated";
    var control = NarrowEvidence(baseline, theorem);
    var positive = Path.Combine(folder, "Checked.lean");
    File.WriteAllText(positive, baseline + "\n" + CheckedEvidenceControl(baseline, control, [theorem], 0));
    evidence.Add(positive, "PASS complete materialized external call certificate and mutation control");
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
        File.WriteAllText(rejectedPath, NarrowEvidence(source, theorem));
        rejected.Add(rejectedPath, "PASS materialized external call rejects " + name,
            "Extraction.DivisionIntrinsicsValid", "is false");
    }
}
