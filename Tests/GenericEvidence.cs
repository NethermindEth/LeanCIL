#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include PreparedLeanFixtures.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../Extractor/ExternalIdentityEvidence.cs

using System.Text;
using System.Text.Json;
using System.Text.RegularExpressions;
using Nethermind.LeanCIL;

if (args is not ([] or ["--external-identities"] or ["--measure"] or ["--return-only"]))
    throw new ArgumentException("Usage: GenericEvidence.cs [--external-identities|--measure|--return-only]");
var output = At("artifacts/GenericEvidence");
Directory.CreateDirectory(output);
var rejected = new RejectedEvidence(output);
var evidence = new GeneratedEvidence(output, args.Contains("--measure", StringComparer.Ordinal));
var controls = new Dictionary<int, List<string>>();
var controlSources = new HashSet<string>(StringComparer.Ordinal);
if (args is ["--return-only"])
{
    RequireLeanFixtures("CIL.Extraction.Translation");
    var directory = Path.Combine(output, "9");
    Run(Extract("extract", At("Examples/Assembly/bin/Examples.dll"), "Examples",
        "GenericMethods::EnumIdentity(Examples.Signed8)", directory));
    ReturnMutations();
    var baseline = File.ReadAllText(Path.Combine(directory, "Extracted.lean"));
    var positive = Path.Combine(output, "ReturnControl.lean");
    File.WriteAllText(positive, baseline + "\n" + string.Join("\n", controls[9]));
    evidence.Add(positive, "PASS declared return control");
    evidence.Check();
    rejected.Check();
    return;
}
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
    var changed = change(source[start..end]);
    // A replacement that matched nothing would leave a fixture rejected for another reason.
    if (changed == source[start..end]) throw new InvalidOperationException("Mutation did not change " + name);
    return source[..start] + changed + source[end..];
}
string Replaced(string text, string before, string after) =>
    text.Contains(before, StringComparison.Ordinal)
        ? text.Replace(before, after, StringComparison.Ordinal)
        : throw new InvalidOperationException("Missing mutation target: " + before);
void Reject(int sample, string name, Func<string, string> mutate,
    string? theorem = "method1_specialization_validated", string diagnostic = "error:")
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
    rejected.Add(path, "PASS generic evidence rejects " + name, diagnostic);
}
foreach (var (name, scope) in new[]
{
    ("wrong-runtime-version", "System.Runtime, Version=9.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a"),
    ("wrong-runtime-token", "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=0000000000000000")
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
// A failed kernel decision prints this text; a mutation that only breaks parsing does not.
const string decisionFailed = "proved that the proposition";
// A theorem proved by `rfl` prints this text when its two sides differ.
const string rflRefused = "not definitionally equal";
// The link moves with the call, so only the binding check can reject the changed target.
Reject(0, "wrong-managed-target", source => ChangeDefinition(Replaced(source, ".call 1 1", ".call 0 1"),
    "method0Link1", line => Replaced(line, ".direct 1", ".direct 0")), "method0_calls_validated",
    decisionFailed);
Console.WriteLine("PASS original-metadata generic substitution, complete managed-call binding and malformed evidence rejection");
// Each mutation changes one fact of the first sample's body evidence, so only the decoding check can reject it;
// the unmutated obligation is checked as the positive control.
const string bodyTheorem = "method0_body_validated";
// The tactic that proves a body obligation names the method and the failure when the kernel refutes it; a mutation
// that only breaks parsing prints other text, and the unmutated obligation is the positive control.
const string bodyDecisionFailed = "the decoded method does not match its body bytes or metadata";
// A mutated body obligation must fail to elaborate and its negation must be proved by the kernel.
void RejectBody(int sample, string name, string theorem, string definition, Func<string, string> change)
{
    Reject(sample, name, source => ChangeDefinition(source, definition, change), theorem, bodyDecisionFailed);
    RefuteMutation(sample, name, theorem, definition, change);
}
// A file that keeps the mutated definitions and states the obligation's negation, which the kernel must prove.
void RefuteMutation(int sample, string name, string theorem, string definition, Func<string, string> change)
{
    var mutated = ChangeDefinition(File.ReadAllText(Path.Combine(output, sample.ToString(), "Extracted.lean")),
        definition, change);
    var refutation = theorem[..^"_validated".Length] + "_refuted";
    var refuted = KernelRefutation(mutated, theorem, refutation);
    var path = Path.Combine(output, "Refuted-" + name + ".lean");
    File.WriteAllText(path, NarrowEvidence(refuted, refutation));
    evidence.Add(path, "PASS the kernel proves the mutated obligation false: " + name, refutation);
}
// A changed declared signature of `definition` fails its `rfl` obligation, which the kernel proves false.
void RejectDeclared(int sample, string name, string definition, Func<string, string> change)
{
    var theorem = definition + "_declared_validated";
    Reject(sample, name, source => ChangeDefinition(source, definition, change), theorem, rflRefused);
    RefuteMutation(sample, name, theorem, definition, change);
}
// The metadata rows of a body shift with the assembly, so each byte is found by its position in the emitted list.
string ChangeByte(string line, string pattern, int change) => Regex.Replace(line, pattern,
    match => match.Groups[1].Value + (int.Parse(match.Groups[2].Value) + change) + match.Groups[3].Value);
// A byte list is emitted as `(CIL.Extraction.fixedBytes <count> 0x<digits>)`; a pattern's second group is one byte.
const string literalHead = """\(CIL\.Extraction\.fixedBytes """;
const string byteLiteral = literalHead + """\d+ 0x""";
string ChangeLiteralByte(string line, string pattern, int change) => Regex.Replace(line, pattern,
    match => match.Groups[1].Value + ((Convert.ToInt32(match.Groups[2].Value, 16) + change) % 256).ToString("X2"));
// Sample 0 starts `ldarg.0; call <token>` under a tiny header: header, ldarg.0, call, then the token bytes.
RejectBody(0, "altered-body-byte", bodyTheorem, "method0Bytes",
    line => ChangeLiteralByte(line, $$"""({{byteLiteral}}[0-9A-F]{2})([0-9A-F]{2})""", 1));
RejectBody(0, "altered-body-header", bodyTheorem, "method0Bytes",
    line => ChangeLiteralByte(line, $$"""({{byteLiteral}})([0-9A-F]{2})""", 4));
RejectBody(0, "altered-token-operand-byte", bodyTheorem, "method0Bytes",
    line => ChangeLiteralByte(line, $$"""({{byteLiteral}}[0-9A-F]{2}0228)([0-9A-F]{2})""", 1));
// A count one short of the digits keeps the code but drops its leading byte, the body header.
RejectBody(0, "altered-literal-count", bodyTheorem, "method0Bytes",
    line => ChangeByte(line, $$"""({{literalHead}})(\d+)( 0x)""", -1));
RejectBody(0, "altered-token-table-key", bodyTheorem, "method0Body",
    line => ChangeByte(line, @"(\()(\d+)(, \.call)", 1));
RejectBody(0, "altered-token-table-operand", bodyTheorem, "method0Body",
    line => line.Replace("name := \"Identity\"", "name := \"Other\""));
RejectBody(0, "altered-instruction-offset", bodyTheorem, "method0Original",
    line => line.Replace("offset := 1, opcode := 40", "offset := 2, opcode := 40"));
RejectBody(0, "altered-max-stack", bodyTheorem, "method0Original",
    line => line.Replace("maxStack := 8", "maxStack := 9"));
// The module's lookup tables are decided once against its metadata; a changed row, heap entry or table is
// refuted there.
void RejectTables(string name, string definition, Func<string, string> change)
{
    const string theorem = "method0_tables_valid";
    Reject(0, name, source => ChangeDefinition(source, definition, change), theorem);
    var mutated = ChangeDefinition(File.ReadAllText(Path.Combine(output, "0", "Extracted.lean")), definition, change);
    var refuted = KernelRefutation(mutated, theorem, "method0_tables_refuted");
    var path = Path.Combine(output, "RefutedTables-" + name + ".lean");
    File.WriteAllText(path, NarrowEvidence(refuted, "method0_tables_refuted"));
    evidence.Add(path, "PASS the kernel proves the mutated tables obligation false: " + name,
        "method0_tables_refuted");
}
RejectTables("altered-metadata-row", "method0Metadata",
    line => ChangeLiteralByte(line, $$"""(rows := \[\(\d+, {{byteLiteral}})([0-9A-F]{2})""", 1));
RejectTables("altered-metadata-string", "method0Metadata", line => ChangeLiteralByte(line,
    $$"""(strings := \[\(0, {{literalHead}}1 0x00\)\), \(\d+, {{byteLiteral}})([0-9A-F]{2})""", 1));
RejectTables("altered-lookup-row", "method0Tables",
    line => ChangeLiteralByte(line, $$"""(rows := .*?{{byteLiteral}})([0-9A-F]{2})""", 1));
// A leaf entry of the rows tree removed, and one added before another.
RejectTables("missing-lookup-row", "method0Tables",
    line => new Regex($$"""\(\.node \.leaf \d+ {{byteLiteral}}[0-9A-F]+\) \.leaf\)""").Replace(line, ".leaf", 1));
RejectTables("extra-lookup-row", "method0Tables",
    line => new Regex($$"""\(\.node \.leaf (\d+) ({{byteLiteral}}[0-9A-F]+\)) \.leaf\)""").Replace(line,
        "(.node (.node .leaf 1 [0] .leaf) $1 $2 .leaf)", 1));
RejectBody(4, "altered-body-branch-index", "method1_body_validated", "method1Original",
    line => line.Replace("operand := .target 4", "operand := .target 3"));
Console.WriteLine("PASS body bytes, token table and original definition reject changed bytes and operands");
Reject(0, "omitted-method-evidence", source => ChangeDefinition(source, "methodEvidence",
    _ => "def methodEvidence : List Extraction.MethodEvidence := []"), null);
Reject(0, "reordered-method-evidence", source => ChangeDefinition(source, "methodEvidence",
    line => line.Replace("method0", "swapped").Replace("method1", "method0").Replace("swapped", "method1")), null);
// Identity64(ulong) and its callee Identity<UInt64>(ulong) have the same shape; with their signature strings swapped,
// each body check refutes the string a proof would select the method by.
string SwapSignatures(string source)
{
    string Value(string name) => Regex.Match(source, "(?m)^def " + name + " : String := (.*)$").Groups[1].Value;
    var (first, second) = (Value("method0Signature"), Value("method1Signature"));
    return ChangeDefinition(ChangeDefinition(source, "method0Signature", line => line.Replace(first, second)),
        "method1Signature", line => line.Replace(second, first));
}
const string equationRefused = "cil_kernel_rfl: the kernel does not accept the two sides as equal";
Reject(0, "swapped-signature-of-a-method", SwapSignatures, bodyTheorem, equationRefused);
Reject(0, "swapped-signature-of-an-instance", SwapSignatures, "method1_body_validated", equationRefused);
Reject(0, "wrong-emitted-return", source => ChangeDefinition(source, "method1",
    line => line.Replace("returnsValue := true", "returnsValue := false"))
        .Replace("method1.returnsValue = (true)", "method1.returnsValue = (false)"), "method1_shape_validated");
Reject(7, "wrong-local-initializer", source => source.Replace("[.i32 0]", "[.i32 1]"), "method1_shape_validated");
Reject(7, "wrong-initlocals-flag", source => source.Replace("initLocals := true", "initLocals := false"), "method1_shape_validated");
ReturnMutations();

void ReturnMutations()
{
    foreach (var (name, replacement) in new[]
        { ("missing-return-narrowing", "System.Int32"), ("wrong-return-signedness", "System.Byte") })
        RejectDeclared(9, name, "method1", line =>
        {
            var returned = line.IndexOf("returnType :=", StringComparison.Ordinal);
            var atom = returned < 0 ? -1 : line.IndexOf("System.SByte", returned, StringComparison.Ordinal);
            if (atom < 0) throw new InvalidOperationException("Missing declared SByte return");
            return line[..atom] + replacement + line[(atom + "System.SByte".Length)..];
        });
}

// The declared signature, call links and layout environment are each checked against their own evidence.
const string word = "Extraction.runtimeScope \"System.UInt64\"";
RejectDeclared(0, "wrong-declared-parameter", "method0", line =>
    line.Replace($"parameters := [.atom {word}]", $"parameters := [.atom {word.Replace("UInt64", "UInt32")}]"));
// The declared signature's own return type, whatever fields follow it.
RejectDeclared(0, "wrong-declared-return", "method0", line => Regex.Replace(line,
    $$"""(declared := {[^}]*returnType := .atom ){{Regex.Escape(word)}}""",
    match => match.Groups[1].Value + word.Replace("UInt64", "UInt32"), RegexOptions.None));
RejectDeclared(0, "wrong-declared-init-flag", "method0", line => line.Replace(", initLocals := false }", " }"));
RejectDeclared(14, "missing-declared-receiver", "method1", line =>
    line.Replace("receiver := some .reference, ", ""));
RejectDeclared(14, "wrong-declared-receiver-kind", "method1", line =>
    line.Replace("receiver := some .reference", "receiver := some .object"));
Reject(0, "wrong-link-callee", source => ChangeDefinition(source, "method0Link1", line =>
    line.Replace(".direct 1", ".direct 0")), "method0_calls_validated", decisionFailed);
Reject(0, "dropped-link", source => ChangeDefinition(source, "method0Links", line =>
    line.Replace(":= [(1, method0Link1)]", ":= []")), "method0_calls_validated", decisionFailed);
Reject(0, "link-at-wrong-pc", source => ChangeDefinition(source, "method0Links", line =>
    line.Replace(":= [(1, method0Link1)]", ":= [(0, method0Link1)]")), "method0_calls_validated",
    decisionFailed);
Reject(0, "link-at-non-call", source => ChangeDefinition(source, "method1Links", line =>
    line.Replace(":= []", ":= [(0, method0Link1)]")), "method1_calls_validated", decisionFailed);
Reject(0, "wrong-environment", source => ChangeDefinition(source, "environment", line =>
    line.Replace("layouts := computedLayouts", "layouts := #[⟨⟨4, []⟩, 4⟩]")), "method0_environment_validated",
    rflRefused);

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
        "System.Runtime, Version=11.0.0.0, Culture=neutral, PublicKeyToken=b03f5f7f11d50a3a::" +
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
        ("changed-version", baseline.Replace("Version=11.0.0.0", "Version=10.0.0.0", StringComparison.Ordinal)),
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
    const string theorem = "method0_intrinsics_validated";
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
            "Extraction.ExactIntrinsicsValid", "is false");
    }
}
