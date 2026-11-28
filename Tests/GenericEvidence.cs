#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
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
        line.Replace(".primitive .uint64",
            $".atom {System.Text.Json.JsonSerializer.Serialize(scope)} \"System.UInt64\" .valueType")));
Reject(0, "wrong-type-argument", source => ChangeDefinition(source, "method1TypeArgumentsRaw",
    line => line.Replace(".primitive .uint64", ".primitive .uint32")));
Reject(0, "wrong-closed-signature", source => ChangeDefinition(source, "method1Closed",
    line => line.Replace(".primitive .uint64", ".primitive .uint32")));
Reject(7, "wrong-closed-local", source => ChangeDefinition(source, "method1Closed", line =>
    line.Replace("locals := [.primitive .int32]", "locals := [.byref (.primitive .int32)]")));
Reject(12, "wrong-type-operand", source => ChangeDefinition(source, "method1Closed", line =>
    line.Replace("operand := .type (.aggregate", "operand := .type (.byref (.aggregate").Replace(" 0) }", " 0)) }")));
Reject(0, "altered-opcode", source => ChangeDefinition(source, "method1Closed",
    line => line.Replace("opcode := 2,", "opcode := 3,")));
Reject(4, "altered-branch", source => ChangeDefinition(source, "method1Closed",
    line => line.Replace("operand := .target 4", "operand := .target 3")));
// A theorem proved by `rfl` prints this text when its two sides differ.
const string rflRefused = "not definitionally equal";
// A forged call obligation must fail its kernel decision, and the kernel must prove its negation; the failed
// decision alone can print "failed to reduce" when its diagnostic stops at a well-founded name codec.
void RejectCall(int sample, string name, string theorem, Func<string, string> mutate)
{
    Reject(sample, name, mutate, theorem, "Tactic `decide`");
    RefuteMutation(sample, name, theorem, mutate);
}
// A call names the method its raw operand names, so the binding check rejects a call naming another method.
RejectCall(0, "wrong-call-operand", "method0_calls_validated", source => ForgeDecodedMethod(source, 0,
    "code := method.code.map fun " +
    "| .call callee prefixes => .call { callee with name := name!\"Other\" } prefixes | other => other"));
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
    RefuteMutation(sample, name, theorem, source => ChangeDefinition(source, definition, change));
}
// A file that keeps the mutated definitions and states the obligation's negation, which the kernel must prove.
void RefuteMutation(int sample, string name, string theorem, Func<string, string> mutate)
{
    var mutated = mutate(File.ReadAllText(Path.Combine(output, sample.ToString(), "Extracted.lean")));
    var refutation = theorem[..^"_validated".Length] + "_refuted";
    var refuted = KernelRefutation(mutated, theorem, refutation);
    var path = Path.Combine(output, "Refuted-" + name + ".lean");
    File.WriteAllText(path, NarrowEvidence(refuted, refutation));
    evidence.Add(path, "PASS the kernel proves the mutated obligation false: " + name, refutation);
}
// A changed declared signature of method `method` fails its `rfl` obligation, which the kernel proves false.
void RejectDeclared(int sample, string name, int method, Func<string, string> mutate)
{
    var theorem = $"method{method}_declared_validated";
    Reject(sample, name, mutate, theorem, rflRefused);
    RefuteMutation(sample, name, theorem, mutate);
}
// The metadata rows of a body shift with the assembly, so each byte is found by its position in the emitted list.
string ChangeByte(string line, Regex pattern, int change) => pattern.Replace(line,
    match => match.Groups[1].Value + (int.Parse(match.Groups[2].Value) + change) + match.Groups[3].Value);
// A byte list is emitted as `(CIL.Extraction.fixedBytes <count> 0x<digits>)`; a pattern's second group is one byte.
string ChangeLiteralByte(string line, Regex pattern, int change) => pattern.Replace(line,
    match => match.Groups[1].Value + ((Convert.ToInt32(match.Groups[2].Value, 16) + change) % 256).ToString("X2"));
// Sample 0 starts `ldarg.0; call <token>` under a tiny header: header, ldarg.0, call, then the token bytes.
RejectBody(0, "altered-body-byte", bodyTheorem, "method0Bytes",
    line => ChangeLiteralByte(line, GenericPatterns.SecondByte, 1));
RejectBody(0, "altered-body-header", bodyTheorem, "method0Bytes",
    line => ChangeLiteralByte(line, GenericPatterns.FirstByte, 4));
RejectBody(0, "altered-token-operand-byte", bodyTheorem, "method0Bytes",
    line => ChangeLiteralByte(line, GenericPatterns.TokenOperandByte, 1));
// A count one short of the digits keeps the code but drops its leading byte, the body header.
RejectBody(0, "altered-literal-count", bodyTheorem, "method0Bytes",
    line => ChangeByte(line, GenericPatterns.LiteralCount, -1));
// Keep the vector's name and arity, but give its platform definition a class marker.
string WrongVectorKind(string source)
{
    var head = $"0x{Convert.ToHexString("Vector128`1"u8)})], kind := ";
    return Replaced(source, head + ".genericValue 1", head + ".genericClass 1");
}
Reject(6, "wrong-instantiation-marker", WrongVectorKind, "method1_body_validated", bodyDecisionFailed);
RefuteMutation(6, "wrong-instantiation-marker", "method1_body_validated", WrongVectorKind);
RejectBody(0, "altered-token-table-key", bodyTheorem, "method0Body",
    line => ChangeByte(line, GenericPatterns.CallTokenKey, 1));
RejectBody(0, "altered-token-table-operand", bodyTheorem, "method0Body",
    line => line.Replace("name := \"Identity\"", "name := \"Other\""));
RejectBody(0, "altered-instruction-offset", bodyTheorem, "method0Original",
    line => line.Replace("offset := 1, opcode := 40", "offset := 2, opcode := 40"));
RejectBody(0, "altered-max-stack", bodyTheorem, "method0Original",
    line => line.Replace("maxStack := 8", "maxStack := 9"));
// The module's lookup tables are decided once against its metadata; a changed row, heap entry or table is
// refuted there.
void RejectTables(string name, Func<string, string> change)
{
    const string theorem = "method0_tables_valid";
    string Mutate(string source) => change(Replaced(source,
        " := Extraction.tablesMatch_of_result method0Tables_eq", " := by decide +kernel"));
    Reject(0, name, Mutate, theorem);
    var mutated = Mutate(File.ReadAllText(Path.Combine(output, "0", "Extracted.lean")));
    var refuted = KernelRefutation(mutated, theorem, "method0_tables_refuted");
    var path = Path.Combine(output, "RefutedTables-" + name + ".lean");
    File.WriteAllText(path, NarrowEvidence(refuted, "method0_tables_refuted"));
    evidence.Add(path, "PASS the kernel proves the mutated tables obligation false: " + name,
        "method0_tables_refuted");
}
// Keep the genuine index when changing the metadata, and the genuine metadata when changing the index.
string ChangeIndexedMetadata(string source, Regex pattern) =>
    ChangeDefinition(Replaced(source, ":= method0Metadata.tables.toOption", ":= originalMetadata.tables.toOption"),
        "method0Metadata", line => line.Replace("method0Metadata", "originalMetadata", StringComparison.Ordinal) +
            "\n" + ChangeLiteralByte(line, pattern, 1));
string ChangeIndexedRows(string source, string rows) => Replaced(source,
    "cil_evaluated method0Tables : List Extraction.IndexTables := method0Metadata.tables.toOption",
    "cil_evaluated originalTables : List Extraction.IndexTables := method0Metadata.tables.toOption\n" +
    "def method0Tables : List Extraction.IndexTables := originalTables.modify 0 fun table => " +
    $"{{ table with rows := Extraction.SearchTree.ofSorted ({rows}) }}");
RejectTables("altered-metadata-row", source => ChangeIndexedMetadata(source, GenericPatterns.MetadataRowByte));
RejectTables("altered-metadata-string", source => ChangeIndexedMetadata(source, GenericPatterns.MetadataStringByte));
RejectTables("altered-lookup-row", source => ChangeIndexedRows(source,
    "table.rows.toList.modify 0 (fun (key, bytes) => (key, bytes.modify 0 (fun b => (b + 1) % 256)))"));
RejectTables("missing-lookup-row", source => ChangeIndexedRows(source, "table.rows.toList.tail"));
RejectTables("extra-lookup-row", source => ChangeIndexedRows(source, "(1, [0]) :: table.rows.toList"));
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
    string Value(string name) => GenericPatterns.StringDefinition.Matches(source)
        .FirstOrDefault(match => match.Groups["name"].Value == name)?.Groups["value"].Value ?? "";
    var (first, second) = (Value("method0Signature"), Value("method1Signature"));
    return ChangeDefinition(ChangeDefinition(source, "method0Signature", line => line.Replace(first, second)),
        "method1Signature", line => line.Replace(second, first));
}
const string equationRefused = "cil_kernel_rfl: the kernel does not accept the two sides as equal";
Reject(0, "swapped-signature-of-a-method", SwapSignatures, bodyTheorem, equationRefused);
Reject(0, "swapped-signature-of-an-instance", SwapSignatures, "method1_body_validated", equationRefused);
// The callee is defined from its decoder, so the forged return flag is the value of a forged decoder.
Reject(0, "wrong-emitted-return", source => ForgeDecodedMethod(source, 1, "returnsValue := false"),
    "method1_shape_validated");
Reject(7, "wrong-local-initializer", source => ForgeDecodedMethod(source, 1, "locals := [.i32 1]"),
    "method1_shape_validated");
Reject(7, "wrong-initlocals-flag", source => ChangeDefinition(
    ForgeDecodedMethod(source, 1, "locals := [.i32 0]"), "method1Closed",
    line => line.Replace("initLocals := true", "initLocals := false", StringComparison.Ordinal)),
    "method1_shape_validated");
ReturnMutations();

void ReturnMutations()
{
    foreach (var (name, replacement) in new[]
        { ("missing-return-narrowing", ".signed32"), ("wrong-return-signedness", ".unsigned8") })
        // The callee is defined from its decoder, so the forged declared return is a forged decoder's value.
        RejectDeclared(9, name, 1, source => ForgeDecodedReturnType(source, 1, ".signed8", replacement));
}

// The declared signature, call links and layout environment are each checked against their own evidence.
// The caller is defined from its decoder, so each forged declared signature is the value of a forged decoder.
RejectDeclared(0, "wrong-declared-parameter", 0, source => ForgeDecodedMethod(source, 0,
    "declared := { method.declared with parameters := [.primitive .uint32] }"));
RejectDeclared(0, "wrong-declared-return", 0, source => ForgeDecodedMethod(source, 0,
    "declared := { method.declared with returnType := .primitive .uint32 }"));
RejectDeclared(0, "wrong-declared-init-flag", 0, source => ForgeDecodedMethod(source, 0,
    "declared := { method.declared with initLocals := true }"));
// The instance method is defined from its decoder, so its forged receiver is the value of a forged decoder.
RejectDeclared(14, "missing-declared-receiver", 1,
    source => ForgeDecodedMethod(source, 1, "declared := { method.declared with receiver := none }"));
RejectDeclared(14, "wrong-declared-receiver-kind", 1,
    source => ForgeDecodedMethod(source, 1, "declared := { method.declared with receiver := some .object }"));
RejectCall(0, "wrong-link-callee", "method0_calls_validated", source => ChangeDefinition(source, "method0Link1",
    line => line.Replace(".direct 1", ".direct 0")));
// A missing link at the live call produces the call hole before a method can be defined.
const string missingCallLink = "CIL.Extraction.MethodDecodeError.liveHole 1 40";
Reject(0, "dropped-link", source => ChangeDefinition(source, "method0Links", line =>
    Replaced(line, "[(1, method0Link1)]", "[]")), "method0_calls_validated", missingCallLink);
Reject(0, "link-at-wrong-pc", source => ChangeDefinition(source, "method0Links", line =>
    Replaced(line, "[(1, method0Link1)]", "[(0, method0Link1)]")),
    "method0_calls_validated", missingCallLink);
// Managed-call evidence also rejects the same forged tables in an already decoded method.
foreach (var (name, links) in new[] { ("dropped-link", "[]"), ("link-at-wrong-pc", "[(0, .direct 1)]") })
{
    const string prefix = "method0DispatchTypes method0Closed) method0Reachable";
    RejectCall(0, $"emitted-{name}", "method0_calls_validated", source => Replaced(source, $"{prefix} method0 :=",
        $$"""{{prefix}} { method0 with links := {{links}} } :="""));
}
RejectCall(0, "link-at-non-call", "method1_calls_validated", source => ChangeDefinition(source, "method1Links",
    line => Replaced(line, ":= []", ":= [(0, method0Link1)]")));
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
    const string theorem = "method0_models_validated";
    var control = NarrowEvidence(baseline, theorem);
    var positive = Path.Combine(folder, "Checked.lean");
    File.WriteAllText(positive, baseline + "\n" + CheckedEvidenceControl(baseline, control, [theorem], 0));
    evidence.Add(positive, "PASS complete materialized external call certificate and mutation control");
    foreach (var (name, source, obligation, markers) in new (string, string, string, string[])[]
    {
        // CreateScalarUnsafe keeps its call and runs its model, so the body evidence, which binds each raw call
        // target to its metadata row, refuses another target.
        ("wrong-raw-target", baseline.Replace("target := .external externalIdentity0",
            "target := .external externalIdentity1", StringComparison.Ordinal), bodyTheorem, [bodyDecisionFailed]),
        // The typed scalar-unsafe reference and its declaration still name the original member.
        ("crossed-Avx2-And-target", baseline.Replace(
            """name := "CreateScalarUnsafe", target := .external externalIdentity0""",
            $"""name := "CreateScalarUnsafe", target := .external {AndTarget()}""",
            StringComparison.Ordinal), bodyTheorem, [bodyDecisionFailed]),
        // Substitute the decoded CreateScalarUnsafe call at pc 1 for op_Equality at pc 4.
        ("wrong-emitted-intrinsic", ForgeDecodedInstruction(baseline, 0, 4, "fun _ => method.code[1]'(by decide)"),
            theorem, ["Extraction.RuntimeModelsAgree", "is false"])
    })
    {
        if (source == baseline) throw new InvalidOperationException("Call mutation was not applied: " + name);
        var rejectedPath = Path.Combine(folder, name + ".lean");
        if (name == "crossed-Avx2-And-target")
        {
            File.WriteAllText(rejectedPath, source);
            const string refuted = "crossed_target_fails_body_binding";
            var refutationPath = Path.Combine(folder, "RefutedCrossedTarget.lean");
            File.WriteAllText(refutationPath, NarrowEvidence(KernelRefutation(source, obligation, refuted), refuted));
            evidence.Add(refutationPath,
                "PASS the kernel refutes BodyDecodes for the crossed Avx2.And target", refuted);
        }
        else File.WriteAllText(rejectedPath, NarrowEvidence(source, obligation));
        rejected.Add(rejectedPath, "PASS materialized external call rejects " + name, markers);
    }
}

static string AndTarget()
{
    const string vector = "System.Runtime.Intrinsics.Vector256`1<System.UInt64>";
    const string owner = "System.Runtime.Intrinsics.X86.Avx2";
    return $"""(CIL.Extraction.intrinsicsScope ++ "::{vector} {owner}::And({vector},{vector})")""";
}

/// <summary>The patterns that find the bytes and rows a mutation changes in generated evidence.</summary>
static partial class GenericPatterns
{
    // A byte list is emitted as (CIL.Extraction.fixedBytes count 0xdigits); a byte pattern's second group is one byte.
    const string LiteralHead = """\(CIL\.Extraction\.fixedBytes """;
    const string ByteLiteral = $$"""{{LiteralHead}}\d+ 0x""";

    [GeneratedRegex($$"""({{ByteLiteral}})([0-9A-F]{2})""")]
    internal static partial Regex FirstByte { get; }

    [GeneratedRegex($$"""({{ByteLiteral}}[0-9A-F]{2})([0-9A-F]{2})""")]
    internal static partial Regex SecondByte { get; }

    /// <summary>The first token byte of a body that starts with a tiny header, ldarg.0 and call.</summary>
    [GeneratedRegex($$"""({{ByteLiteral}}[0-9A-F]{2}0228)([0-9A-F]{2})""")]
    internal static partial Regex TokenOperandByte { get; }

    [GeneratedRegex($$"""({{LiteralHead}})(\d+)( 0x)""")]
    internal static partial Regex LiteralCount { get; }

    [GeneratedRegex(@"(\()(\d+)(, \.call)")]
    internal static partial Regex CallTokenKey { get; }

    [GeneratedRegex($$"""(rows := \[\(\d+, {{ByteLiteral}})([0-9A-F]{2})""")]
    internal static partial Regex MetadataRowByte { get; }

    [GeneratedRegex($$"""(strings := \[\(0, {{LiteralHead}}1 0x00\)\), \(\d+, {{ByteLiteral}})([0-9A-F]{2})""")]
    internal static partial Regex MetadataStringByte { get; }

    [GeneratedRegex(@"(?m)^def (?<name>\w+) : String := (?<value>.*)$")]
    internal static partial Regex StringDefinition { get; }
}
