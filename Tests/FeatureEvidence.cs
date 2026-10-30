#!/usr/bin/env dotnet
#:property PublishAot=false
#:package Mono.Cecil
#:include ../scripts/Verification.cs
#:include PreparedLeanFixtures.cs
#:include ../scripts/BatchVerification.cs
#:include RejectedEvidence.cs
#:include GeneratedEvidence.cs
#:include ../scripts/RuntimeProfileValidation.cs

using System.Text.RegularExpressions;
using System.Reflection;
using System.Text.Json;
using System.Text.Json.Nodes;
using Mono.Cecil;
using Mono.Cecil.Cil;

using var verification = new Program();
var output = At("artifacts/FeatureEvidence");
Directory.CreateDirectory(output);
var rejected = new RejectedEvidence(output);
// Exercise the production validator and both old-name and custom-profile migration paths.
verification.EnsureExtractorBuilt();
var profileType = Assembly.Load(File.ReadAllBytes(ExtractorPath))
    .GetType("Nethermind.LeanCIL.FeatureProfile", throwOnError: true)!;
var selectProfile = profileType.GetMethod("Select", BindingFlags.Static | BindingFlags.NonPublic)!;
object SelectProfile(string name) => selectProfile.Invoke(null, [name])!;
var jsonOptions = new JsonSerializerOptions { PropertyNamingPolicy = JsonNamingPolicy.CamelCase };
var sharedCases = RuntimeProfileValidation.Observations(
    Directory.GetFiles(At("docs/evidence/runtime-profiles"), "*.json")).ToList();
// Getters read AdvSimd.Arm64 as AdvSimd and Avx512Vbmi.VL as Avx512Vbmi, so observations that
// omit or split either nested flag are refused.
foreach (var (evidence, nested, baseFlag, getter) in new[]
{
    ("macos-arm64-net10.json", "advSimd64", "advSimd", "AdvSimd.Arm64"),
    ("windows-x64-net10.json", "avx512VbmiVL", "avx512Vbmi", "Avx512Vbmi.VL")
})
{
    var recorded = JsonNode.Parse(File.ReadAllText(At($"docs/evidence/runtime-profiles/{evidence}")))!;
    foreach (var (name, mutate) in new (string, Action<JsonObject>)[]
    {
        ("missing", observed => observed.Remove(nested)),
        ("split", observed => observed[nested] = !observed[baseFlag]!.GetValue<bool>())
    })
    {
        var observations = recorded.DeepClone();
        mutate(observations[0]!["observed"]!.AsObject());
        var observationPath = Path.Combine(output, $"{nested}-{name}.json");
        File.WriteAllText(observationPath, observations.ToJsonString());
        try
        {
            _ = RuntimeProfileValidation.Observations([observationPath]).ToList();
            throw new InvalidOperationException($"{getter} observation accepted: {name}");
        }
        catch (InvalidDataException error) when (error.Message.Contains(getter, StringComparison.Ordinal)) { }
        Console.WriteLine($"PASS {getter} observation rejected: {name}");
    }
}
foreach (var name in new[] { "scalar", "x64-sse2", "x64-sse42", "x64-v3", "x64-v4", "arm64-advsimd" })
    sharedCases.Add((JsonSerializer.Serialize(SelectProfile(name), jsonOptions), true));
foreach (var name in new[] { "x64-avx2", "x64-avx2-bmi1", "x64-avx512", "x64-avx512-bmi1",
    "x64-bmi2", "x64-vector256", "x64-sse41", "arm64-armbase" })
{
    try { _ = SelectProfile(name); throw new InvalidOperationException("Retired profile accepted: " + name); }
    catch (TargetInvocationException exception) when (exception.InnerException is ArgumentException invalidProfile &&
        invalidProfile.Message.Contains("Retired execution profile", StringComparison.Ordinal)) { }
}
foreach (var (name, flag, value, accepted) in new[]
{
    ("x64-v3", "bmi1", false, false), ("x64-v3", "bmi2", false, false),
    ("x64-v3", "vector256Accelerated", false, true), ("x64-v3", "vector128Accelerated", false, false),
    ("x64-sse42", "sse42", false, false), ("x64-sse42", "vector256Accelerated", true, false),
    ("x64-v4", "avx512FVL", false, false), ("x64-v4", "avx512DQ", false, false),
    ("x64-v4", "avx512DQVL", false, false), ("arm64-advsimd", "advSimd", false, false),
    ("arm64-advsimd", "vector128Accelerated", false, false), ("arm64-advsimd", "vector256Accelerated", true, false),
    // VBMI is an optional group above AVX-512: x64-v4 may add it, but nothing below v4 may.
    ("x64-v4", "avx512Vbmi", true, true), ("x64-v3", "avx512Vbmi", true, false),
    ("arm64-advsimd", "avx512Vbmi", true, false)
})
{
    var profile = JsonSerializer.SerializeToNode(SelectProfile(name), jsonOptions)!;
    profile[flag] = JsonValue.Create(value);
    sharedCases.Add((profile.ToJsonString(), accepted));
    var profilePath = Path.Combine(output, $"{name}-{flag}.json");
    File.WriteAllText(profilePath, profile.ToJsonString());
    try
    {
        _ = SelectProfile("@" + profilePath);
        if (!accepted) throw new InvalidOperationException("Split runtime group accepted: " + profilePath);
    }
    catch (TargetInvocationException exception) when (!accepted && exception.InnerException is InvalidDataException) { }
}
Console.WriteLine("PASS runtime profile groups, retired profiles and reduced vector width");
RequireLeanFixtures("CIL.Extraction.Features", "CIL.SymbolicExecution", "CIL.Safety.Execution");
var sharedEvidence = Path.Combine(output, "RuntimeProfiles.lean");
RuntimeProfileValidation.Check(sharedCases, ExtractorPath, sharedEvidence);
Run(["lake", "env", "lean", sharedEvidence], cwd: verification.CheckoutPackage());
RequireLeanFixtures("Tests.FeatureEvidence");
var assembly = At("Examples/Assembly/bin/Examples.dll");
var folder = Path.Combine(output, "CompiledLoop");
Run(Extract("extract", assembly, "Examples", "Loops::FeatureCountdown(uint)", folder, "scalar"));
var path = Path.Combine(folder, "Extracted.lean");
var baseline = File.ReadAllText(path);
const string featureObligation = "method0_features_validated";
var control = CheckedEvidenceControl(baseline, NarrowEvidence(baseline, featureObligation),
    [featureObligation], 0);
var checkedPath = Path.Combine(folder, "Checked.lean");
File.WriteAllText(checkedPath, baseline + control);
Run(["lake", "env", "lean", checkedPath], cwd: verification.CheckoutPackage());

void Reject(string name, string mutated)
{
    if (mutated == baseline) throw new InvalidOperationException("Feature mutation did not change source: " + name);
    var target = Path.Combine(output, name + ".lean");
    File.WriteAllText(target, NarrowEvidence(mutated, featureObligation));
    rejected.Add(target, "PASS feature certificate rejects " + name,
        "Extraction.FeatureFlowValid", "is false");
}

string MutateState(string source, string update) => Regex.Replace(source,
    @"(?m)^(def method0FeatureStates : Extraction.FeatureCertificate := )([^\r\n]+)",
    match => match.Groups[1].Value + "(" + match.Groups[2].Value + ")." + update);

// Each mutation checks feature flow independently, without unrelated validator proofs
// or instruction lookup equations that could reject it for a different reason.
Reject("wrong-feature", baseline.Replace(".feature .avx2", ".feature .sse2"));
Reject("wrong-branch", baseline.Replace(".brzero 10", ".brzero 11"));
Reject("forged-constant", baseline.Replace("stack := [some (BitVec.ofInt 32 (0))]", "stack := [some (BitVec.ofInt 32 (1))]"));
Reject("malformed-entry", MutateState(baseline, "set 0 (some { stack := [none], locals := [none] })"));
Reject("false-pruned-successor", MutateState(baseline, "set 10 none"));
Reject("omitted-states", MutateState(baseline, "take 17"));
var unsupported = Execute(Extract("extract", assembly, "Examples", "Loops::FeatureCountdown(uint)",
    Path.Combine(output, "EnabledUnsupported"), "x64-v3"));
if (unsupported.Code == 0 || !unsupported.Output.Contains("Unsupported instruction"))
    throw new InvalidOperationException("Enabled feature failed to expose unsupported array code: " + unsupported.Output);
// X86Base.X64 and Vector128 getters decide their branches from the profile alone.
var capabilitiesQueue = new GeneratedQueue(verification, assembly);
var platformResult = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Capabilities")!
    .GetMethod("Platform")!.Invoke(null, []);
if (!Equals(platformResult, 17)) throw new InvalidOperationException("Platform comparison requires a 64-bit process");
foreach (var (profile, flags) in new[] { ("scalar", 0), ("x64-v3", 3), ("arm64-advsimd", 2), ("x64-sse42", 3) })
{
    var capabilities = Path.Combine(output, "Capabilities-" + profile);
    Directory.CreateDirectory(capabilities);
    var proof = Path.Combine(capabilities, "Proof.lean");
    File.WriteAllText(proof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\ntheorem correctness :\n" +
        $"  (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = .ok [.scalar (.i32 {flags})] := rfl\nend ExampleProof\n");
    capabilitiesQueue.Add(new("Capabilities::Flags()", proof, Path.Combine(capabilities, "Verified"), Profile: profile),
        () => Console.WriteLine($"PASS Capabilities::Flags under {profile} returns {flags}"));
    var platform = Path.Combine(capabilities, "Platform.lean");
    File.WriteAllText(platform, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        "theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = " +
        ".ok [.scalar (.i32 17)] := rfl\n#print axioms correctness\nend ExampleProof\n");
    capabilitiesQueue.Add(new("Capabilities::Platform()", platform, Path.Combine(capabilities, "Platform"), Profile: profile),
        () => Console.WriteLine($"PASS platform constants and pruned unsupported branch under {profile}"));
    // AdvSimd.Arm64 and AdvSimd share one answer, so ArmFlags is 0 or 3 and never 1 or 2.
    var armFlags = profile == "arm64-advsimd" ? 3 : 0;
    var armProof = Path.Combine(capabilities, "ArmFlags.lean");
    File.WriteAllText(armProof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        "theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = " +
        $".ok [.scalar (.i32 {armFlags})] := rfl\n#print axioms correctness\nend ExampleProof\n");
    capabilitiesQueue.Add(
        new("Capabilities::ArmFlags()", armProof, Path.Combine(capabilities, "ArmFlags"), Profile: profile),
        () => Console.WriteLine($"PASS AdvSimd.Arm64 follows AdvSimd under {profile}: {armFlags}"));
    var endianProof = Path.Combine(capabilities, "Endian.lean");
    File.WriteAllText(endianProof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
        "theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = " +
        ".ok [.scalar (.i32 1)] := rfl\n#print axioms correctness\nend ExampleProof\n");
    capabilitiesQueue.Add(
        new("Capabilities::Endian()", endianProof, Path.Combine(capabilities, "Endian"), Profile: profile),
        () => Console.WriteLine($"PASS BitConverter.IsLittleEndian prunes the big-endian branch under {profile}"));
}
// x64-v4 excludes VBMI; a custom v4 profile that declares it reads both getters as true.
var vbmiProfile = Path.Combine(output, "x64-v4-vbmi.json");
var vbmiNode = JsonSerializer.SerializeToNode(SelectProfile("x64-v4"), jsonOptions)!;
vbmiNode["name"] = "x64-v4-vbmi";
vbmiNode["avx512Vbmi"] = true;
File.WriteAllText(vbmiProfile, vbmiNode.ToJsonString());
foreach (var (profile, label, vbmiFlags) in new[]
{
    ("scalar", "scalar", 0), ("x64-v3", "x64-v3", 0), ("x64-v4", "x64-v4", 0), ("arm64-advsimd", "arm64-advsimd", 0),
    ($"@{vbmiProfile}", "x64-v4-vbmi", 3)
})
{
    var vbmiFolder = Path.Combine(output, $"Vbmi-{label}");
    Directory.CreateDirectory(vbmiFolder);
    var vbmiProof = Path.Combine(vbmiFolder, "VbmiFlags.lean");
    File.WriteAllText(vbmiProof, $$"""
        import Extracted
        import Examples.Support
        namespace ExampleProof
        theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd =
            .ok [.scalar (.i32 {{vbmiFlags}})] := rfl
        #print axioms correctness
        end ExampleProof

        """);
    capabilitiesQueue.Add(
        new("Capabilities::VbmiFlags()", vbmiProof, Path.Combine(vbmiFolder, "VbmiFlags"), Profile: profile),
        () => Console.WriteLine($"PASS Avx512Vbmi.VL follows Avx512Vbmi under {label}: {vbmiFlags}"));
}
// The unmodeled VBMI body is pruned under x64-v4 and blocks extraction when VBMI is declared.
foreach (var (profile, label) in new[] { ("x64-v4", "x64-v4"), ($"@{vbmiProfile}", "x64-v4-vbmi") })
{
    var result = Execute(Extract("extract", assembly, "Examples", "Capabilities::VbmiCount(ulong)",
        Path.Combine(output, $"VbmiCount-{label}"), profile));
    var blocked = result.Output.Contains("External managed dependency", StringComparison.Ordinal) &&
        result.Output.Contains("Avx512Vbmi/VL::PermuteVar32x8", StringComparison.Ordinal);
    if (label == "x64-v4-vbmi" ? result.Code == 0 || !blocked : result.Code != 0)
        throw new InvalidOperationException($"Avx512Vbmi.VL branch selection failed under {label}:\n{result.Output}");
    Console.WriteLine($"PASS Avx512Vbmi.VL selects the {(blocked ? "rejected VBMI" : "portable")} body under {label}");
}
var vbmi2 = Execute(Extract("extract", assembly, "Examples", "Capabilities::Vbmi2()",
    Path.Combine(output, "Unclassified-Vbmi2"), $"@{vbmiProfile}"));
if (vbmi2.Code == 0 || !vbmi2.Output.Contains(
        "Unclassified feature getter: System.Boolean System.Runtime.Intrinsics.X86.Avx512Vbmi2/VL::get_IsSupported()",
        StringComparison.Ordinal))
    throw new InvalidOperationException($"Avx512Vbmi2.VL getter was classified:\n{vbmi2.Output}");
Console.WriteLine("PASS unmeasured AVX-512 getter rejected: Avx512Vbmi2/VL");
// The unmodeled ARM64 body is pruned without AdvSimd and blocks extraction with it.
foreach (var profile in new[] { "scalar", "x64-v4", "arm64-advsimd" })
{
    var result = Execute(Extract("extract", assembly, "Examples", "Capabilities::ArmCount(ulong)",
        Path.Combine(output, "ArmCount-" + profile), profile));
    var blocked = result.Output.Contains("External managed dependency", StringComparison.Ordinal) &&
        result.Output.Contains("ArmBase/Arm64::LeadingSignCount", StringComparison.Ordinal);
    if (profile == "arm64-advsimd" ? result.Code == 0 || !blocked : result.Code != 0)
        throw new InvalidOperationException($"AdvSimd.Arm64 branch selection failed under {profile}:\n{result.Output}");
    var body = blocked ? "rejected ARM64" : "portable";
    Console.WriteLine($"PASS AdvSimd.Arm64 selects the {body} body under {profile}");
}
foreach (var (method, owner) in new[] { ("Crc64", "Crc32/Arm64"), ("Rdm64", "Rdm/Arm64") })
{
    var result = Execute(Extract("extract", assembly, "Examples", $"Capabilities::{method}()",
        Path.Combine(output, "Unclassified-" + method), "arm64-advsimd"));
    if (result.Code == 0 || !result.Output.Contains(
            $"Unclassified feature getter: System.Boolean System.Runtime.Intrinsics.Arm.{owner}::get_IsSupported()",
            StringComparison.Ordinal))
        throw new InvalidOperationException($"Nested ARM64 getter was classified: {owner}\n{result.Output}");
    Console.WriteLine("PASS unmeasured nested ARM64 getter rejected: " + owner);
}
var referenceQueryFolder = Path.Combine(output, "ReferenceQuery");
Directory.CreateDirectory(referenceQueryFolder);
var referenceQueryProof = Path.Combine(referenceQueryFolder, "Proof.lean");
var referenceResult = Assembly.Load(File.ReadAllBytes(assembly)).GetType("Examples.Capabilities")!
    .GetMethod("ReferenceFree")!.Invoke(null, null);
if (!Equals(referenceResult, 73)) throw new InvalidOperationException("Unexpected CLR reference-content result");
File.WriteAllText(referenceQueryProof, "import Extracted\nimport Examples.Support\nnamespace ExampleProof\n" +
    "theorem correctness : (CIL.Safety.invoke Extracted.program 64 0 [] Examples.empty).map Prod.snd = " +
    ".ok [.scalar (.i32 73)] := rfl\n#print axioms correctness\nend ExampleProof\n");
capabilitiesQueue.Add(new("Capabilities::ReferenceFree()", referenceQueryProof,
    Path.Combine(referenceQueryFolder, "Verified")),
    () => Console.WriteLine("PASS validated reference-free queries and pruned unsupported branch"));
capabilitiesQueue.Flush();
var referenceQuerySource = File.ReadAllText(Path.Combine(referenceQueryFolder, "Verified", "Extracted.lean"));
var queryControls = new GeneratedEvidence(Path.Combine(output, "ReferenceQueryControls"));
foreach (var obligation in new[] { featureObligation, "method0_scalars_validated" })
{
    var narrowed = NarrowEvidence(referenceQuerySource, obligation);
    var controlPath = Path.Combine(output, obligation + "-reference-query.lean");
    File.WriteAllText(controlPath, narrowed);
    queryControls.Add(controlPath, "PASS exact reference-content control: " + obligation, obligation);
    var aggregate = Regex.Match(narrowed, "typeArguments := \\[\\.aggregate \"[^\"]+\" [0-9]+\\]").Value;
    if (aggregate.Length == 0) throw new InvalidOperationException("Missing query-only aggregate layout");
    foreach (var (name, before, after) in new[]
    {
        ("answer", ".const32 0", ".const32 1"),
        ("scope", ".atom Extraction.runtimeScope \"System.Runtime.CompilerServices.RuntimeHelpers\"",
            ".atom \"forged\" \"System.Runtime.CompilerServices.RuntimeHelpers\""),
        ("byref", "typeArguments := [.atom Extraction.runtimeScope \"System.Int32\"]",
            "typeArguments := [.byref (.atom Extraction.runtimeScope \"System.Int32\")]"),
        ("layout", aggregate, Regex.Replace(aggregate, "\"[^\"]+\"", "\"forged\"")),
        ("signature", "parameterCount := 0, hasThis := false, returnsValue := true",
            "parameterCount := 1, hasThis := false, returnsValue := true")
    })
    {
        var changed = narrowed.Replace(before, after, StringComparison.Ordinal);
        if (changed == narrowed) throw new InvalidOperationException("Missing reference-query mutation: " + name);
        var forged = Path.Combine(output, obligation + "-reference-query-" + name + ".lean");
        File.WriteAllText(forged, changed);
        rejected.Add(forged, "PASS reference-content forgery rejected: " + name + " " + obligation,
            obligation == featureObligation ? "FeatureFlowValid" : "ScalarFlowValid");
    }
}
queryControls.Check(replay: false);
// A cached type validation belongs to its module and architecture within this request.
using (var module = ModuleDefinition.ReadModule(assembly))
using (var other = ModuleDefinition.CreateModule("OtherQueryOwner", ModuleKind.Dll))
using (var scope = (IDisposable)profileType.Assembly.GetType("Nethermind.LeanCIL.EnumTypes", true)!
    .GetMethod("BeginScope", BindingFlags.Static | BindingFlags.NonPublic)!.Invoke(null, null)!)
{
    var validate = profileType.Assembly.GetType("Nethermind.LeanCIL.ReferenceQueries", true)!
        .GetMethod("Constant", BindingFlags.Static | BindingFlags.NonPublic)!;
    var method = module.Types.Single(type => type.FullName == "Examples.Capabilities")
        .Methods.Single(method => method.Name == "ReferenceFree");
    var validQuery = method.Body.Instructions.Select(instruction => instruction.Operand)
        .OfType<GenericInstanceMethod>().Single(call => call.GenericArguments[0].Name == "EnumRecord");
    if (!Equals(validate.Invoke(null, [validQuery, "scalar"]), 0) ||
        !Equals(validate.Invoke(null, [validQuery, "scalar"]), 0))
        throw new InvalidOperationException("Reference-content cache control failed");
    var owner = validQuery.DeclaringType;
    var definition = new MethodReference(validQuery.Name, validQuery.ReturnType,
        new TypeReference(owner.Namespace, owner.Name, other, owner.Scope))
        { CallingConvention = MethodCallingConvention.Generic };
    definition.GenericParameters.Add(new GenericParameter("T", definition));
    var foreignQuery = new GenericInstanceMethod(definition);
    foreignQuery.GenericArguments.Add(validQuery.GenericArguments[0]);
    try
    {
        _ = validate.Invoke(null, [foreignQuery, "scalar"]);
        throw new InvalidOperationException("Reference-content cache crossed module contexts");
    }
    catch (TargetInvocationException exception) when (exception.InnerException is InvalidDataException invalidQuery &&
        invalidQuery.Message.Contains("Unsupported reference-content query type", StringComparison.Ordinal)) { }
    Console.WriteLine("PASS reference-content cache retains module context");
}
foreach (var mutation in new[] { "span", "byref", "pointer", "class", "float", "reference-field", "scope" })
{
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = module.Types.Single(type => type.FullName == "Examples.Capabilities")
        .Methods.Single(method => method.Name == "ReferenceFree");
    var query = (GenericInstanceMethod)method.Body.Instructions
        .First(instruction => instruction.Operand is GenericInstanceMethod call &&
            call.Name == "IsReferenceOrContainsReferences").Operand;
    var integer = query.GenericArguments[0];
    var diagnostic = "Unsupported reference-content query type";
    switch (mutation)
    {
        case "span":
            var span = new GenericInstanceType(new TypeReference("System", "Span`1", module, integer.Scope, true));
            span.GenericArguments.Add(integer);
            query.GenericArguments[0] = span;
            break;
        case "byref": query.GenericArguments[0] = new ByReferenceType(integer); break;
        case "pointer": query.GenericArguments[0] = new PointerType(integer); break;
        case "class": query.GenericArguments[0] = module.TypeSystem.Object; break;
        case "float": query.GenericArguments[0] = module.TypeSystem.Single; break;
        case "reference-field":
            var record = module.Types.Single(type => type.FullName == "Examples.EnumRecord");
            record.Fields[0].FieldType = module.TypeSystem.Object;
            query.GenericArguments[0] = record;
            diagnostic = "Unsupported field type";
            break;
        case "scope":
            query.ElementMethod.DeclaringType.Scope = new AssemblyNameReference("Forged", new Version(10, 0));
            diagnostic = "Unsupported reference-content query signature";
            break;
    }
    var modified = Path.Combine(referenceQueryFolder, mutation + ".dll");
    module.Write(modified);
    var result = Execute(Extract("extract", modified, "Examples", "Capabilities::ReferenceFree()",
        Path.Combine(referenceQueryFolder, mutation)));
    if (result.Code == 0 || !result.Output.Contains(diagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException("Unsupported query failed for the wrong reason: " + mutation +
            "\n" + result.Output);
    Console.WriteLine("PASS unsupported reference-content query rejected: " + mutation);
}
foreach (var mutation in new[] { "missing-switch-target", "switch-tail-interior", "branch-tail-interior" })
{
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = module.Types.Single(type => type.FullName == "Examples.Capabilities")
        .Methods.Single(method => method.Name == "Platform");
    var instructions = method.Body.Instructions;
    var table = (Instruction[])instructions.Single(instruction => instruction.OpCode.Code == Code.Switch).Operand;
    var tailCall = Instruction.Create(OpCodes.Call, method);
    instructions.Add(Instruction.Create(OpCodes.Tail));
    instructions.Add(tailCall);
    instructions.Add(Instruction.Create(OpCodes.Ret));
    if (mutation == "branch-tail-interior")
    {
        var branch = instructions.First(instruction => instruction.OpCode.Code is Code.Bne_Un or Code.Bne_Un_S);
        branch.OpCode = OpCodes.Bne_Un;
        branch.Operand = tailCall;
    }
    else
    {
        var missing = Instruction.Create(OpCodes.Nop);
        missing.Offset = int.MaxValue;
        table[1] = mutation == "missing-switch-target" ? missing : tailCall;
    }
    var mutatedAssembly = Path.Combine(output, mutation + ".dll");
    module.Write(mutatedAssembly);
    var result = Execute(Extract("extract", mutatedAssembly, "Examples", "Capabilities::Platform()",
        Path.Combine(output, mutation)));
    var diagnostic = mutation == "missing-switch-target" ? "Malformed switch targets" : "middle of a tail transfer";
    if (result.Code == 0 || !result.Output.Contains(diagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException("Invalid unselected target accepted: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS invalid unselected control-flow target rejected: " + mutation);
}
var platformSource = File.ReadAllText(Path.Combine(output, "Capabilities-scalar", "Platform", "Extracted.lean"));
var platformControls = new GeneratedEvidence(Path.Combine(output, "PlatformControls"));
foreach (var (obligation, diagnostic) in new[]
{
    ("method0_features_validated", "FeatureFlowValid"), ("method0_scalars_validated", "ScalarFlowValid")
})
{
    var narrowed = NarrowEvidence(platformSource, obligation);
    var controlPath = Path.Combine(output, obligation + "-platform.lean");
    File.WriteAllText(controlPath, narrowed);
    platformControls.Add(controlPath, "PASS exact platform constant control: " + diagnostic, obligation);
    const string literal = ".const32 8";
    var position = narrowed.IndexOf(literal, StringComparison.Ordinal);
    if (position < 0) throw new InvalidOperationException("Missing initial platform getter constant");
    var forged = Path.Combine(output, obligation + "-wrong-platform.lean");
    File.WriteAllText(forged, narrowed[..position] + ".const32 4" + narrowed[(position + literal.Length)..]);
    rejected.Add(forged, "PASS exact platform constant rejection: " + diagnostic, diagnostic);
}
platformControls.Check(replay: false);
// Lean binds the raw endianness load to System.Runtime's BitConverter Boolean and the value 1.
var endianSource = File.ReadAllText(Path.Combine(output, "Capabilities-scalar", "Endian", "Extracted.lean"));
var endianControls = new GeneratedEvidence(Path.Combine(output, "EndianControls"));
foreach (var (obligation, diagnostic) in new[]
{
    (featureObligation, "FeatureFlowValid"), ("method0_scalars_validated", "ScalarFlowValid")
})
{
    var narrowed = NarrowEvidence(endianSource, obligation);
    var controlPath = Path.Combine(output, obligation + "-endian.lean");
    File.WriteAllText(controlPath, narrowed);
    endianControls.Add(controlPath, "PASS exact endianness constant control: " + diagnostic, obligation);
    const string literal = ".const32 1";
    var position = narrowed.IndexOf(literal, StringComparison.Ordinal);
    if (position < 0) throw new InvalidOperationException("Missing endianness constant");
    var forgedValue = Path.Combine(output, obligation + "-wrong-endian.lean");
    File.WriteAllText(forgedValue, narrowed[..position] + ".const32 0" + narrowed[(position + literal.Length)..]);
    rejected.Add(forgedValue, "PASS endianness constant value rejection: " + diagnostic, diagnostic);
    const string owner = ".atom Extraction.runtimeScope \"System.BitConverter\"";
    if (!narrowed.Contains(owner, StringComparison.Ordinal))
        throw new InvalidOperationException("Missing endianness owner");
    var forgedOwner = Path.Combine(output, obligation + "-forged-endian-owner.lean");
    File.WriteAllText(forgedOwner,
        narrowed.Replace(owner, ".atom \"forged\" \"System.BitConverter\"", StringComparison.Ordinal));
    rejected.Add(forgedOwner, "PASS endianness owner forgery rejection: " + diagnostic, diagnostic);
}
endianControls.Check(replay: false);
foreach (var mutation in new[] { "scope", "field", "module-type" })
{
    using var module = ModuleDefinition.ReadModule(assembly);
    var method = module.Types.Single(type => type.FullName == "Examples.Capabilities")
        .Methods.Single(method => method.Name == "Endian");
    var load = method.Body.Instructions.Single(instruction => instruction.OpCode.Code == Code.Ldsfld);
    var field = (FieldReference)load.Operand;
    var diagnostic = "Only System.Runtime's static readonly BitConverter.IsLittleEndian is a platform constant";
    switch (mutation)
    {
        case "scope": field.DeclaringType.Scope = new AssemblyNameReference("Forged", new Version(10, 0)); break;
        case "field":
            load.Operand = new FieldReference("IsBigEndian", field.FieldType, field.DeclaringType);
            diagnostic = "Only same-assembly static readonly";
            break;
        case "module-type":
            const Mono.Cecil.TypeAttributes staticClass = Mono.Cecil.TypeAttributes.Public |
                Mono.Cecil.TypeAttributes.Abstract | Mono.Cecil.TypeAttributes.Sealed;
            const Mono.Cecil.FieldAttributes readonlyStatic = Mono.Cecil.FieldAttributes.Public |
                Mono.Cecil.FieldAttributes.Static | Mono.Cecil.FieldAttributes.InitOnly;
            var forged = new TypeDefinition("System", "BitConverter", staticClass, module.TypeSystem.Object);
            var forgedField = new FieldDefinition("IsLittleEndian", readonlyStatic, module.TypeSystem.Boolean);
            forged.Fields.Add(forgedField);
            module.Types.Add(forged);
            load.Operand = forgedField;
            break;
    }
    var modified = Path.Combine(output, "endian-" + mutation + ".dll");
    module.Write(modified);
    var result = Execute(Extract("extract", modified, "Examples", "Capabilities::Endian()",
        Path.Combine(output, "endian-" + mutation)));
    if (result.Code == 0 || !result.Output.Contains("Unsupported static field load", StringComparison.Ordinal) ||
        !result.Output.Contains(diagnostic, StringComparison.Ordinal))
        throw new InvalidOperationException(
            "Endianness lookalike accepted or misreported: " + mutation + "\n" + result.Output);
    Console.WriteLine("PASS endianness lookalike rejected: " + mutation);
}
var comparisonEvidence = NarrowEvidence(platformSource, featureObligation);
foreach (var (name, before, after) in new[]
{
    ("branch", ".bne ", ".beq "), ("signedness", ".gt,", ".gtu,"),
    ("unsigned-comparison", ".ltu,", ".lt,")
})
{
    if (!comparisonEvidence.Contains(before, StringComparison.Ordinal))
        throw new InvalidOperationException("Missing comparison mutation target: " + name);
    var forged = Path.Combine(output, "wrong-comparison-" + name + ".lean");
    File.WriteAllText(forged, comparisonEvidence.Replace(before, after, StringComparison.Ordinal));
    rejected.Add(forged, "PASS exact constant comparison rejection: " + name, "FeatureFlowValid");
}
rejected.Check();
var scalarCapabilities = Path.Combine(output, "Capabilities-scalar");
verification.Verify(assembly, "Examples", "Capabilities::Flags()", Path.Combine(scalarCapabilities, "Proof.lean"),
    Path.Combine(scalarCapabilities, "Verified"), check: true);
var wrongProfileRejected = false;
try
{
    verification.Verify(assembly, "Examples", "Capabilities::Flags()", Path.Combine(scalarCapabilities, "Proof.lean"),
        Path.Combine(scalarCapabilities, "Verified"), "x64-v3", check: true);
}
catch (InvalidOperationException error) when (
    error.Message.Contains("differs from regenerated CIL", StringComparison.Ordinal))
{
    wrongProfileRejected = true;
}
if (!wrongProfileRejected) throw new InvalidOperationException("A mixed-profile report accepted the wrong profile");
Console.WriteLine("PASS mixed-profile batch report preserves its extraction profile");
// A custom profile names the rule it breaks.
var noBase = Path.Combine(output, "bmi2-without-x86base.json");
File.WriteAllText(noBase, """
    { "name": "bmi2-only", "architecture": "x64", "nativeWidth": 64, "littleEndian": true, "advSimd": false, "sse2": false,
      "ssse3": false, "sse42": false, "avx": false, "avx2": false, "avx512F": false, "avx512FVL": false, "bmi1": false,
      "sse41": false, "avx512DQ": false, "avx512DQVL": false, "bmi2": true, "armBase64": false, "vector256Accelerated": false,
      "x86Base64": false, "vector128Accelerated": false, "avx512Vbmi": false }
    """);
var invalid = Execute(Extract("extract", assembly, "Examples", "Capabilities::Flags()", Path.Combine(output, "Reject-profile"), "@" + noBase));
if (invalid.Code == 0 || !invalid.Output.Contains("bmi2-only: x86 ISA flags require x86Base64"))
    throw new InvalidOperationException("Profile without X86Base64 was not rejected by name: " + invalid.Output);
Console.WriteLine("PASS x86 ISA flags without X86Base64 rejected with the rule");
Console.WriteLine("PASS raw feature analysis, join/backedge weakening, local eligibility, switches and emitted-code binding");
