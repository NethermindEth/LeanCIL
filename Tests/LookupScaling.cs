#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification/Verification.cs
#:include ../scripts/Checking/DeepChecks.cs
#:include ../scripts/Checking/FailureReports.cs
#:include ../scripts/Checking/LeanDiagnostics.cs
#:include ../scripts/Checking/BindingImage.cs
#:include ../scripts/Checking/DeepCheckInputs.cs
#:include GeneratedEvidence.cs
#:include ../Extractor/ProgramLookupFacts.cs
#:include ../Extractor/ObjectOperandProof.cs
#:include ../Extractor/PlatformDefinitions.cs
#:include ../Extractor/ByteLiterals.cs
#:package Mono.Cecil

using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;
using Nethermind.LeanCIL;

if (args.Contains("--object-admission-only", StringComparer.Ordinal))
{
    ShapeResolutionCosts(admissionOnly: true);
    return;
}
if (args.Contains("--layout-identities-only", StringComparer.Ordinal))
{
    LayoutIdentityCosts().Invoke();
    return;
}
if (args.Contains("--exception-types-only", StringComparer.Ordinal))
{
    ExceptionDecisionCosts();
    return;
}
if (args.Contains("--closed-arguments-only", StringComparer.Ordinal))
{
    ClosedArgumentsCosts();
    return;
}
if (args.Contains("--argument-resolution-only", StringComparer.Ordinal))
{
    ArgumentResolutionCosts();
    return;
}
if (args.Contains("--element-shape-only", StringComparer.Ordinal))
{
    ElementShapeCosts();
    return;
}
if (args.Contains("--shape-resolution-only", StringComparer.Ordinal))
{
    ShapeResolutionCosts();
    return;
}
if (args.Contains("--indirect-access-only", StringComparer.Ordinal))
{
    IndirectAccessCosts();
    return;
}
if (args.Contains("--call-check-only", StringComparer.Ordinal))
{
    CallCheckCosts();
    return;
}
if (args.Contains("--decode-only", StringComparer.Ordinal))
{
    DecodeCosts();
    return;
}
if (args.Contains("--method-decode-only", StringComparer.Ordinal))
{
    MethodDecodeCosts();
    return;
}
if (args.Contains("--static-facts-only", StringComparer.Ordinal))
{
    StaticFactCosts();
    StaticIdentityCosts();
    return;
}
if (args.Contains("--decoded-definition-only", StringComparer.Ordinal))
{
    DecodedDefinitionCosts();
    return;
}
if (args.Contains("--decoded-program-only", StringComparer.Ordinal))
{
    DecodedProgramCosts();
    return;
}
if (args.Contains("--closure-only", StringComparer.Ordinal))
{
    ClosureCosts();
    return;
}
if (args.Contains("--run-only", StringComparer.Ordinal))
{
    RunCosts();
    return;
}
if (args.Contains("--return-step-only", StringComparer.Ordinal))
{
    ReturnResolutionCosts(stepOnly: true);
    return;
}
if (args.Contains("--metadata-name-only", StringComparer.Ordinal))
{
    MetadataNameCosts();
    return;
}
if (args.Contains("--model-table-only", StringComparer.Ordinal))
{
    ModelTableCosts();
    return;
}
if (args.Contains("--import-links-only", StringComparer.Ordinal))
{
    ImportLinkCosts();
    return;
}
if (args.Contains("--platform-table-only", StringComparer.Ordinal))
{
    PlatformTableCosts();
    return;
}
if (args.Contains("--indirect-target-only", StringComparer.Ordinal))
{
    IndirectTargetCosts();
    return;
}
if (args.Contains("--lineage-only", StringComparer.Ordinal))
{
    LineageCosts();
    return;
}
if (args.Contains("--prefix-entry-only", StringComparer.Ordinal))
{
    PrefixEntryCosts();
    return;
}
var instructionEquationsOnly = args.Contains("--instruction-equations-only", StringComparer.Ordinal);
// Each of these options runs the leading checks in order and stops after the ones it names.
if (args.Contains("--native-table-only", StringComparer.Ordinal) ||
    args.Contains("--return-evidence-only", StringComparer.Ordinal) ||
    args.Contains("--return-resolution-only", StringComparer.Ordinal))
{
    NativeTableCosts();
    if (args.Contains("--native-table-only", StringComparer.Ordinal)) return;
    ExceptionDecisionCosts();
    CheckNarrowedResolution();
    if (args.Contains("--return-evidence-only", StringComparer.Ordinal)) return;
    ReturnResolutionCosts();
    ArgumentResolutionCosts();
    ElementShapeCosts();
    ShapeResolutionCosts();
    LineageCosts();
    return;
}

// `cil_instruction_equations` proves each equation from the code suffix that starts its block. Proved
// against the whole code list instead, it walks one cell per preceding instruction and a method's equations
// cost quadratic time, which this fixture reports as a per-instruction cost that grows with the method.
const int ShortStatements = 125;
const int MiddleStatements = 250;
const int LongStatements = 500;
// Compiling four times the instructions may cost at most this much more per instruction.
const double AllowedGrowth = 1.15;
const int FewCalls = 100;
const int ManyCalls = 400;
// Link reads whose cost grows with the square of the calls make the recheck of an embedding cost 1.29 times as
// much per call at 2,048 calls as at 512; linear reads cost the same.
const int EmbedFewCalls = 512;
const int EmbedManyCalls = 2048;
// Segments in each of the two blocks of an embedding whose pc map puts the second block first.
const int ReorderFewSegments = 128;
const int ReorderManySegments = 512;
// Four times the calls of an embedding may cost at most this much more per call.
const double AllowedEmbedGrowth = 1.15;
// Two calls in bodies of these many statements: the link output must not grow with the body.
const int SparseShortStatements = 250;
const int SparseLongStatements = 1000;
// Four times the call sites may cost at most this much more per call site.
const double AllowedCallGrowth = 1.35;
// Type identities compare one code per name, so a name four times as long may cost at most this much more.
const double AllowedNameGrowth = 1.05;
// A model table sixteen times as large may cost a lookup at most this much more.
const double AllowedModelLookupGrowth = 1.05;
// The most heartbeats deciding equality or inequality of two type identities may cost at either name length.
const long TypeDecisionLimit = 9_500;
// `decide +kernel` costs about 2,000 heartbeats for any statement; less means the decision was not measured.
const long KernelDecisionFloor = 2_000;
// Bodies of these many array element addresses. A readonly rule that scans the body at every address costs
// about 1.5 times as much per address at each doubling.
const int FewAddresses = 128;
const int MoreAddresses = 256;
const int ManyAddresses = 512;
// Bodies of these many local loads, stores, addresses and pops, which cycle over four int32 locals.
const int FewLocalAccesses = 256;
const int MoreLocalAccesses = 1024;
const int ManyLocalAccesses = 4096;
// Bodies of these many locals, each stored once and then loaded or addressed. A check that walks the locals list,
// or the list of locals a `calli` consumes, at each such site costs between 1.3 and 2.3 times as much per
// instruction at 512 as at 128; reading indexes built once per body costs at most about 1.1 times as much.
const int FewLocals = 128;
const int MoreLocals = 256;
const int ManyLocals = 512;
// Four times the locals may cost at most this much more per instruction; the closed argument storage reads a set
// of pointer locals whose lookups cost the logarithm of the locals.
const double AllowedLocalGrowth = 1.25;
// Bodies of a fixed length over these many int32 locals, cycling through every local. Feature states list known
// facts alone, so a body that stores no constant costs the same per instruction at every local count.
const int FewFeatureLocals = 16;
const int MoreFeatureLocals = 64;
const int ManyFeatureLocals = 256;
const int FeatureLocalSegments = 256;
const int FeatureLocalInstructions = 8 * FeatureLocalSegments + 1;
// Bodies over `ManyKnownFacts` int32 locals that store zero into the first few, more or many of them, then store a
// new word into each in turn and load it back for `KnownFactRounds` rounds; every loop state holds every fact.
const int FewKnownFacts = 4;
const int MoreKnownFacts = 16;
const int ManyKnownFacts = 64;
const int KnownFactRounds = 128;
// Linear growth makes the increment from 16 to 64 facts four times the one from 4 to 16; at about 400 heartbeats per
// fact, a quadratic term of one heartbeat per fact pair in each state exceeds this ratio.
const double AllowedFactIncrementRatio = 4.5;

// Lean processes reserve these while concurrent checks run: the measured peak working sets reach 8.8 GiB for the
// largest inputs and 4.8 GiB for the next size down.
const long LargeLeanProcess = 9L << 30;
const long MediumLeanProcess = 5L << 30;

// The reservation of the address checks: their two larger sizes are the only ones above the default.
static long AddressMemory(int sites) =>
    sites == ManyAddresses ? LargeLeanProcess : sites == MoreAddresses ? MediumLeanProcess : 0;

var directory = At("artifacts/LookupScaling");
Directory.CreateDirectory(directory);
if (!instructionEquationsOnly)
{
    // Checks that time Lean run alone, and the libraries the other checks import are built first.
    ModelTableCosts();
    ClosureCosts();
    DecodeCosts();
    Run(["dotnet", "run", "--file", At("Tests/MetadataFieldPrefixes.cs"), "-c", "Release"]);
    BuildLeanTestLibraries("Certificate index, feature getter, layout projection and home index libraries",
        "Tests.FlowIndex", "Tests.CertificateFlow", "Tests.FeatureGetter", "Tests.ExtractionHomeIndexes",
        "Tests.LayoutProjectionIndexes");
}

// Signature facts inspect a return head; code and unrelated layout entries stay outside that inspection.
void ReturnResolutionCosts(bool stepOnly = false)
{
    var resolutionDirectory = At("artifacts/LookupScaling/ReturnResolution");
    Directory.CreateDirectory(resolutionDirectory);
    const double GrowthLimit = AllowedLocalGrowth;
    static bool WithinGrowth((int Size, double Cost)[] samples, bool perItem)
    {
        double Normalized((int Size, double Cost) sample) => sample.Cost / (perItem ? sample.Size : 1);
        return samples.Skip(1).All(sample => Normalized(sample) <= Normalized(samples[0]) * GrowthLimit);
    }
    int[] controlSizes = [32, 128, 512];
    if (!WithinGrowth(controlSizes.Select(size => (size, (double)size)).ToArray(), perItem: true) ||
        WithinGrowth(controlSizes.Select(size => (size, (double)size * size)).ToArray(), perItem: true) ||
        !WithinGrowth(controlSizes.Select(size => (size, 32.0)).ToArray(), perItem: false) ||
        WithinGrowth(controlSizes.Select(size => (size, (double)size)).ToArray(), perItem: false))
        throw new InvalidOperationException("Return resolution growth check failed its normalization controls.");
    var dimensions = stepOnly ? new[] { "step-methods", "step-body" } :
        ["methods", "body", "layouts", "enum-layouts", "step-methods", "step-body"];
    foreach (var dimension in dimensions)
    {
        var samples = new List<(int Size, long Facts, long Simplifier)>();
        foreach (var size in new[] { 32, 128, 512 })
        {
            var source = new StringBuilder("""
                import CIL.Safety.ValueSteps
                import CIL.Safety.StepComposition
                open CIL CIL.Extraction Lean Elab Command
                set_option maxRecDepth 8192
                /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
                elab "#resolution_cost " label:str " in " command:command : command => do
                  let before <- IO.getNumHeartbeats
                  elabCommand command
                  let after <- IO.getNumHeartbeats
                  logInfo m!"resolution {label.getString} {after - before} heartbeats"

                """);
            var type = ".primitive .byte";
            var expected = "some .unsigned8";
            if (dimension == "layouts")
            {
                type = ".aggregate \"Point\" 0";
                expected = "none";
            }
            if (dimension == "enum-layouts")
            {
                source.AppendLine("""
                    private def smallEnum : TypeIdentity :=
                      { assembly := runtimeAssembly, typeNamespace := name!"", name := name!"Small" }
                    """);
                type = ".enum smallEnum .unsigned8";
            }
            var instructions = dimension is "body" or "step-body"
                ? string.Join(", ", Enumerable.Repeat(".nop", size)) : "";
            var layouts = dimension is "layouts" or "enum-layouts" ? string.Join(", ", Enumerable.Repeat(
                "{ identity := \"Point\", explicit := false, packing := 0, declaredSize := 0, fields := [] }",
                size)) : "";
            source.AppendLine($"def rawLayouts : List RawLayout := [{layouts}]");
            var methods = dimension is "methods" or "step-methods" ? size : 1;
            for (var index = 0; index < methods; index++)
            {
                source.AppendLine($$"""
                    def body{{index}} : Method := {
                      code := [{{instructions}}], locals := [], returnsValue := true,
                      declared := { returnType := {{type}} }, environment := { rawLayouts := rawLayouts } }
                    theorem body{{index}}_returnsValue : body{{index}}.returnsValue = true := rfl
                    theorem body{{index}}_declared :
                      body{{index}}.declared = { returnType := {{type}} } := rfl
                    #resolution_cost "fact" in cil_resolution_facts body{{index}}
                    """);
                if (dimension.StartsWith("step-", StringComparison.Ordinal))
                    source.AppendLine($$"""
                    #resolution_cost "simplifier" in
                    theorem body{{index}}_simplified (frame : Safety.Frame) (memory : Safety.Memory) :
                        Safety.step body{{index}} .ret 0 [] frame [.scalar (.i32 300)] memory =
                          .ok (.returned [.scalar (.i32 44)] memory) := by
                      simp only [Safety.step_ret_eq, body{{index}}_returnsValue,
                        body{{index}}_returnNarrow]
                      rfl
                    """);
                else source.AppendLine($$"""
                    #resolution_cost "simplifier" in
                    theorem body{{index}}_simplified : body{{index}}.returnNarrow = {{expected}} := by
                      simp only [cil_step]
                    """);
                foreach (var suffix in new[] { "returnsValue", "declared", "returnNarrow", "simplified" })
                    source.AppendLine($"#print axioms body{index}_{suffix}");
            }
            var path = Path.Combine(resolutionDirectory, $"{dimension}{size}.lean");
            File.WriteAllText(path, source.ToString());
            var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
            if (output.Contains("sorryAx", StringComparison.Ordinal))
                throw new InvalidOperationException("Return resolution introduced an unproved theorem.");
            var costs = LookupPatterns.ReturnResolution.Matches(output).Cast<Match>().ToArray();
            if (costs.Length != methods * 2)
                throw new InvalidOperationException("Missing return resolution costs: " + output);
            long Sum(string label) => costs.Where(match => match.Groups[1].Value == label)
                .Sum(match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
            samples.Add((size, Sum("fact"), Sum("simplifier")));
        }
        foreach (var simplifier in new[] { false, true })
        {
            var measured = samples.Select(sample =>
                (sample.Size, (double)(simplifier ? sample.Simplifier : sample.Facts))).ToArray();
            if (!WithinGrowth(measured,
                perItem: dimension is "methods" or "step-methods"))
                throw new InvalidOperationException($"Superlinear return resolution {dimension}: " +
                    string.Join("; ", measured));
            Console.WriteLine($"PASS return resolution {(simplifier ? "simplifier" : "fact")} {dimension}: " +
                string.Join("; ", samples.Select(sample =>
                    $"{sample.Size} = {(simplifier ? sample.Simplifier : sample.Facts)} heartbeats")));
        }
    }
}

// Fails when argument facts or reads at 8, 32 and 128 parameters cost over 1.35 times more per argument than
// at the size before; evaluating parameters[index]? or searching homes gives 2.40x, 3.40x (2.48x, 3.46x homed).
void ArgumentResolutionCosts()
{
    const double AllowedArgumentGrowth = 1.35;
    var resolutionDirectory = At("artifacts/LookupScaling/ArgumentResolution");
    Directory.CreateDirectory(resolutionDirectory);
    const string Int32Type = ".primitive .int32";
    foreach (var homed in new[] { false, true })
    {
        var samples = new List<(int Size, long Facts, long Reads)>();
        foreach (var size in new[] { 8, 32, 128 })
        {
            // Each homed argument's slot follows the one declared local, in argument order.
            var slots = Enumerable.Range(0, size).Where(index => homed && index % 2 == 1)
                .Select((index, position) => (index, position))
                .ToDictionary(home => home.index, home => 1 + home.position);
            var homes = string.Join(", ", slots.Keys.Order().Select(index => $"({index}, .word32)"));
            var signature = $"{{ parameters := [{string.Join(", ", Enumerable.Repeat(Int32Type, size))}] }}";
            var code = string.Join(", ", Enumerable.Range(0, size).Select(index =>
                slots.TryGetValue(index, out var slot) ? $".ldloc {slot}, .pop" : $".ldarg {index}, .pop")) + ", .ret";
            var accesses = string.Join(", ", Enumerable.Range(0, size).Select(index =>
                slots.TryGetValue(index, out var slot) ? $".home {slot}" : ".value none"));
            var reads = string.Join(", ", Enumerable.Range(0, size).Select(index => $"body.argumentAccess {index}"));
            var source = $$"""
                import CIL.Safety.ValueSteps
                open CIL CIL.Extraction Lean Elab Command
                set_option maxRecDepth 8192
                /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
                elab "#resolution_cost " label:str " in " command:command : command => do
                  let before <- IO.getNumHeartbeats
                  elabCommand command
                  let after <- IO.getNumHeartbeats
                  logInfo m!"resolution {label.getString} {after - before} heartbeats"
                def body : Method := {
                  code := [{{code}}], locals := [.i32 0], localKinds := [.word32],
                  parameterHomes := [{{homes}}], returnsValue := false, declared := {{signature}} }
                theorem body_returnsValue : body.returnsValue = false := rfl
                theorem body_declared : body.declared = {{signature}} := rfl
                #resolution_cost "fact" in cil_resolution_facts body
                #resolution_cost "simplifier" in
                theorem body_reads : [{{reads}}] = [{{accesses}}] := by simp only [cil_code]
                #print axioms body_argumentAccess{{size - 1}}
                #print axioms body_reads
                """ + "\n";
            var path = Path.Combine(resolutionDirectory, $"{(homed ? "Homed" : "Unhomed")}{size}.lean");
            File.WriteAllText(path, source);
            var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
            if (output.Contains("sorryAx", StringComparison.Ordinal))
                throw new InvalidOperationException("Argument resolution introduced an unproved theorem.");
            var costs = LookupPatterns.ReturnResolution.Matches(output).Cast<Match>().ToArray();
            if (costs.Length != 2)
                throw new InvalidOperationException("Missing argument resolution costs: " + output);
            samples.Add((size, long.Parse(costs[0].Groups[2].Value, CultureInfo.InvariantCulture),
                long.Parse(costs[1].Groups[2].Value, CultureInfo.InvariantCulture)));
        }
        var label = homed ? "with every other argument homed" : "without homes";
        foreach (var (name, cost) in new (string, Func<(int Size, long Facts, long Reads), long>)[]
            { ("facts", sample => sample.Facts), ("reads", sample => sample.Reads) })
        {
            var perArgument = samples.Select(sample => (double)cost(sample) / sample.Size).ToArray();
            var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
                $"{sample.Size} = {(double)cost(sample) / sample.Size:F0}")));
            if (perArgument.Skip(1).Zip(perArgument).Any(pair => pair.First > pair.Second * AllowedArgumentGrowth))
                throw new InvalidOperationException(
                    $"Argument {name} {label} cost {measured} heartbeats per argument; the limit is " +
                    $"{AllowedArgumentGrowth} times the cost per argument at the size before.");
            Console.WriteLine($"PASS argument {name} {label}: {measured} heartbeats per argument");
        }
    }
}

// `cil_resolution_facts` states each static site's descriptor from one ascending check and the named site suffix
// of its block, so facts and the simplifier's reads of them at 8, 32 and 128 sites cost at most 1.35 times more
// per site than at the size before; a fact that searched the sites before it would grow with the size.
void StaticFactCosts()
{
    const double AllowedSiteGrowth = 1.35;
    var factDirectory = At("artifacts/LookupScaling/StaticFacts");
    Directory.CreateDirectory(factDirectory);
    var samples = new List<(int Size, long Facts, long Reads)>();
    foreach (var size in new[] { 8, 32, 128 })
    {
        string Descriptor(int index) => string.Create(CultureInfo.InvariantCulture,
            $"{{ identity := {index}, field := field, bytes := [{index % 256}] }}");
        var code = string.Join(", ", Enumerable.Repeat(".ldsfld field, .pop", size)) + ", .ret";
        var sites = string.Join(", ",
            Enumerable.Range(0, size).Select(index => $"({2 * index}, {Descriptor(index)})"));
        var reads = string.Join(", ", Enumerable.Range(0, size).Select(index => $"body.staticAt {2 * index}"));
        var resolved = string.Join(", ", Enumerable.Range(0, size).Select(index => $"some {Descriptor(index)}"));
        var source = $$"""
            import CIL.Safety.ResolutionFacts
            open CIL CIL.Extraction Lean Elab Command
            set_option maxRecDepth 8192
            /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
            elab "#resolution_cost " label:str " in " command:command : command => do
              let before <- IO.getNumHeartbeats
              elabCommand command
              let after <- IO.getNumHeartbeats
              logInfo m!"resolution {label.getString} {after - before} heartbeats"
            def field : FieldRef :=
              { owner := .atom "Fixture" "Holder" .classType, index := 0, type := .atom "Fixture" "Pair" .valueType,
                name := name!"Field" }
            def body : Method := {
              code := [{{code}}], locals := [], returnsValue := false, declared := {},
              staticSites := [{{sites}}] }
            theorem body_returnsValue : body.returnsValue = false := rfl
            theorem body_declared : body.declared = {} := rfl
            #resolution_cost "fact" in cil_resolution_facts body
            #resolution_cost "simplifier" in
            theorem body_reads : [{{reads}}] = [{{resolved}}] := by simp only [cil_code]
            #print axioms body_staticAt{{2 * (size - 1)}}
            #print axioms body_reads
            """ + "\n";
        var path = Path.Combine(factDirectory, $"Sites{size}.lean");
        File.WriteAllText(path, source);
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        if (output.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException("Static site facts introduced an unproved theorem.");
        var costs = LookupPatterns.ReturnResolution.Matches(output).Cast<Match>().ToArray();
        if (costs.Length != 2)
            throw new InvalidOperationException("Missing static site fact costs: " + output);
        samples.Add((size, long.Parse(costs[0].Groups[2].Value, CultureInfo.InvariantCulture),
            long.Parse(costs[1].Groups[2].Value, CultureInfo.InvariantCulture)));
    }
    foreach (var (name, cost) in new (string, Func<(int Size, long Facts, long Reads), long>)[]
        { ("facts", sample => sample.Facts), ("reads", sample => sample.Reads) })
    {
        var perSite = samples.Select(sample => (double)cost(sample) / sample.Size).ToArray();
        var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
            $"{sample.Size} = {(double)cost(sample) / sample.Size:F0}")));
        if (perSite.Skip(1).Zip(perSite).Any(pair => pair.First > pair.Second * AllowedSiteGrowth))
            throw new InvalidOperationException(
                $"Static site {name} cost {measured} heartbeats per site; the limit is " +
                $"{AllowedSiteGrowth} times the cost per site at the size before.");
        Console.WriteLine($"PASS static site {name}: {measured} heartbeats per site");
    }
}

// `StaticIdentitiesValid` reads each site's recorded token from one index of the body and inserts the site into two
// ordered maps, so deciding it at 8, 32 and 128 sites of distinct fields and identities costs at most
// AllowedIdentityGrowth times more per site than at the size before; comparing each site with every other would not.
void StaticIdentityCosts()
{
    const double AllowedIdentityGrowth = 1.35;
    var identityDirectory = At("artifacts/LookupScaling/StaticIdentities");
    Directory.CreateDirectory(identityDirectory);
    var samples = new List<(int Size, long Cost)>();
    foreach (var size in new[] { 8, 32, 128 })
    {
        var code = string.Join(", ", Enumerable.Repeat(".ldsfld field, .pop", size)) + ", .ret";
        var sites = string.Join(", ", Enumerable.Range(0, size).Select(index => string.Create(
            CultureInfo.InvariantCulture, $"({2 * index}, {{ identity := {index}, field := field, bytes := [0] }})")));
        var statics = string.Join(", ", Enumerable.Range(0, size).Select(index => string.Create(
            CultureInfo.InvariantCulture, $"({2 * index}, {0x04000001 + index})")));
        var source = $$"""
            import CIL.Extraction.StaticIdentities
            open CIL CIL.Extraction Lean Elab Command
            set_option maxRecDepth 8192
            /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
            elab "#identity_cost " command:command : command => do
              let before <- IO.getNumHeartbeats
              elabCommand command
              let after <- IO.getNumHeartbeats
              logInfo m!"static identities {after - before} heartbeats"
            def field : FieldRef :=
              { owner := .atom "Fixture" "Holder" .classType, index := 0, type := .atom "Fixture" "Pair" .valueType,
                name := name!"Field" }
            def body : Method := {
              code := [{{code}}], locals := [], returnsValue := false, declared := {},
              staticSites := [{{sites}}] }
            def evidence : BodyEvidence :=
              { bytes := [], tokens := { operands := [] }, metadata := {}, identities := [⟨name!"Fixture", ⟨1, 0, 0, 0⟩, name!"", none⟩],
                tables := [], names := {}, pinned := PinnedIndex.ofIdentities [], statics := [{{statics}}] }
            #identity_cost
            theorem identities_valid : StaticIdentitiesValid [body] [evidence] := by decide +kernel
            #print axioms identities_valid
            """ + "\n";
        var path = Path.Combine(identityDirectory, $"Sites{size}.lean");
        File.WriteAllText(path, source);
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        if (output.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException("The static identity check introduced an unproved theorem.");
        var cost = LookupPatterns.StaticIdentities.Match(output);
        if (!cost.Success) throw new InvalidOperationException("Missing static identity cost: " + output);
        samples.Add((size, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture)));
    }
    var perSite = samples.Select(sample => (double)sample.Cost / sample.Size).ToArray();
    var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
        $"{sample.Size} = {(double)sample.Cost / sample.Size:F0}")));
    if (perSite.Skip(1).Zip(perSite).Any(pair => pair.First > pair.Second * AllowedIdentityGrowth))
        throw new InvalidOperationException(
            $"Static identities cost {measured} heartbeats per site; the limit is " +
            $"{AllowedIdentityGrowth} times the cost per site at the size before.");
    Console.WriteLine($"PASS static identities: {measured} heartbeats per site");
}

// Fails when element shape facts or reads cost over 1.35 times more per element type as types and layouts grow
// together, or over 1.35 times more in total as sites of 8 types grow; per-site facts would grow with the sites.
void ElementShapeCosts()
{
    const double AllowedElementGrowth = 1.35;
    var shapeDirectory = At("artifacts/LookupScaling/ElementShapes");
    Directory.CreateDirectory(shapeDirectory);
    (string Name, Func<(int Size, long Facts, long Reads), long> Cost)[] measures =
        [("facts", sample => sample.Facts), ("reads", sample => sample.Reads)];
    // Both rows include 8 types at 8 sites; a sample is elaborated once and read by every row that includes it.
    var samples = new Dictionary<(int Types, int Sites), (int Size, long Facts, long Reads)>();
    (int Size, long Facts, long Reads) Sample(int types, int sites) =>
        samples.TryGetValue((types, sites), out var known) ? known
            : samples[(types, sites)] = ElementShapeSample(shapeDirectory, types, sites);
    var byType = new[] { 8, 32, 128 }.Select(size => (Count: size, Sample: Sample(size, size))).ToArray();
    foreach (var (name, cost) in measures)
    {
        var perElement = byType.Select(sample => (double)cost(sample.Sample) / sample.Count).ToArray();
        var measured = string.Join("; ", byType.Select(sample => string.Create(CultureInfo.InvariantCulture,
            $"{sample.Count} = {(double)cost(sample.Sample) / sample.Count:F0}")));
        if (perElement.Skip(1).Zip(perElement).Any(pair => pair.First > pair.Second * AllowedElementGrowth))
            throw new InvalidOperationException(
                $"Element shape {name} cost {measured} heartbeats per element type; the limit is " +
                $"{AllowedElementGrowth} times the cost per element type at the size before.");
        Console.WriteLine($"PASS element shape {name}: {measured} heartbeats per element type");
    }
    const int SharedTypes = 8;
    var bySite = new[] { 8, 32, 128 }.Select(sites =>
        (Count: sites, Sample: Sample(SharedTypes, sites))).ToArray();
    foreach (var (name, cost) in measures)
    {
        var totals = bySite.Select(sample => (double)cost(sample.Sample)).ToArray();
        var measured = string.Join("; ", bySite.Select(sample => string.Create(CultureInfo.InvariantCulture,
            $"{sample.Count} = {cost(sample.Sample)}")));
        if (totals.Skip(1).Zip(totals).Any(pair => pair.First > pair.Second * AllowedElementGrowth))
            throw new InvalidOperationException(
                $"Element shape {name} of {SharedTypes} types cost {measured} heartbeats by site count; the limit " +
                $"is {AllowedElementGrowth} times the cost at the site count before.");
        Console.WriteLine($"PASS element shape {name} of {SharedTypes} types: {measured} heartbeats by site count");
    }
}

// The heartbeats of the element shape facts of a method with `sites` struct element sites over `types` layouts, the
// site at position k naming layout k mod types, and of reading every type's shape through them.
(int Size, long Facts, long Reads) ElementShapeSample(string directory, int types, int sites)
{
    var indices = Enumerable.Range(0, types).ToArray();
    var raw = string.Join(",\n  ", indices.Select(index => $$"""
        { identity := "Cell{{index}}", explicit := false, packing := 0, declaredSize := 0, fields := [] }
        """));
    var computed = string.Join(",\n  ", indices.Select(index =>
        $$"""{ layout := { size := {{4 * (index + 1)}}, fields := [] }, alignment := 4 }"""));
    var code = string.Join(", ", Enumerable.Range(0, sites).Select(site =>
        $$"""⟨{{5 * site}}, 163, .type (.aggregate "Cell{{site % types}}" {{site % types}})⟩"""));
    var reads = string.Join(", ", indices.Select(index =>
        $$"""body.elementShape (.aggregate "Cell{{index}}" {{index}})"""));
    var shapes = string.Join(", ", indices.Select(index =>
        $$""".value (.aggregate "Cell{{index}}" {{4 * (index + 1)}})"""));
    var source = $$"""
        import CIL.Safety.ValueSteps
        open CIL CIL.Extraction Lean Elab Command
        set_option maxRecDepth 8192
        /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
        elab "#resolution_cost " label:str " in " command:command : command => do
          let before <- IO.getNumHeartbeats
          elabCommand command
          let after <- IO.getNumHeartbeats
          logInfo m!"resolution {label.getString} {after - before} heartbeats"
        def rawLayouts : List RawLayout := [
          {{raw}}]
        def computedLayouts : Array ComputedLayout := #[
          {{computed}}]
        def environment : LayoutEnvironment := { rawLayouts := rawLayouts, layouts := computedLayouts }
        def body : Method := { code := [.ret], locals := [], returnsValue := false, environment := environment }
        theorem body_returnsValue : body.returnsValue = false := rfl
        theorem body_declared : body.declared = {} := rfl
        def bodyClosed : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false, callingConvention := 0,
          attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
          initLocals := true, maxStack := 2, genericParameters := [], code := [{{code}}] }
        #resolution_cost "fact" in cil_resolution_facts body
        #resolution_cost "simplifier" in
        theorem body_reads : [{{reads}}] = [{{shapes}}] := by simp only [cil_code]
        #print axioms body_elementShape{{types - 1}}
        #print axioms body_reads
        """ + "\n";
    var path = Path.Combine(directory, $"Elements{types}Sites{sites}.lean");
    File.WriteAllText(path, source);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("Element shape facts introduced an unproved theorem.");
    var costs = LookupPatterns.ReturnResolution.Matches(output).Cast<Match>().ToArray();
    if (costs.Length != 2)
        throw new InvalidOperationException("Missing element shape costs: " + output);
    return (types, long.Parse(costs[0].Groups[2].Value, CultureInfo.InvariantCulture),
        long.Parse(costs[1].Groups[2].Value, CultureInfo.InvariantCulture));
}

// Fails when the shape facts or reads of distinct operands cost over 1.35 times more per operand than at the size
// before: fields of one struct up to 128, and fields and value types of a struct each up to 512, read by a
// 512-instruction body. A fact that walks the layouts to its struct costs 1.7 times as much per operand at 512 as
// at 128 for fields and 3.2 times for value types. Every row is measured before the first failure is reported.
void ShapeResolutionCosts(bool admissionOnly = false)
{
    const double AllowedShapeGrowth = 1.35;
    var resolutionDirectory = At("artifacts/LookupScaling/ShapeResolution");
    Directory.CreateDirectory(resolutionDirectory);
    (string Name, string Label, int[] Sizes, bool Spread, bool Value, bool Repeated)[] rows =
    [
        ("Struct", "field shape {0} with every field in one struct", [8, 32, 128], false, false, false),
        ("Spread", "field shape {0} with each field in its own struct", [8, 32, 128, 512], true, false, false),
        ("Value", "value shape {0} with each type a struct of its own", [8, 32, 128, 512], true, true, false),
        ("RepeatedValue", "value shape {0} at repeated sites of one struct", [8, 32, 128], true, true, true),
    ];
    var failures = new List<string>();
    foreach (var row in rows)
    {
        if (admissionOnly && row.Name != "Value") continue;
        var samples = new List<(int Size, long Facts, long Reads)>();
        var admission = new List<(int Sites, double Cost)>();
        foreach (var size in row.Sizes)
        {
            var measureAdmission = row.Name == "Value" && size <= 128;
            if (admissionOnly && !measureAdmission) continue;
            var output = RunShapeFixture(resolutionDirectory, row.Name, size, row.Spread, row.Value, row.Repeated,
                admissionOnly);
            var costs = LookupPatterns.ReturnResolution.Matches(output).Cast<Match>().ToArray();
            var shapeCosts = admissionOnly ? 0 : (row.Repeated ? 1 : size) + 1;
            if (costs.Length != shapeCosts + (measureAdmission ? 1 : 0))
                throw new InvalidOperationException("Missing shape resolution costs: " + output);
            long Sum(string label) => costs.Where(match => match.Groups[1].Value == label)
                .Sum(match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
            samples.Add((size, Sum("fact"), Sum("simplifier")));
            if (measureAdmission) admission.Add((size, (double)Sum("objects") / size));
        }
        foreach (var (previous, current) in admission.Zip(admission.Skip(1)))
            if (previous.Cost <= 0 || current.Cost <= 0 || current.Cost > previous.Cost * AllowedGrowth)
                failures.Add($"Object admission grew from {previous.Cost:F0} to {current.Cost:F0} heartbeats/site.");
        foreach (var sample in admission)
            Console.WriteLine($"Object admission at {sample.Sites} distinct layouts: {sample.Cost:F0} heartbeats/site");
        if (admissionOnly) continue;
        foreach (var (name, cost) in new (string, Func<(int Size, long Facts, long Reads), long>)[]
            { ("facts", sample => sample.Facts), ("reads", sample => sample.Reads) })
        {
            var label = string.Format(CultureInfo.InvariantCulture, row.Label, name);
            var perOperand = samples.Select(sample => (double)cost(sample) / sample.Size).ToArray();
            var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
                $"{sample.Size} = {(double)cost(sample) / sample.Size:F0}")));
            if (perOperand.Skip(1).Zip(perOperand).Any(pair => pair.First > pair.Second * AllowedShapeGrowth))
            {
                failures.Add($"{label} cost {measured} heartbeats per operand; the limit is {AllowedShapeGrowth} " +
                    "times the cost per operand at the size before.");
                Console.WriteLine($"FAIL {label}: {measured} heartbeats per operand");
            }
            else Console.WriteLine($"PASS {label}: {measured} heartbeats per operand");
        }
    }
    if (failures.Count > 0) throw new InvalidOperationException(string.Join("\n", failures));
}

// Fails when locating a class field on an instance, or rejecting one whose owner is outside the instance's lineage,
// costs over 1.35 times more per base than at the size before, for 2, 8 and 32 bases. The check walks the lineage
// once, so its cost per base falls toward a constant; a walk per base would grow with the bases.
void LineageCosts()
{
    const double AllowedLineageGrowth = 1.35;
    var lineageDirectory = At("artifacts/LookupScaling/Lineage");
    Directory.CreateDirectory(lineageDirectory);
    var samples = new List<(int Bases, long Rejected, long Located)>();
    foreach (var bases in new[] { 2, 8, 32 })
    {
        var output = RunLineageFixture(lineageDirectory, bases);
        var costs = LookupPatterns.Lineage.Matches(output).Cast<Match>().ToArray();
        if (costs.Length != 2) throw new InvalidOperationException("Missing lineage costs: " + output);
        long Cost(string label) => long.Parse(costs.Single(match => match.Groups[1].Value == label).Groups[2].Value,
            CultureInfo.InvariantCulture);
        samples.Add((bases, Cost("rejected"), Cost("located")));
    }
    var failures = new List<string>();
    foreach (var (name, cost) in new (string, Func<(int Bases, long Rejected, long Located), long>)[]
        { ("rejecting an unrelated owner", sample => sample.Rejected), ("locating the furthest base's field",
            sample => sample.Located) })
    {
        var perBase = samples.Select(sample => (double)cost(sample) / sample.Bases).ToArray();
        var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
            $"{sample.Bases} = {(double)cost(sample) / sample.Bases:F0}")));
        if (perBase.Skip(1).Zip(perBase).Any(pair => pair.First > pair.Second * AllowedLineageGrowth))
        {
            failures.Add($"Lineage check {name} cost {measured} heartbeats per base; the limit is " +
                $"{AllowedLineageGrowth} times the cost per base at the size before.");
            Console.WriteLine($"FAIL lineage check {name}: {measured} heartbeats per base");
        }
        else Console.WriteLine($"PASS lineage check {name}: {measured} heartbeats per base");
    }
    if (failures.Count > 0) throw new InvalidOperationException(string.Join("\n", failures));
}

// Locates a field of the furthest of `bases` base classes on a fresh instance and rejects one of an unrelated class.
string RunLineageFixture(string directory, int bases)
{
    var lineage = string.Join(", ", Enumerable.Range(0, bases).Reverse().Select(index =>
        $".object \"T\" \"T.Base{index}\""));
    var source = $$"""
        import CIL.Safety.HeapObjectFacts
        open CIL CIL.Extraction CIL.Safety Lean Elab Command
        /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
        elab "#lineage_cost " label:str " in " command:command : command => do
          let before <- IO.getNumHeartbeats
          elabCommand command
          let after <- IO.getNumHeartbeats
          logInfo m!"lineage {label.getString} {after - before} heartbeats"
        def lineageType : RuntimeType := { identity := .object "T" "T.Derived", bases := [{{lineage}}] }
        #lineage_cost "rejected" in
        theorem rejected (memory : Safety.Memory) :
            objectFieldAddress (objectMemory memory lineageType 64) (.address ⟨memory.nextIdentity, 0⟩)
              (.object "T" "T.Unrelated") 8 =
                .error (.unsupported "Field owner is not the object's class or a base of it") :=
          objectMemory_field_unrelated memory lineageType 64 8 _ (by decide)
        #lineage_cost "located" in
        theorem located (memory : Safety.Memory) :
            objectFieldAddress (objectMemory memory lineageType 64) (.address ⟨memory.nextIdentity, 0⟩)
              (.object "T" "T.Base0") 8 = .ok ⟨memory.nextIdentity, 8⟩ :=
          objectMemory_field memory lineageType (by decide) (by decide) (by decide)
        #print axioms rejected
        #print axioms located
        """ + "\n";
    var path = Path.Combine(directory, $"Lineage{bases}.lean");
    File.WriteAllText(path, source);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("The lineage fixture introduced an unproved theorem.");
    return output;
}

// Declares one shape fact per operand over size structs, or over one struct of size fields, and reads every fact.
string RunShapeFixture(string directory, string name, int size, bool spread, bool value, bool repeated,
    bool admissionOnly)
{
    var operandCount = repeated ? 1 : size;
    var structs = spread ? operandCount : 1;
    var fieldsPerStruct = spread ? 1 : size;
    var structFields = string.Join(", ", Enumerable.Repeat("{ type := .signed32 }", fieldsPerStruct));
    var raw = string.Join(",\n  ", Enumerable.Range(0, structs).Select(index =>
        $"{{ identity := \"T::S{index}\", explicit := false, packing := 0, declaredSize := 0, " +
        $"fields := [{structFields}] }}"));
    var offsets = string.Join(", ", Enumerable.Range(0, fieldsPerStruct).Select(field =>
        $"{{ offset := {4 * field}, width := 4 }}"));
    var computed = string.Join(",\n  ", Enumerable.Repeat(
        $"⟨{{ size := {4 * fieldsPerStruct}, fields := [{offsets}] }}, 4⟩", structs));
    var operands = new StringBuilder();
    var facts = new StringBuilder();
    for (var operand = 0; operand < operandCount; operand++)
    {
        var owner = spread ? operand : 0;
        operands.AppendLine(value
            ? $"def operand{operand} : TypeExpr := .aggregate \"T::S{owner}\" {owner}"
            : $"def operand{operand} : FieldRef := {{ owner := .aggregate \"T::S{owner}\" {owner}, " +
                $"index := {(spread ? 0 : operand)}, type := .primitive .int32, " +
                $"name := name!\"f{operand}\" }}");
        if (!admissionOnly) facts.Append("#resolution_cost \"fact\" in ");
        facts.AppendLine($"cil_{(value ? "value" : "field")}_shape environment " +
            $"operand{operand}");
    }
    var reads = string.Join(", ", Enumerable.Range(0, size).Select(operand =>
        $"body.{(value ? "valueShape" : "fieldShape")} operand{(repeated ? 0 : operand)}"));
    var shapes = string.Join(", ", Enumerable.Range(0, size).Select(operand =>
        value ? ".aggregate 4" : $".value {(spread ? 0 : 4 * operand)} 4 false"));
    var shapeType = value ? "ValueShape" : "FieldShape";
    var admission = "";
    if (name == "Value" && size <= 128)
    {
        var indices = Enumerable.Range(0, size);
        var sites = string.Join(", ", indices.Select(index =>
            $"RawInstruction.mk {index} 0xfe1c (.type operand{index})"));
        var code = string.Join(", ", indices.Select(index => $".sizeof operand{index}"));
        var proof = Nethermind.LeanCIL.ObjectOperandProof.Render("emitted",
            indices.Select(index => (0xfe1c, $"operand{index}")));
        admission = $$"""
            def raw : RawMethod := {
              token := 1, owner := "Scaling", hasThis := false, explicitThis := false, callingConvention := 0,
              attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
              initLocals := false, maxStack := {{size}}, genericParameters := [], code := [{{sites}}] }
            def emitted : Method := { body with code := [{{code}}] }
            #resolution_cost "objects" in
            theorem objects_checked : ObjectOperandsValid raw (List.replicate {{size}} true) emitted :=
              {{proof}}
            #print axioms objects_checked
            """;
    }
    var shapeReads = admissionOnly ? "" : $$"""
        #resolution_cost "simplifier" in
        theorem body_reads : ([{{reads}}] : List {{shapeType}}) = [{{shapes}}] := by simp only [cil_code]
        #print axioms body_reads
        """;
    var source = $$"""
        import CIL.Safety.ResolutionFacts
        import CIL.Extraction.ObjectOperands
        open CIL CIL.Extraction Lean Elab Command
        set_option maxRecDepth 8192
        /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
        elab "#resolution_cost " label:str " in " command:command : command => do
          let before <- IO.getNumHeartbeats
          elabCommand command
          let after <- IO.getNumHeartbeats
          logInfo m!"resolution {label.getString} {after - before} heartbeats"
        def rawLayouts : List RawLayout := [
          {{raw}}]
        def computedLayouts : Array ComputedLayout := #[
          {{computed}}]
        @[cil_code] def environment : LayoutEnvironment :=
          { rawLayouts := rawLayouts, layouts := computedLayouts }
        def body : Method :=
          { code := List.replicate 512 .nop, locals := [], returnsValue := false, environment }
        {{operands}}
        {{facts}}
        {{admission}}
        {{shapeReads}}
        #print axioms operand{{operandCount - 1}}_shape
        """ + "\n";
    var path = Path.Combine(directory, $"{name}{size}.lean");
    File.WriteAllText(path, source);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("Shape resolution introduced an unproved theorem.");
    return output;
}

// Decides the managed-call check on bodies of call and nop pairs with the extractor's literal table; a per-pc table
// scan costs the square of the call sites.
void CallCheckCosts()
{
    var checkDirectory = At("artifacts/LookupScaling/CallCheck");
    Directory.CreateDirectory(checkDirectory);
    var samples = new List<(int Sites, long Cost)>();
    foreach (var sites in new[] { 64, 256, 1024 })
    {
        var pcs = Enumerable.Range(0, sites).Select(site => 2 * site).ToArray();
        var raw = string.Join(", ", pcs.Select(_ => "site, ⟨0, 0, .none⟩"));
        var code = string.Join(", ", pcs.Select(_ => ".call callMethod, .nop"));
        var links = string.Join(", ", pcs.Select(pc => $"({pc}, .direct 0)"));
        var statement =
            $"ManagedCallsValid [⟨[], callee, ⟨⟨name!\"Tests\", ⟨1, 0, 0, 0⟩, name!\"\", none⟩⟩⟩] [] (fun _ => false) raw (List.replicate {2 * sites} true) body";
        var source = $$"""
            import CIL.Extraction.Generics
            open CIL CIL.Extraction Lean Elab Command
            set_option maxRecDepth 65536
            set_option maxHeartbeats 0
            /-- Elaboration and kernel checking of one command, excluding fixture construction. -/
            elab "#call_check_cost " command:command : command => do
              let before <- IO.getNumHeartbeats
              elabCommand command
              let after <- IO.getNumHeartbeats
              logInfo m!"call check {after - before} heartbeats"
            def callee : RawMethod := {
              token := 1, owner := "Tests, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null::Scaling", hasThis := false, explicitThis := false,
              callingConvention := 0, attributes := 0, implementation := 0,
              returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
              genericParameters := [], code := [] }
            def callMethod : MethodRef := {
              owner := .atom "Tests, Version=1.0.0.0, Culture=neutral, PublicKeyToken=null" "Scaling" .classType,
              name := name!"", hasThis := false, genericArity := 0, returnType := .void, parameters := [] }
            def site : RawInstruction := ⟨0, 40, .call {
              method := callMethod, declared := { convention := 0 }, target := .managed 1,
              typeArguments := [], parameterCount := 0,
              returnsValue := false }⟩
            def raw : RawMethod := { callee with code := [{{raw}}] }
            def body : Method := { locals := [], returnsValue := false, code := [{{code}}], links := [{{links}}] }
            #call_check_cost
            theorem checked : {{statement}} := by decide +kernel
            #print axioms checked
            """ + "\n";
        var path = Path.Combine(checkDirectory, $"Sites{sites}.lean");
        File.WriteAllText(path, source);
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        if (output.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidOperationException("The call check cost fixture introduced an unproved theorem.");
        var cost = LookupPatterns.CallCheck.Match(output);
        if (!cost.Success) throw new InvalidOperationException("Missing the call check cost: " + output);
        samples.Add((sites, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture)));
    }
    var perSite = samples.Select(sample => (double)sample.Cost / sample.Sites).ToArray();
    var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
        $"{sample.Sites} = {(double)sample.Cost / sample.Sites:F0}")));
    if (perSite.Skip(1).Zip(perSite).Any(pair => pair.First > pair.Second * AllowedCallGrowth))
        throw new InvalidOperationException(
            $"The managed-call check costs {measured} heartbeats per call site; the limit is {AllowedCallGrowth} " +
            "times the cost per call site at the size before.");
    Console.WriteLine($"PASS the managed-call check costs {measured} heartbeats per call site");
}

// Isolating one validator must also remove generated facts whose signature premises were removed.
void CheckNarrowedResolution()
{
    const string Source = """
        import CIL.Safety.ResolutionFacts
        namespace Extracted
        open CIL CIL.Extraction
        def method0 : Method :=
          { code := [], locals := [], returnsValue := true,
            declared := { returnType := .primitive .byte } }
        theorem method0_returnsValue : method0.returnsValue = true := rfl
        theorem method0_declared :
          method0.declared = { returnType := .primitive .byte } := rfl
        cil_resolution_facts method0
        theorem selected : True := True.intro
        #print axioms method0_returnsValue
        #print axioms method0_declared
        #print axioms method0_returnNarrow
        #print axioms selected
        end Extracted
        """;
    var directory = At("artifacts/LookupScaling/ReturnResolution");
    Directory.CreateDirectory(directory);
    var path = Path.Combine(directory, "Narrowed.lean");
    File.WriteAllText(path, NarrowEvidence(Source + "\n", "selected") + "\n#print axioms Extracted.selected\n");
    Run(["lake", "env", "lean", path], cwd: FixturePackage());
    Console.WriteLine("PASS isolated evidence retains its selected obligation with generated return facts");
}

// A command that logs the heartbeats `decide +kernel` adds to the same statement closed with `sorry`.
const string KernelCostCommand = """
    /-- Logs what `decide +kernel` costs beyond elaborating the statement. -/
    elab "#kernel_cost " label:str statement:term : command => do
      let before <- IO.getNumHeartbeats
      elabCommand (<- `(example : $statement := sorry))
      let middle <- IO.getNumHeartbeats
      elabCommand (<- `(example : $statement := by decide +kernel))
      let after <- IO.getNumHeartbeats
      let cost : Int := ((after - middle : Nat) : Int) - ((middle - before : Nat) : Int)
      logInfo m!"{label.getString} {cost} heartbeats"
    """;

// Exception decisions compare constructors, so display-name length cannot increase their cost.
void ExceptionDecisionCosts()
{
    var directory = At("artifacts/LookupScaling/ExceptionTypes");
    Directory.CreateDirectory(directory);
    string[] members = ["format", "applicationException"];
    var statements = members.SelectMany(member =>
    {
        string fault = $"ExecutionFault.thrown .{member}";
        return new[]
        {
            $"#kernel_cost \"thrownEqual {member}\" {fault} = {fault}",
            $"#kernel_cost \"thrownUnequal {member}\" Not ({fault} = ExecutionFault.thrown .overflow)",
            $"#kernel_cost \"clrUnequal {member}\" Not (({fault}).clrException = some .overflow)",
            $"#kernel_cost \"raisesEqual {member}\" (some .{member} : Option ExceptionType) = some .{member}"
        };
    });
    var path = Path.Combine(directory, "Equality.lean");
    File.WriteAllText(path, """
        import CIL.Safety.RuntimeExceptions
        open CIL CIL.Safety Lean Elab Command

        """ + KernelCostCommand + "\n" + string.Join("\n", statements) + "\n");
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.ExceptionDecision.Matches(output).ToDictionary(
        match => match.Groups[1].Value,
        match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
    if (costs.Count != 8) throw new InvalidOperationException("Missing exception decision costs:\n" + output);
    foreach (var decision in new[] { "thrownEqual", "thrownUnequal", "clrUnequal", "raisesEqual" })
    {
        long shortName = costs[decision + " format"];
        long longName = costs[decision + " applicationException"];
        var measured = $"{shortName} heartbeats at format and {longName} at applicationException";
        if (Math.Min(shortName, longName) < KernelDecisionFloor ||
            Math.Max(shortName, longName) > TypeDecisionLimit || longName > shortName * AllowedNameGrowth)
            throw new InvalidOperationException($"Exception decision {decision} exceeds its cost bound: {measured}");
        Console.WriteLine($"PASS deciding {decision} costs {measured}");
    }
}

// Lean definitions of a value-only body of `instructions` instructions: `raw`, its raw instructions, and `code`, the
// instructions the translator emits for them. Raw instructions carry distinct offsets, so the kernel decodes each one
// instead of reusing a cached decode.
static string ValueBody(int instructions)
{
    const int SegmentLength = 10;
    return $$"""
        /-- The raw instructions of one segment: short and long constants, locals, an argument,
            arithmetic, a checked conversion, a branch, a four-target switch and a return. -/
        def segment (index : Nat) : List RawInstruction :=
          let start := {{SegmentLength}} * index
          [⟨start, 31, .integer (index % 100)⟩, ⟨start + 1, 32, .integer (70000 + index)⟩,
            ⟨start + 2, 17, .local (index % 4)⟩, ⟨start + 3, 19, .local (index % 4)⟩,
            ⟨start + 4, 14, .argument (index % 4)⟩, ⟨start + 5, 88, .none⟩, ⟨start + 6, 130, .none⟩,
            ⟨start + 7, 58, .target index⟩,
            ⟨start + 8, 69, .targets [index, index + 1, index + 2, index + 3]⟩, ⟨start + 9, 42, .none⟩]
        /-- The instructions the translator emits for one segment. -/
        def codeSegment (index : Nat) : List Instruction :=
          [.ldc_i4 (BitVec.ofNat 32 (index % 100)), .ldc_i4 (BitVec.ofNat 32 (70000 + index)),
            .ldloc (index % 4), .stloc (index % 4), .ldarg (index % 4), .add, .conv_ovf_un .i1,
            .brtrue index, .switch [index, index + 1, index + 2, index + 3], .ret]
        /-- A body of {{instructions}} raw instructions. -/
        def raw : List RawInstruction := (List.range {{instructions / SegmentLength}}).flatMap segment
        /-- The {{instructions}} emitted instructions of the body. -/
        def code : List Instruction := (List.range {{instructions / SegmentLength}}).flatMap codeSegment
        """;
}

// The heartbeats `decide +kernel` adds to deciding that every instruction of a body of 500, 2000 and 8000
// instructions is the one its raw value opcode decodes to. Decoding costs the same at every instruction and a
// `switch` its targets, so four times the instructions may cost at most `AllowedLocalGrowth` more per instruction.
void DecodeCosts()
{
    var decodeDirectory = At("artifacts/LookupScaling/ValueDecoding");
    Directory.CreateDirectory(decodeDirectory);
    var samples = new List<(int Instructions, long Cost, long Milliseconds)>();
    foreach (var instructions in new[] { 500, 2000, 8000 })
    {
        var path = Path.Combine(decodeDirectory, $"Instructions{instructions}.lean");
        File.WriteAllText(path, $$"""
            import CIL.Extraction.ValueDecoding
            set_option maxRecDepth 100000
            set_option maxHeartbeats 0
            open CIL CIL.Extraction Lean Elab Command
            {{KernelCostCommand}}
            namespace ValueDecodingCost
            {{ValueBody(instructions)}}
            #kernel_cost "decode {{instructions}}"
              (raw.zip code).all (fun pair => valueEncodingMatches none pair.1 pair.2) = true
            end ValueDecodingCost
            """ + "\n");
        var package = FixturePackage();
        var clock = System.Diagnostics.Stopwatch.StartNew();
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: package);
        var cost = LookupPatterns.ValueDecoding.Match(output);
        if (!cost.Success) throw new InvalidOperationException($"Missing the value decoding cost:\n{output}");
        samples.Add((instructions, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture),
            clock.ElapsedMilliseconds));
    }
    var perInstruction = samples.Select(sample => (double)sample.Cost / sample.Instructions).ToArray();
    var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
        $"{(double)sample.Cost / sample.Instructions:F1} at {sample.Instructions} ({sample.Milliseconds} ms)")));
    if (samples.Any(sample => sample.Cost < KernelDecisionFloor) ||
        perInstruction.Skip(1).Zip(perInstruction).Any(pair => pair.First > pair.Second * AllowedLocalGrowth))
        throw new InvalidOperationException(
            $"Decoding raw value opcodes costs {measured} heartbeats per instruction; the limit is " +
            $"{AllowedLocalGrowth} times the cost per instruction at the size before.");
    Console.WriteLine($"PASS decoding raw value opcodes costs {measured} heartbeats per instruction");
}

// Body evidence checks prefix structure. Raw construction also decides branch entry.
void PrefixEntryCosts()
{
    const int SegmentLength = 4;
    const double DestinationOrderTolerance = 0.02;
    var directory = At("artifacts/LookupScaling/PrefixEntry");
    Directory.CreateDirectory(directory);
    var samples = new Dictionary<string, List<(int Instructions, long Cost)>>
        { ["body"] = [], ["ascending"] = [], ["descending"] = [], ["shuffled"] = [] };
    foreach (var instructions in new[] { 500, 2000, 8000 })
    {
        var path = Path.Combine(directory, $"Instructions{instructions}.lean");
        var ascending = Enumerable.Range(0, instructions / SegmentLength).Select(index => SegmentLength * index)
            .ToArray();
        var shuffled = ascending.ToArray();
        new Random(1701).Shuffle(shuffled);
        File.WriteAllText(path, $$"""
            import CIL.Extraction.Scalars
            set_option maxRecDepth 100000
            set_option maxHeartbeats 0
            open CIL CIL.Extraction Lean Elab Command
            {{KernelCostCommand}}
            namespace PrefixEntryCost
            /-- The element type of every address. -/
            def intType : TypeExpr := .primitive .int32
            /-- Each segment branches to the prefix at the given destination. -/
            def segment (destination index : Nat) : List RawInstruction :=
              let start := {{SegmentLength}} * index
              [⟨start, 65054, .none⟩, ⟨start + 1, 143, .type intType⟩, ⟨start + 2, 38, .none⟩,
                ⟨start + 3, 43, .target destination⟩]
            /-- The same {{instructions}} instructions with the given branch operands. -/
            def raw (targets : List Nat) :=
              targets.zipIdx.flatMap fun (target, pc) => segment target pc
            /-- The branch targets in increasing order. -/
            def ascending := raw [{{string.Join(",", ascending)}}]
            /-- The same branch targets in decreasing order. -/
            def descending := raw [{{string.Join(",", ascending.Reverse())}}]
            /-- A fixed permutation of the same branch targets. -/
            def shuffled := raw [{{string.Join(",", shuffled)}}]
            #kernel_cost "prefix body {{instructions}}"
              prefixSequenceValid .void ascending = true
            #kernel_cost "prefix ascending {{instructions}}" rawPrefixesValid .void ascending = true
            #kernel_cost "prefix descending {{instructions}}" rawPrefixesValid .void descending = true
            #kernel_cost "prefix shuffled {{instructions}}" rawPrefixesValid .void shuffled = true
            end PrefixEntryCost

            """);
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var costs = LookupPatterns.PrefixEntry.Matches(output);
        foreach (var (kind, rows) in samples)
        {
            var cost = costs.Single(match => match.Groups[1].Value == kind);
            rows.Add((instructions, long.Parse(cost.Groups[2].Value, CultureInfo.InvariantCulture)));
        }
    }
    var failures = new List<string>();
    foreach (var (kind, rows) in samples)
    {
        var costs = rows.Select(row => (double)row.Cost / row.Instructions).ToArray();
        var measured = string.Join("; ", rows.Select(row => string.Create(CultureInfo.InvariantCulture,
            $"{(double)row.Cost / row.Instructions:F1} at {row.Instructions}")));
        if (rows.Any(row => row.Cost < KernelDecisionFloor) ||
            costs.Skip(1).Zip(costs).Any(pair => pair.First > pair.Second * AllowedLocalGrowth))
            failures.Add($"Prefix {kind} exceeds the growth limit at {measured}");
        Console.WriteLine($"Prefix {kind} costs {measured} heartbeats per instruction");
        if (kind is "descending" or "shuffled" && rows.Zip(samples["ascending"]).Any(pair =>
            Math.Abs((double)pair.First.Cost / pair.Second.Cost - 1) > DestinationOrderTolerance))
            failures.Add($"Prefix {kind} differs from ascending by more than 2% at {measured}");
    }
    if (failures.Count != 0) throw new InvalidOperationException(string.Join(Environment.NewLine, failures));
    Console.WriteLine("PASS prefix validation growth and destination order");
}

// The heartbeats `decide +kernel` adds to deciding that `Method.ofRaw?` of a value-only body of 500, 2000 and 8000
// instructions with four parameters and four locals gives the emitted code, the initialized locals and no homes or
// links. Each instruction is decoded and instantiated once, so four times the instructions may cost at most
// `AllowedLocalGrowth` more per instruction.
void MethodDecodeCosts()
{
    var decodeDirectory = At("artifacts/LookupScaling/DecodedMethod");
    Directory.CreateDirectory(decodeDirectory);
    var samples = new List<(int Instructions, long Cost)>();
    foreach (var instructions in new[] { 500, 2000, 8000 })
    {
        var path = Path.Combine(decodeDirectory, $"Instructions{instructions}.lean");
        File.WriteAllText(path, $$"""
            import CIL.Extraction.DecodedMethod
            set_option maxRecDepth 100000
            set_option maxHeartbeats 0
            open CIL CIL.Extraction Lean Elab Command
            {{KernelCostCommand}}
            namespace DecodedMethodCost
            {{ValueBody(instructions)}}
            /-- The type of every parameter and local. -/
            def uint32 : TypeExpr := .primitive .uint32
            /-- A static method with four parameters, four zero-initialized locals and {{instructions}} raw
                instructions. -/
            def source : RawMethod :=
              { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
                attributes := 0, implementation := 0, returnType := .void, parameters := List.replicate 4 uint32,
                locals := List.replicate 4 uint32, initLocals := true,
                maxStack := 8, genericParameters := [], code := raw }
            #kernel_cost "decoded method {{instructions}}"
              (Method.ofRaw? .scalar {} [] (List.replicate {{instructions}} true) source []).any (fun method =>
                method.code.length == {{instructions}} &&
                  (method.code.zip code).all (fun pair => pair.1.sameValue pair.2) &&
                  method.locals == List.replicate 4 (.i32 0) && method.parameterHomes.isEmpty &&
                  method.links.isEmpty) = true
            end DecodedMethodCost
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.DecodedMethod.Match(output);
        if (!cost.Success) throw new InvalidOperationException($"Missing the decoded method cost:\n{output}");
        samples.Add((instructions, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture)));
    }
    var perInstruction = samples.Select(sample => (double)sample.Cost / sample.Instructions).ToArray();
    var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
        $"{(double)sample.Cost / sample.Instructions:F1} at {sample.Instructions}")));
    if (samples.Any(sample => sample.Cost < KernelDecisionFloor) ||
        perInstruction.Skip(1).Zip(perInstruction).Any(pair => pair.First > pair.Second * AllowedLocalGrowth))
        throw new InvalidOperationException(
            $"Decoding a method costs {measured} heartbeats per instruction; the limit is " +
            $"{AllowedLocalGrowth} times the cost per instruction at the size before.");
    Console.WriteLine($"PASS decoding a method costs {measured} heartbeats per instruction");
}

// The heartbeats `cil_decoded_method` spends defining a value-only method of 500, 2000 and 8000 instructions with
// four locals from its raw definition, its kernel checks included. Its literal and its checks are linear in the
// instructions, so four times the instructions may cost at most `AllowedLocalGrowth` more per instruction.
void DecodedDefinitionCosts()
{
    var definitionDirectory = At("artifacts/LookupScaling/DecodedDefinition");
    Directory.CreateDirectory(definitionDirectory);
    const int SegmentLength = 10;
    var samples = new List<(int Instructions, long Cost)>();
    foreach (var instructions in new[] { 500, 2000, 8000 })
    {
        var path = Path.Combine(definitionDirectory, $"Instructions{instructions}.lean");
        File.WriteAllText(path, $$"""
            import CIL.Extraction.DecodedDefinition
            set_option maxRecDepth 100000
            set_option maxHeartbeats 0
            open CIL CIL.Extraction Lean Elab Command
            /-- Logs the heartbeats elaborating `body` costs, its kernel checks included. -/
            elab "#command_cost " label:str body:command : command => do
              let before <- IO.getNumHeartbeats
              elabCommand body
              let after <- IO.getNumHeartbeats
              logInfo m!"{label.getString} {after - before} heartbeats"
            namespace DecodedDefinitionCost
            /-- The raw instructions of one segment: short and long constants, locals, arithmetic, a checked
                conversion, a branch, a four-target switch and a return. -/
            def segment (index : Nat) : List RawInstruction :=
              let start := {{SegmentLength}} * index
              [⟨start, 31, .integer (index % 100)⟩, ⟨start + 1, 32, .integer (70000 + index)⟩,
                ⟨start + 2, 17, .local (index % 4)⟩, ⟨start + 3, 19, .local (index % 4)⟩,
                ⟨start + 4, 6, .none⟩, ⟨start + 5, 88, .none⟩, ⟨start + 6, 130, .none⟩,
                ⟨start + 7, 58, .target index⟩,
                ⟨start + 8, 69, .targets [index, index + 1, index + 2, index + 3]⟩, ⟨start + 9, 42, .none⟩]
            /-- The profile the method is decoded under, named as an extraction names it. -/
            def profile : FeatureProfile := .scalar
            /-- The layouts the method is decoded under, named as an extraction names them. -/
            def environment : LayoutEnvironment := {}
            /-- A static method with four zero-initialized `uint32` locals and {{instructions}} raw instructions. -/
            def source : RawMethod :=
              { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
                attributes := 0, implementation := 0, returnType := .void, parameters := [],
                locals := List.replicate 4 (.primitive .uint32), initLocals := true,
                maxStack := 8, genericParameters := [],
                code := (List.range {{instructions / SegmentLength}}).flatMap segment }
            #command_cost "decoded definition {{instructions}}"
              cil_decoded_method method :=
                Method.ofRaw? profile environment [] (List.replicate {{instructions}} true) source []
            end DecodedDefinitionCost
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.DecodedDefinition.Match(output);
        if (!cost.Success) throw new InvalidOperationException($"Missing the decoded definition cost:\n{output}");
        samples.Add((instructions, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture)));
    }
    var perInstruction = samples.Select(sample => (double)sample.Cost / sample.Instructions).ToArray();
    var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
        $"{(double)sample.Cost / sample.Instructions:F1} at {sample.Instructions}")));
    if (samples.Any(sample => sample.Cost < KernelDecisionFloor) ||
        perInstruction.Skip(1).Zip(perInstruction).Any(pair => pair.First > pair.Second * AllowedLocalGrowth))
        throw new InvalidOperationException(
            $"Defining a decoded method costs {measured} heartbeats per instruction; the limit is " +
            $"{AllowedLocalGrowth} times the cost per instruction at the size before.");
    Console.WriteLine($"PASS defining a decoded method costs {measured} heartbeats per instruction");
}

// The heartbeats `decodedProgram?_eq_some` costs to state and prove that 8, 32 and 128 records decode to their
// methods, given one decoding fact per record. Each record adds one constructor, so four times the records may cost
// at most `AllowedLocalGrowth` more per record.
void DecodedProgramCosts()
{
    var programDirectory = At("artifacts/LookupScaling/DecodedProgram");
    Directory.CreateDirectory(programDirectory);
    var samples = new List<(int Records, long Cost)>();
    foreach (var records in new[] { 8, 32, 128 })
    {
        var indexes = Enumerable.Range(0, records).ToArray();
        var items = string.Join(" ", indexes.Select(index => $"item{index}"));
        var methods = string.Join(" ", indexes.Select(index => $"method{index}"));
        var facts = string.Join("\n", indexes.Select(index =>
            $"    (decodes{index} : Decodes profile environment item{index} method{index})"));
        var bodies = string.Concat(indexes.Select(index => $"(.cons decodes{index} ")) + ".nil" +
            new string(')', records);
        var path = Path.Combine(programDirectory, $"Records{records}.lean");
        File.WriteAllText(path, $$"""
            import CIL.Safety.DecodedSummary
            set_option maxRecDepth 100000
            set_option maxHeartbeats 0
            open CIL CIL.Extraction CIL.Safety Lean Elab Command
            /-- Logs the heartbeats elaborating `body` costs, its kernel checks included. -/
            elab "#command_cost " label:str body:command : command => do
              let before <- IO.getNumHeartbeats
              elabCommand body
              let after <- IO.getNumHeartbeats
              logInfo m!"{label.getString} {after - before} heartbeats"
            namespace DecodedProgramCost
            variable (profile : FeatureProfile) (environment : LayoutEnvironment)
            /-- The pinned body bytes of `item` decode to `method`. -/
            abbrev Decodes (item : MethodEvidence) (method : CIL.Method) : Prop :=
              Method.ofBody? profile environment item.links item.reachable item.body item.original
                item.arguments = some method
            #command_cost "decoded program {{records}}"
              theorem decoded ({{items}} : MethodEvidence) ({{methods}} : CIL.Method)
            {{facts}}
                  (masks : programBindingsValid [{{items.Replace(" ", ", ")}}]
                    [{{methods.Replace(" ", ", ")}}] = true) :
                  decodedProgram? profile environment [{{items.Replace(" ", ", ")}}] =
                    some [{{methods.Replace(" ", ", ")}}] :=
                decodedProgram?_eq_some masks {{bodies}}
            end DecodedProgramCost
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.DecodedProgram.Match(output);
        if (!cost.Success) throw new InvalidOperationException($"Missing the decoded program cost:\n{output}");
        samples.Add((records, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture)));
    }
    var perRecord = samples.Select(sample => (double)sample.Cost / sample.Records).ToArray();
    var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
        $"{(double)sample.Cost / sample.Records:F0} at {sample.Records}")));
    if (samples.Any(sample => sample.Cost < KernelDecisionFloor) ||
        perRecord.Skip(1).Zip(perRecord).Any(pair => pair.First > pair.Second * AllowedLocalGrowth))
        throw new InvalidOperationException(
            $"Proving a decoded program costs {measured} heartbeats per record; the limit is " +
            $"{AllowedLocalGrowth} times the cost per record at the size before.");
    Console.WriteLine($"PASS proving a decoded program costs {measured} heartbeats per record");
}

// A closure search reads each of its n methods from a program index stated once and gives each of the e callees their
// link tables enter one packed table entry, so it costs O(n * log P + e) kernel steps in a program of P methods. Each
// shape grows one term: a chain whose closure is the whole program grows n * log P, up to the corpus scale of several
// hundred methods, one method calling seven others grows e, and a closure of four methods at the start of a longer
// program grows log P alone. Reading each method from the list instead costs n * P, which the tail pays in P and which
// the row also measures; folding over the search state costs time quadratic in e. Stating the index costs O(P) once.
void ClosureCosts()
{
    var closureDirectory = At("artifacts/LookupScaling/Closures");
    Directory.CreateDirectory(closureDirectory);
    // Four times the units may cost at most this much more per unit.
    const double AllowedClosureGrowth = 1.15;
    int[][] Chain(int size) => [.. Enumerable.Range(0, size).Select(int[] (index) =>
        index + 1 < size ? [index + 1] : [])];
    ClosureShape[] shapes =
    [
        new("chain", [8, 32, 128], Chain, size => size, size => size - 1),
        new("longchain", [128, 256, 512], Chain, size => size, size => size - 1),
        new("fan", [32, 128, 512], size => [[.. Enumerable.Range(0, size).Select(index => 1 + index % 7)],
            .. Enumerable.Repeat(Array.Empty<int>(), 7)], _ => 8, size => size),
        new("tail", [128, 512, 2048], size => [[1], [2], [3], .. Enumerable.Repeat(Array.Empty<int>(), size - 3)],
            _ => 4, _ => 3)
    ];
    // The list form of the long chain costs tens of millions of heartbeats at 512, so only the others measure it.
    bool ListMeasured(ClosureShape shape) => shape.Name != "longchain";
    // A program two shapes share at one size is stated and measured once, by the first shape that lists it.
    ClosureShape Measuring(ClosureShape shape, int size) =>
        shapes.First(other => other.Program == shape.Program && other.Sizes.Contains(size));
    string Statement(ClosureShape shape, int size)
    {
        if (Measuring(shape, size) != shape) return "";
        var program = shape.Program(size);
        var name = $"{shape.Name}{size}";
        var expected = $"some [{string.Join(", ", Enumerable.Range(0, shape.Methods(size)))}]";
        var list = ListMeasured(shape)
            ? $"#kernel_cost \"list closure {shape.Name} {size}\" (({name}.closure 0).map Prod.snd = {expected})\n"
            : "";
        // The tail programs also state their index as an extraction does, between two heartbeat marks.
        var start = shape.Name == "tail" ? $"#heartbeat_mark \"index {size} start\"" : "";
        var stated = shape.Name != "tail" ? "" : $$"""
            /-- The length of the {{name}} program. -/
            def {{name}}Length : Nat := {{program.Length}}
            theorem {{name}}Length_eq : {{name}}Length = {{name}}.length := by cil_kernel_rfl
            theorem {{name}}Index_eq : {{name}}Index = FlowIndex.ofList {{name}} := by cil_kernel_rfl
            theorem {{name}}Index_get? (index : Nat) : {{name}}Index.get? index = {{name}}[index]? := by
              rw [{{name}}Index_eq]; exact FlowIndex.get?_ofList {{name}} index
            #heartbeat_mark "index {{size}} end"
            #print axioms [{{name}}Length_eq, {{name}}Index_eq, {{name}}Index_get?]

            """;
        return $$"""
            /-- The {{shape.Name}} program of size {{size}}. -/
            def {{name}} : Program :=
              [{{string.Join(", ", program.Select(callees => $"stub [{string.Join(", ", callees)}]"))}}]
            {{start}}
            /-- The index of the {{name}} program. -/
            def {{name}}Index : FlowIndex Method := program_index% {{name}}
            {{stated}}#kernel_cost "closure {{shape.Name}} {{size}}"
              ((closureWith {{name}}Index.get? {{program.Length}} 0).map Prod.snd = {{expected}})
            {{list}}
            """;
    }
    var path = Path.Combine(closureDirectory, "Closures.lean");
    File.WriteAllText(path, $$"""
        import CIL.Safety.ProgramClosure
        import CIL.Extraction.KernelEquation
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        open CIL CIL.Extraction Lean Elab Command
        {{KernelCostCommand}}
        /-- Build a literal list outside the measured elaboration of its index. -/
        elab "sample_cells% " size:num : term => do
          let cells := List.replicate size.getNat (mkNatLit 0)
          Meta.mkListLit (mkConst ``Nat) cells
        /-- The smaller input to the native index construction check. -/
        def smallCells : List Nat := sample_cells% 2048
        /-- Sixteen times the smaller input. -/
        def largeCells : List Nat := sample_cells% 32768
        -- Heartbeats omit native list traversal when the reads allocate nothing.
        run_cmd liftTermElabM do
          let measure (input : Term) : Term.TermElabM Nat := do
            let mut samples := #[]
            for _ in [:3] do
              let before <- IO.monoNanosNow
              let tree <- Term.elabTerm (<- `(program_index% $input)) none
              let after <- IO.monoNanosNow
              unless tree.isAppOf ``FlowIndex.branch do throwError "Expected a literal branch"
              samples := samples.push (after - before)
            return samples.foldl min samples[0]!
          let small <- measure (<- `(smallCells))
          let large <- measure (<- `(largeCells))
          logInfo m!"Index construction at 2048 / 32768 cells: {small} / {large} ns"
          -- Sixteen times as many cells allow four times the linear growth for timing variation.
          unless 0 < small && large <= 64 * small do
            throwError "Index construction grows faster than the traversal bound"
        /-- Logs the heartbeats spent so far, so two marks give the cost of the commands between them. -/
        elab "#heartbeat_mark " label:str : command => do
          let count <- IO.getNumHeartbeats
          logInfo m!"mark {label.getString} {count}"
        /-- A method whose link table enters `callees` in order, one call pc each. -/
        def stub (callees : List Nat) : Method :=
          { code := [], locals := [], returnsValue := false,
            links := callees.zipIdx.map fun (callee, pc) => (pc, .direct callee) }
        {{string.Join("\n", shapes.SelectMany(shape => shape.Sizes.Select(size => Statement(shape, size))))}}

        """);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException($"A closure certificate depends on sorryAx in {path}");
    Console.WriteLine(output.Split('\n').Single(line => line.StartsWith("Index construction at",
        StringComparison.Ordinal)).TrimEnd());
    var costs = LookupPatterns.ClosureCost.Matches(output).ToDictionary(
        match => (match.Groups[1].Value.Length > 0, match.Groups[2].Value,
            int.Parse(match.Groups[3].Value, CultureInfo.InvariantCulture)),
        match => long.Parse(match.Groups[4].Value, CultureInfo.InvariantCulture));
    var marks = LookupPatterns.HeartbeatMark.Matches(output).ToDictionary(
        match => (int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture), match.Groups[2].Value),
        match => long.Parse(match.Groups[3].Value, CultureInfo.InvariantCulture));
    var tail = shapes.Single(shape => shape.Name == "tail");
    var measuredCosts = shapes.Sum(shape => shape.Sizes.Count(size => Measuring(shape, size) == shape) *
        (ListMeasured(shape) ? 2 : 1));
    if (costs.Count != measuredCosts ||
        costs.Values.Min() < KernelDecisionFloor || marks.Count != 2 * tail.Sizes.Length)
        throw new InvalidOperationException($"Missing closure costs:\n{output}");
    long Cost(bool list, ClosureShape shape, int size) => costs[(list, Measuring(shape, size).Name, size)];
    string Measured(ClosureShape shape, bool list) => string.Join(", ", shape.Sizes.Select(size =>
        string.Create(CultureInfo.InvariantCulture, $"{Cost(list, shape, size)} at {size}")));
    foreach (var shape in shapes)
    {
        var units = shape.Sizes.Select(size => shape.Methods(size) *
            Math.Ceiling(Math.Log2(shape.Program(size).Length)) + shape.Edges(size)).ToArray();
        if (ClosureGrowth(units, [.. units.Select(unit => unit * unit)]) <= AllowedClosureGrowth)
            throw new InvalidOperationException($"The {shape.Name} bound accepts a cost quadratic in n * log P + e");
        // A whole-program closure of a growing program that read each method from the list would cost n * P, which
        // the bound must refuse.
        var listReads = shape.Sizes.Select(size =>
            (double)shape.Methods(size) * shape.Program(size).Length + shape.Edges(size)).ToArray();
        if (shape.Program(shape.Sizes[0]).Length < shape.Program(shape.Sizes[^1]).Length &&
            shape.Sizes.All(size => shape.Methods(size) == shape.Program(size).Length) &&
            ClosureGrowth(units, listReads) <= AllowedClosureGrowth)
            throw new InvalidOperationException($"The {shape.Name} bound accepts list reads of its methods");
        void CheckGrowth(bool list, double[] work, string unit)
        {
            var samples = shape.Sizes.Select(size => (double)Cost(list, shape, size)).ToArray();
            var growth = ClosureGrowth(work, samples);
            var route = list ? "list" : "index";
            var measured = string.Create(CultureInfo.InvariantCulture, $$"""
                The {{shape.Name}} closure through the {{route}} costs {{Measured(shape, list)}} heartbeats.
                Each added unit of {{unit}} costs {{growth:F2}} times as much between the last two sizes.
                """);
            if (!double.IsFinite(growth) || growth > AllowedClosureGrowth)
                throw new InvalidOperationException($"{measured} The limit is {AllowedClosureGrowth}.");
            Console.WriteLine($"PASS {measured}");
        }
        CheckGrowth(false, units, "n * log P + e");
        if (ListMeasured(shape)) CheckGrowth(true, listReads, "n * P + e");
    }
    // A closure of a few methods must cost less through the index than through the list at every program size.
    foreach (var size in tail.Sizes)
        if (costs[(false, "tail", size)] >= costs[(true, "tail", size)])
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $$"""
                The tail closure of {{size}} costs {{costs[(false, "tail", size)]}} heartbeats through the index.
                It must cost less than the list lookup's {{costs[(true, "tail", size)]}} heartbeats.
                """));
    // Stating the index, its length and its lookup theorem costs time linear in P.
    var programs = tail.Sizes.Select(size => (double)size).ToArray();
    var stating = tail.Sizes.Select(size => (double)(marks[(size, "end")] - marks[(size, "start")])).ToArray();
    var statingGrowth = ClosureGrowth(programs, stating);
    var statingMeasured = string.Join(", ", tail.Sizes.Select(size => string.Create(CultureInfo.InvariantCulture,
        $"{marks[(size, "end")] - marks[(size, "start")]} at {size}")));
    if (statingGrowth > AllowedClosureGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $$"""
            Stating the program index costs {{statingMeasured}} heartbeats.
            Its cost per added method grows {{statingGrowth:F2}} times, more than {{AllowedClosureGrowth}}.
            """));
    Console.WriteLine(string.Create(CultureInfo.InvariantCulture,
        $$"""
        PASS stating the program index costs {{statingMeasured}} heartbeats.
        Each added method costs {{statingGrowth:F2}} times as much between the last two sizes.
        """));
}

// Each caller executes a direct call and returns the result. Its callee's position varies
// independently of its two-instruction body. The stepper uses the emitted method equations.
void RunCosts()
{
    var runDirectory = At("artifacts/LookupScaling/Runs");
    Directory.CreateDirectory(runDirectory);
    // Allow the extra tree depth when the program grows from 16 to 256 methods.
    const double AllowedRunSpread = 1.15;
    int[] sizes = [16, 64, 256];
    int[] Positions(int size) => [0, size / 2 - 1, size - 1];
    string[] routes = ["rfl list", "rfl index", "kernel list", "kernel index", "stepper"];
    string Statement(int size)
    {
        var name = $"run{size}";
        var source = new StringBuilder();
        var positions = Positions(size);
        foreach (var index in Enumerable.Range(0, size))
        {
            var body = index is >= 1 and <= 3
                ? $$"""code := [.call runTarget {}, .ret], links := [(0, .direct {{positions[index - 1]}})]"""
                : $$"""code := [.ldc_i4 {{index}}, .ret]""";
            source.AppendLine(CultureInfo.InvariantCulture, $$"""
                /-- Method {{index}} of the {{size}}-method program. -/
                def {{name}}m{{index}} : Method :=
                  { returnsValue := true, locals := [], {{body}} }
                cil_instruction_equations {{name}}m{{index}}
                """);
        }
        source.AppendLine(CultureInfo.InvariantCulture, $$"""
            /-- The {{size}}-method program. -/
            def {{name}} : Program :=
              [{{string.Join(", ", Enumerable.Range(0, size).Select(index => $"{name}m{index}"))}}]
            """);
        source.AppendLine(CultureInfo.InvariantCulture, $$"""
            /-- The index of the {{size}}-method program. -/
            def {{name}}Index : FlowIndex Method := program_index% {{name}}
            /-- The number of methods in the program. -/
            def {{name}}Length : Nat := {{size}}
            theorem {{name}}Length_eq : {{name}}Length = {{name}}.length := by cil_kernel_rfl
            theorem {{name}}Index_eq : {{name}}Index = FlowIndex.ofList {{name}} := by cil_kernel_rfl
            theorem {{name}}Index_get? (index : Nat) : {{name}}Index.get? index = {{name}}[index]? := by
              rw [{{name}}Index_eq]; exact FlowIndex.get?_ofList {{name}} index
            """);
        var equations = new StringBuilder();
        Nethermind.LeanCIL.ProgramLookupFacts.Append(equations, name, $"{name}m", size);
        var emitted = equations.ToString();
        var report = AxiomsCommand.Matches(emitted).Single();
        var members = report.Groups["members"].Value.Split(',', StringSplitOptions.TrimEntries);
        string[] expected = [$"{name}Length_eq", $"{name}Index_eq", $"{name}Index_get?",
            .. Enumerable.Range(0, size).Select(index => $"{name}_method{index}")];
        var exactGroup = members.Length == expected.Length && expected.ToHashSet(StringComparer.Ordinal)
            .SetEquals(members);
        var wrapped = report.Value.Split('\n').All(line => line.TrimEnd('\r').Length < 100);
        if (!exactGroup || !wrapped || report.Index + report.Length != emitted.Length)
            throw new InvalidOperationException($"Invalid axiom report for {name}: {report.Value}");
        source.AppendLine($"#heartbeat_mark \"index {size} equations\"");
        source.Append(emitted.AsSpan(0, report.Index));
        source.AppendLine($"#heartbeat_mark \"index {size} start\"");
        source.Append(emitted.AsSpan(report.Index));
        source.AppendLine($"#heartbeat_mark \"index {size} end\"");
        foreach (var index in Enumerable.Range(0, size))
            source.AppendLine(CultureInfo.InvariantCulture, $$"""
                example : {{name}}[{{index}}]? = some {{name}}m{{index}} := by cil_lookup [{{name}}]
                """);
        source.AppendLine($"#heartbeat_mark \"index {size} lookups\"");
        foreach (var (ordinal, position) in positions.Index())
        {
            var caller = ordinal + 1;
            var statement = $$"""
                (invoke {{name}} 5 {{caller}} [] Memory.empty).map Prod.snd =
                    .ok [.scalar (.i32 {{position}})]
                """;
            var rewrite = $"rw [invoke_eq_invokeWith {name}Index_get?]";
            string[] proofs = ["rfl", $"{rewrite}; rfl", "cil_kernel_rfl", $"{rewrite}; cil_kernel_rfl"];
            foreach (var (route, proof) in routes.Zip(proofs))
                source.AppendLine(CultureInfo.InvariantCulture, $$"""
                    #heartbeat_mark "{{size}} {{position}} {{route}} start"
                    example : {{statement}} := by {{proof}}
                    #heartbeat_mark "{{size}} {{position}} {{route}} end"
                    """);
            source.AppendLine(CultureInfo.InvariantCulture, $$"""
                #heartbeat_mark "{{size}} {{position}} stepper start"
                theorem {{name}}_invoke{{position}} (memory : Safety.Memory) :
                    invoke {{name}} 5 {{caller}} [] memory = .ok (memory, [.scalar (.i32 {{position}})]) := by
                  cil_checked_steps
                #heartbeat_mark "{{size}} {{position}} stepper end"
                #print axioms {{name}}_invoke{{position}}
                """);
        }
        source.AppendLine(CultureInfo.InvariantCulture, $$"""
            run_meta do
              let info <- getConstInfo ``{{name}}_invoke{{positions[^1]}}
              let some proof := info.value? (allowOpaque := true) | throwError "Missing call proof"
              let used := proof.getUsedConstants
              for name in [``{{name}}_method3, ``{{name}}_method{{positions[^1]}}] do
                unless used.contains name do throwError "The call proof did not use {name}"
            """);
        return source.ToString();
    }
    var path = Path.Combine(runDirectory, "Runs.lean");
    File.WriteAllText(path, $$"""
        import CIL
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        open CIL CIL.Safety CIL.Extraction Lean Elab Command
        /-- The direct call operand shared by the three callers. -/
        def runTarget : MethodRef :=
          { owner := .void, name := ⟨1⟩, hasThis := false, genericArity := 0,
            returnType := .void, parameters := [] }
        /-- Logs the heartbeats spent so far, so two marks give the cost of the commands between them. -/
        elab "#heartbeat_mark " label:str : command => do
          let count <- IO.getNumHeartbeats
          logInfo m!"mark {label.getString} {count}"
        {{string.Join("\n", sizes.Select(Statement))}}

        """);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException($"A measured call or lookup fact depends on sorryAx in {path}");
    var auditMarks = LookupPatterns.HeartbeatMark.Matches(output).ToDictionary(
        match => (int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture), match.Groups[2].Value),
        match => long.Parse(match.Groups[3].Value, CultureInfo.InvariantCulture));
    var audits = sizes.Select(size => (double)(auditMarks[(size, "end")] - auditMarks[(size, "start")])).ToArray();
    var equations = sizes.Select(size => (double)(auditMarks[(size, "start")] - auditMarks[(size, "equations")]))
        .ToArray();
    var equationGrowth = ClosureGrowth([.. sizes.Select(size => size * Math.Log2(size))], equations);
    var equationCosts = string.Join(", ", equations.Zip(sizes, (cost, size) => $"{cost} at {size}"));
    if (equations.Any(cost => cost <= 0) || !double.IsFinite(equationGrowth) || equationGrowth > AllowedRunSpread)
        throw new InvalidOperationException(
            $"Method equations cost {equationCosts} heartbeats; growth {equationGrowth}");
    Console.WriteLine($"PASS method equations cost {equationCosts} heartbeats; growth {equationGrowth:F3}");
    var auditGrowth = ClosureGrowth([.. sizes.Select(size => (double)size)], audits);
    var auditCosts = string.Join(", ", audits.Zip(sizes, (cost, size) => $"{cost} at {size}"));
    if (audits.Any(cost => cost <= 0) || !double.IsFinite(auditGrowth) || auditGrowth > AllowedRunSpread)
        throw new InvalidOperationException(
            $"Method axiom reports cost {auditCosts} heartbeats; growth {auditGrowth}");
    Console.WriteLine($"PASS method axiom reports cost {auditCosts} heartbeats");
    var lookups = sizes.Select(size => (double)(auditMarks[(size, "lookups")] - auditMarks[(size, "end")])).ToArray();
    var lookupGrowth = ClosureGrowth([.. sizes.Select(size => (double)size)], lookups);
    var lookupCosts = string.Join(", ", lookups.Zip(sizes, (cost, size) => $"{cost} at {size}"));
    if (lookups.Any(cost => cost <= 0) || !double.IsFinite(lookupGrowth) || lookupGrowth > AllowedRunSpread)
        throw new InvalidOperationException(
            $"Supplied-program lookups cost {lookupCosts} heartbeats; growth {lookupGrowth}");
    Console.WriteLine($"PASS supplied-program lookups cost {lookupCosts} heartbeats; growth {lookupGrowth:F3}");
    var marks = LookupPatterns.RunMark.Matches(output).ToDictionary(
        match => (int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture),
            int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture), match.Groups[3].Value,
            match.Groups[4].Value),
        match => long.Parse(match.Groups[5].Value, CultureInfo.InvariantCulture));
    if (marks.Count != 2 * routes.Length * sizes.Sum(size => Positions(size).Length))
        throw new InvalidOperationException($"Missing run costs:\n{output}");
    long Cost(int size, int position, string route) =>
        marks[(size, position, route, "end")] - marks[(size, position, route, "start")];
    string Measured(string route) => string.Join("; ", sizes.Select(size => string.Create(
        CultureInfo.InvariantCulture,
        $"{string.Join(" / ", Positions(size).Select(position => Cost(size, position, route)))} at {size}")));
    void Flat(string route)
    {
        var measured = sizes.SelectMany(size => Positions(size).Select(position => Cost(size, position, route)))
            .ToArray();
        var spread = (double)measured.Max() / measured.Min();
        if (spread > AllowedRunSpread)
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $$"""
                The {{route}} route costs {{Measured(route)}} heartbeats.
                The maximum/minimum ratio {{spread:F4}} exceeds {{AllowedRunSpread}}.
                """));
    }
    foreach (var route in new[] { "rfl index", "kernel index", "stepper" })
        Flat(route);
    // A list read walks to its position, so the last method of the largest program costs most through the list.
    var largest = sizes[^1];
    foreach (var (list, index) in new[] { ("rfl list", "rfl index"), ("kernel list", "kernel index") })
        if (Cost(largest, largest - 1, list) <= Cost(largest, largest - 1, index) ||
            Cost(largest, largest - 1, list) <= Cost(largest, 0, list))
            throw new InvalidOperationException($"The {list} route no longer walks the list: {Measured(list)}");
    foreach (var route in routes)
        Console.WriteLine($"PASS the {route} route costs {Measured(route)} heartbeats at methods 1, n/2 and n");
}

// How many times as much each added unit costs between the last two sizes as between the first two.
static double ClosureGrowth(double[] units, double[] costs) =>
    (costs[2] - costs[1]) / (units[2] - units[1]) / ((costs[1] - costs[0]) / (units[1] - units[0]));

// Four times the rows allow logarithmic index growth but rule out repeated scans of the table.
// Builds the fixture before returning the measurement, so no dotnet build runs beside a concurrent check.
Action LayoutIdentityCosts()
{
    var directory = At("artifacts/LookupScaling/LayoutIdentities");
    Directory.CreateDirectory(directory);
    var sharedLayoutCost = SharedLayoutCost(directory);
    return () =>
    {
        double previousPerRow = 0;
        foreach (int count in new[] { 32, 128, 512 })
        {
            var names = Enumerable.Range(0, count).Select(index => $"row \"Scope::Layout{index:D4}\"");
            var header = $$"""
                import CIL.Extraction.Layout
                /-! Cost of validating distinct layouts with fixed-width type identities. -/
                set_option maxRecDepth 65536
                set_option maxHeartbeats 0
                namespace LayoutIdentityCost
                open CIL CIL.Extraction
                /-- An empty sequential struct with the given identity. -/
                def row (name : String) : RawLayout :=
                  { identity := name, explicit := false, packing := 0, declaredSize := 0, fields := [] }
                /-- The rows compared by identity. -/
                def raw := [{{string.Join(", ", names)}}]
                /-- Each empty struct occupies one byte. -/
                def layouts : Array ComputedLayout := Array.replicate {{count}} ⟨⟨1, []⟩, 1⟩

                """;
            var path = Path.Combine(directory, $"Rows{count}.lean");
            long cost = DecideCost(path, header, "LayoutsValid raw layouts", "LayoutIdentityCost");
            double perRow = (double)cost / count;
            Console.WriteLine($"Layout identities at {count} rows cost {cost} heartbeats ({perRow:F1} per row)");
            if (cost < KernelDecisionFloor || previousPerRow > 0 && perRow > 1.5 * previousPerRow)
                throw new InvalidOperationException($"Layout validation exceeds its growth bound at {count} rows.");
            previousPerRow = perRow;
        }
        sharedLayoutCost();
    };
}

Action SharedLayoutCost(string directory)
{
    const int rowCount = 8;
    var assembly = Path.Combine(directory, "Assembly");
    Directory.CreateDirectory(assembly);
    var project = Path.Combine(assembly, "SharedLayouts.csproj");
    File.WriteAllText(project, """
        <Project Sdk="Microsoft.NET.Sdk">
          <PropertyGroup><TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
        </Project>
        """);
    var rows = Enumerable.Range(0, rowCount).Select(index =>
    {
        var field = index == 0 ? "int" : $"Row{index - 1}";
        return $"public struct Row{index} {{ public {field} Value; }}";
    });
    File.WriteAllText(Path.Combine(assembly, "SharedLayouts.cs"), $$"""
        {{string.Join("\n", rows)}}
        public static class SharedLayouts
        {
            static int First(int value) => value + 1;
            static int Second(int value) => value + 2;
            static int Third(int value) => value + 3;
            public static int Read(Row7 row) =>
                Third(Second(First(row.Value.Value.Value.Value.Value.Value.Value.Value)));
        }
        """);
    Run(["dotnet", "build", project, "-c", "Release"]);
    return () =>
    {
        var output = Path.Combine(directory, "Read");
        Run(Extract("extract", Path.Combine(assembly, "bin/SharedLayouts.dll"), "SharedLayouts",
            "SharedLayouts::Read(Row7)", output));
        using var manifest =
            System.Text.Json.JsonDocument.Parse(File.ReadAllText(Path.Combine(output, "identity.json")));
        var extraction = manifest.RootElement;
        if (extraction.GetProperty("methods").GetArrayLength() != 4 ||
            extraction.GetProperty("layoutIdentities").GetArrayLength() != rowCount)
            throw new InvalidOperationException("Expected four methods and eight layout rows in the cost fixture.");
        var source = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
        var (cost, _) = CountHeartbeats(Path.Combine(directory, "SharedLayouts.lean"), source);
        const long limit = 45_000_000;
        Console.WriteLine($"Four methods sharing {rowCount} layouts cost {cost} whole-file heartbeats (limit {limit})");
        if (cost > limit) throw new InvalidOperationException("Shared layout extraction exceeds its whole-file bound.");
    };
}

// Primitive argument storage costs at most 150,000 heartbeats per parameter, independently of unused layouts.
void ClosedArgumentsCosts()
{
    var storageDirectory = At("artifacts/LookupScaling/ClosedArguments");
    Directory.CreateDirectory(storageDirectory);
    const long PerParameterLimit = 150_000;
    const double LayoutGrowthLimit = 1.05;
    var samples = new List<(int Parameters, int Layouts, long Cost)>();
    foreach (var parameters in new[] { 1, 4, 16 })
    foreach (var layouts in new[] { 8, 32, 128 })
    {
        var path = Path.Combine(storageDirectory, $"Parameters{parameters}Layouts{layouts}.lean");
        File.WriteAllText(path, $$"""
            import CIL.Extraction.Generics
            import Lean
            /-! Kernel cost of closed primitive arguments with unrelated aggregate layouts. -/
            set_option maxRecDepth 10000
            set_option maxHeartbeats 0
            open CIL CIL.Extraction Lean Elab Command
            {{KernelCostCommand}}
            /-- Every parameter is the exact scoped uint32 type. -/
            def raw : RawMethod := {
              token := 0, owner := "Scaling", hasThis := false, explicitThis := false,
              callingConvention := 0, attributes := 150, implementation := 0, returnType := .void,
              parameters := List.replicate {{parameters}} (.primitive .uint32),
              locals := [], initLocals := false, maxStack := 1, genericParameters := [],
              code := [.mk 0 42 .none] }
            /-- Primitive argument storage does not inspect unrelated layouts. -/
            def layouts : List RawLayout := List.replicate {{layouts}} {
              identity := "Unrelated", explicit := false, packing := 0, declaredSize := 4,
              fields := [.mk .unsigned32 none] }
            #kernel_cost "closed arguments {{parameters}} {{layouts}}"
              closedArguments layouts raw = some
                (.mk (List.replicate {{parameters}} (.field .unsigned32)) [] [.other])
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.ClosedArguments.Match(output);
        if (!cost.Success) throw new InvalidOperationException($"Missing the closed argument cost:\n{output}");
        samples.Add((parameters, layouts, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture)));
    }
    foreach (var sample in samples)
    {
        var firstLayout = samples.Single(row => row.Parameters == sample.Parameters && row.Layouts == 8);
        var firstParameter = samples.Single(row => row.Parameters == 1 && row.Layouts == sample.Layouts);
        var perParameter = (double)sample.Cost / sample.Parameters;
        if (sample.Cost < KernelDecisionFloor || perParameter > PerParameterLimit ||
            sample.Cost > firstLayout.Cost * LayoutGrowthLimit ||
            perParameter > firstParameter.Cost * AllowedLocalGrowth)
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"Closed arguments cost {perParameter:F1} heartbeats per parameter at " +
                $"{sample.Parameters} parameters and {sample.Layouts} layouts; limit {PerParameterLimit}, " +
                $"layout growth {LayoutGrowthLimit}, parameter growth {AllowedLocalGrowth}."));
        Console.WriteLine(string.Create(CultureInfo.InvariantCulture,
            $"PASS closed arguments {sample.Parameters} parameters {sample.Layouts} layouts: " +
            $"{sample.Cost} heartbeats, {perParameter:F1} per parameter"));
    }
}

// The heartbeats `decide +kernel` adds to one `add` of an int32 offset to a native method table of 16, 64 and 256
// entries and to one load of its first and of its last entry, each table and its storage defined once outside the
// decision. The step and the load's bound read the table's entry count, not its entries, so their cost may grow by at
// most `AllowedGrowth` between sizes. Reading entry i walks i cells of the literal, so the last entry's cost beyond
// the first's may grow per index by at most `AllowedGrowth`.
void NativeTableCosts()
{
    var tableDirectory = At("artifacts/LookupScaling/NativeTableStep");
    Directory.CreateDirectory(tableDirectory);
    var costs = new List<(int Entries, long Step, long First, long Last)>();
    foreach (var entries in new[] { 16, 64, 256 })
    {
        var targets = string.Join(", ", Enumerable.Range(1, entries).Select(token => $"⟨\"Handlers\", {token}, []⟩"));
        var path = Path.Combine(tableDirectory, $"Entries{entries}.lean");
        File.WriteAllText(path, $$"""
            import CIL.Safety.Execution
            set_option maxRecDepth 8192
            open CIL CIL.Safety Lean Elab Command
            {{KernelCostCommand}}
            namespace NativeTableStep
            /-- The closed signature every entry shares. -/
            def signature : ManagedSignature := ⟨.void, []⟩
            /-- The {{entries}} supplied entries, the entry at index i holding token i + 1. -/
            def targets : Array ManagedIdentity := #[{{targets}}]
            /-- A supplied native table of the entries whose storage is static binding 42. -/
            def table : MethodTable :=
              { signature, targets := some targets, backing := some ⟨42, 0⟩, entryCount := {{entries}} }
            /-- The table with its cursor on the last entry. -/
            def lastTable : MethodTable :=
              { signature, targets := some targets, backing := some ⟨42, {{8 * (entries - 1)}}⟩,
                entryCount := {{entries}} }
            /-- Immutable static storage holding exactly the table's entries. -/
            def memory : CIL.Safety.Memory :=
              { allocations := fun index => if index == 0 then
                  some { kind := .immutableStatic, layout := ⟨{{8 * entries}}, 8, []⟩ } else none
                cells := fun _ _ => ⟨0, true⟩
                views := [⟨0, 0, {{8 * entries}}, true, false⟩]
                nextIdentity := 1
                staticBindings := [(42, ⟨0, 0⟩)] }
            /-- A body with no code; the step reads only its profile. -/
            def body : CIL.Method := { code := [], locals := [], returnsValue := false }
            /-- The frame of the step, which owns nothing. -/
            def frame : CIL.Safety.Frame := { activation := 0, locals := [], owned := [] }
            #kernel_cost "table step {{entries}}" (match CIL.Safety.step body .add 0 [] frame
                [.scalar (.i32 8), .methodTable table] memory with
              | .ok (.next _ [.methodTable moved] _ _) => moved.backing
              | _ => none) = some ⟨42, 8⟩
            #kernel_cost "table load first {{entries}}" (match loadNativeTable table memory with
              | .ok ⟨_, some ⟨_, token, _⟩⟩ => token == 1
              | _ => false) = true
            #kernel_cost "table load last {{entries}}" (match loadNativeTable lastTable memory with
              | .ok ⟨_, some ⟨_, token, _⟩⟩ => token == {{entries}}
              | _ => false) = true
            end NativeTableStep
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        long Measured(Regex pattern, string row)
        {
            var cost = pattern.Match(output);
            if (!cost.Success) throw new InvalidOperationException($"Missing the native table {row} cost:\n{output}");
            return long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture);
        }
        costs.Add((entries, Measured(LookupPatterns.NativeTableStep, "step"),
            Measured(LookupPatterns.NativeTableLoadFirst, "first load"),
            Measured(LookupPatterns.NativeTableLoadLast, "last load")));
    }
    RequireConstant("one native table step", costs.Select(sample => (sample.Entries, sample.Step)).ToList());
    RequireConstant("one load of a native table's first entry",
        costs.Select(sample => (sample.Entries, sample.First)).ToList());
    // The last entry sits at index entries - 1, so its cost beyond the first entry's is divided by that index.
    var perIndex = costs.Select(sample => (sample.Entries, sample.Last,
        PerIndex: (sample.Last - sample.First) / (sample.Entries - 1))).ToList();
    var walked = string.Join("; ", perIndex.Select(sample =>
        $"{sample.Last} heartbeats, {sample.PerIndex} per index, at {sample.Entries}"));
    if (costs.Any(sample => sample.Last < KernelDecisionFloor) ||
        perIndex.Skip(1).Any(sample => sample.PerIndex > perIndex[0].PerIndex * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Loading a native table's last entry costs {walked}; the limit is {AllowedGrowth} times the cost per " +
            $"index at {costs[0].Entries} entries."));
    Console.WriteLine($"PASS loading a native table's last entry costs {walked} entries");
}

// Fails unless every cost is a real decision and none exceeds `AllowedGrowth` times the cost at the smallest size.
void RequireConstant(string row, List<(int Entries, long Cost)> costs)
{
    var measured = string.Join("; ", costs.Select(sample => $"{sample.Cost} heartbeats at {sample.Entries} entries"));
    if (costs.Any(sample => sample.Cost < KernelDecisionFloor) ||
        costs.Skip(1).Any(sample => sample.Cost > costs[0].Cost * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Deciding {row} costs {measured}; the limit is {AllowedGrowth} times the cost at " +
            $"{costs[0].Entries} entries."));
    Console.WriteLine($"PASS deciding {row} costs {measured}");
}

// The heartbeats `decide +kernel` adds to the same statement closed with `sorry`, for equal and unequal type
// identities whose names have 20 and 80 characters and share all but their last character. Each statement is
// distinct, so no decision reuses the auxiliary lemma of another.
Dictionary<string, long> TypeDecisionCosts()
{
    const string Prefix = "System.Runtime.InteropServices.Marshalling.Collections.Generic.Dictionary.Keys.";
    string Type(int length, char last)
    {
        var name = Prefix[..(length - 1)] + last;
        return $$"""({ assembly := runtime, typeNamespace := name!"System", name := name!"{{name}}" } : """ +
            "TypeIdentity)";
    }
    var statements = new[] { 20, 80 }.SelectMany(length => new[]
    {
        $"#kernel_cost \"equal {length}\" {Type(length, '0')} = {Type(length, '0')}",
        $"#kernel_cost \"unequal {length}\" Not ({Type(length, '1')} = {Type(length, '2')})"
    });
    var path = Path.Combine(directory, "TypeIdentityEquality.lean");
    File.WriteAllText(path, """
        import CIL.Identity
        open CIL Lean Elab Command
        /-- The core library assembly of .NET 11. -/
        def runtime : AssemblyName :=
          { name := name!"System.Runtime", version := { major := 11, minor := 0, build := 0, revision := 0 },
            culture := name!"", publicKeyToken := some 0xb03f5f7f11d50a3a }

        """ + KernelCostCommand + "\n" + string.Join("\n", statements) + "\n");
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.TypeDecision.Matches(output).ToDictionary(
        match => match.Groups[1].Value, match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
    if (costs.Count != 4) throw new InvalidOperationException("Missing type identity decision costs:\n" + output);
    return costs;
}
void TypeIdentityCosts()
{
    var decisions = TypeDecisionCosts();
    foreach (var outcome in new[] { "equal", "unequal" })
    {
        long shortName = decisions[$"{outcome} 20"], longName = decisions[$"{outcome} 80"];
        var measured = $"{shortName} heartbeats at 20 characters and {longName} at 80";
        if (Math.Min(shortName, longName) < KernelDecisionFloor || Math.Max(shortName, longName) > TypeDecisionLimit ||
            longName > shortName * AllowedNameGrowth)
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"""
                Deciding {outcome} type identities costs {measured}; the limits are {TypeDecisionLimit} heartbeats
                and {AllowedNameGrowth} times as many at 80 characters.
                """).ReplaceLineEndings(" "));
        Console.WriteLine($"PASS deciding {outcome} type identities costs {measured}");
    }
}

// Each input quadruples the number of distinct exports, links and call instructions together.
void ImportLinkCosts()
{
    int[] sizes = [12, 48, 192];
    var directory = At("artifacts/LookupScaling/ImportLinks");
    Directory.CreateDirectory(directory);
    var path = Path.Combine(directory, "ImportLinks.lean");
    var samples = sizes.Select(size => $"""#kernel_cost "import links {size}" (checkLinks {size} = true)""");
    File.WriteAllText(path, $$"""
        import CIL.Extraction.BodyDecoding
        open CIL CIL.Extraction Lean Elab Command
        {{KernelCostCommand}}
        /-- Distinct static exports with a scalar call shape. -/
        def slot (index : Nat) : ImportSlot :=
          { identity := toString index, closureDigest := "", parameterCount := 0,
            hasThis := false, returnsValue := false }
        /-- Every direct call uses its own export at the matching instruction index. -/
        def checkLinks (count : Nat) : Bool :=
          let indices := List.range count
          let imports := ImportSlotIndex.ofList (indices.map slot)
          let bound := imports.forLinks 1 (indices.map fun i => (i, .direct (i + 1)))
          let sites := indices.map fun i =>
            let method := { MethodRef.arity 0 with hasThis := false }
            let site : CallSite :=
              { method, declared := method.signature 0, target := .external (toString i),
                typeArguments := [], parameterCount := 0, returnsValue := false }
            ({ offset := i, opcode := 0x28, operand := .call site } : RawInstruction)
          bound.calls.length == count && bound.checkUses bound.byIdentity sites
        {{string.Join("\n", samples)}}
        """);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.ImportLinkCost.Matches(output).ToDictionary(
        match => int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture),
        match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
    if (costs.Count != sizes.Length || costs.Values.Any(cost => cost < KernelDecisionFloor))
        throw new InvalidOperationException($"""Missing import link costs: {output}""");
    var measured = string.Join(", ", sizes.Select(size => $"""{costs[size]} at {size}"""));
    if (sizes.Zip(sizes.Skip(1)).Any(pair => costs[pair.Second] > 2 * costs[pair.First] * pair.Second / pair.First))
        throw new InvalidOperationException($"""Import lookup cost per call more than doubled: {measured}""");
    Console.WriteLine($"""PASS import link checks cost {measured} heartbeats""");
}

// Compare each lookup at three table sizes, including identical names scoped by different assemblies.
void PlatformTableCosts()
{
    var tableDirectory = At("artifacts/LookupScaling/PlatformTables");
    Directory.CreateDirectory(tableDirectory);
    int[] sizes = [16, 128, 1024];
    string[] sites = ["reference", "enum", "pair", "chain", "constant", "base", "shared", "scoped", "missing"];
    static string Bytes(string text) => $"""[{string.Join(", ", Encoding.UTF8.GetBytes(text))}]""";
    static string Parts(string space, string name) => $"[{Bytes(space)}, {Bytes(name)}]";
    // Table names in the literal form an extraction writes, so the literal costs what an extraction's does.
    static string Literal(string text) => ByteLiterals.Of(Encoding.UTF8.GetBytes(text));
    // The typed assembly in the literal form an extraction writes: `runtimeAssembly` by default.
    static string Assembly(string name, string version = "0, 0, 0, 0", string token = "none") =>
        $$"""{ name := name!"{{name}}", version := ⟨{{version}}⟩, culture := name!"", publicKeyToken := {{token}} }""";
    string runtime = Assembly("System.Runtime", "11, 0, 0, 0", "some 0xb03f5f7f11d50a3a");
    string Definition(string space, string name, string kind, string? assembly = null) =>
        $$"""{ assembly := {{assembly ?? runtime}}, parts := [{{Literal(space)}}, {{Literal(name)}}], """ +
        $$"""kind := {{kind}} }""";
    // The depth an extraction sets for its list, so a list it would refuse to compile fails here.
    static string Depth(int count) => $"set_option maxRecDepth {PlatformDefinitions.RecursionDepth(count)} in";
    string[] relied =
    [
        Definition("System", "Console", ".classType"), Definition("System", "Object", ".objectRoot"),
        Definition("System", "ValueType", ".valueTypeRoot"), Definition("System", "ValueTuple`2", ".valuePair"),
        Definition("System", "BitConverter", ".byteOrder"), Definition("", "Number", ".enumType 8"),
    ];
    string Table(int size) => $$"""
        #elab_cost "platform elaboration {{size}}"
        {{Depth(size + relied.Length)}}
        /-- The definitions the sites rely on among {{size}} others of distinct names. -/
        def table{{size}} : PlatformTable := platform_table% [
          {{string.Join(",\n  ", relied.Concat(Enumerable.Range(0, size).Select(index =>
              Definition("Filler", $"Type{index:D5}", ".classType"))))}}]
        {{Depth(size)}}
        /-- {{size}} classes named `Enumerator`, each in a namespace of its own. -/
        def shared{{size}} : PlatformTable := platform_table% [
          {{string.Join(",\n  ", Enumerable.Range(0, size).Select(index =>
              Definition($"Shared{index:D5}", "Enumerator", ".classType")))}}]
        {{Depth(size)}}
        /-- Identical names alternate between class and value storage in distinct scopes. -/
        def scopes{{size}} : PlatformTable := platform_table% [
          {{string.Join(",\n  ", Enumerable.Range(0, size).Select(index =>
              Definition("Shared", "Enumerator", index % 2 == 0 ? ".classType" : ".valueType",
                  Assembly($"Scope{index:D5}"))))}}]
        /-- The environment of no slices under the table. -/
        def env{{size}} : MetadataEnv := MetadataEnv.ofSlices [] (platform := table{{size}})
        #kernel_cost "platform reference {{size}}"
          ((env{{size}}.externalNamed 0 runtimeAssembly (bytesOf "System.Console")
            {{Parts("System", "Console")}} (some false)).isOk = true)
        #kernel_cost "platform enum {{size}}"
          ((do
            let head <- env{{size}}.externalNamed 0 runtimeAssembly (bytesOf "Number")
              {{Parts("", "Number")}} (some true)
            let frame : Frame :=
              { corlib := some runtimeScopeBytes, anchor := runtimeScopeBytes, arity := 0, ownerArity := 0 }
            return frame.admits (.named head)
              (.enum { assembly := runtimeAssembly, typeNamespace := name!"", name := name!"Number" }
                .signed32)).toOption = some true)
        #kernel_cost "platform pair {{size}}"
          ((env{{size}}.platformField 0
            { owner := .genericInst (named "System.ValueTuple`2" {{Parts("System", "ValueTuple`2")}})
                (.cons (.primitive 8) (.cons (.primitive 10) .nil)),
              name := bytesOf "Item2", declared := .var 1, definition := none }
            (.primitive 10) false false).isOk = true)
        #kernel_cost "platform chain {{size}}"
          ((env{{size}}.chainRoot 0 0 runtimeAssembly {{Parts("System", "Object")}} true).isOk = true)
        #kernel_cost "platform constant {{size}}"
          ((env{{size}}.platformConstant 0
            { owner := .named (named "System.BitConverter" {{Parts("System", "BitConverter")}}),
              name := bytesOf "IsLittleEndian", declared := .primitive 2, definition := none }
            (.primitive 2) true true).isOk = true)
        #kernel_cost "platform base {{size}}"
          ((table{{size}}.require 0 runtimeAssembly {{Parts("System", "ValueType")}}
            (baseFits true {{Parts("System", "ValueType")}})).isOk = true)
        #kernel_cost "platform shared {{size}}"
          (shared{{size}}.kindOf runtimeAssembly {{Parts($"Shared{size / 2:D5}", "Enumerator")}} =
            some .classType)
        #kernel_cost "platform scoped {{size}}"
          (scopes{{size}}.kindOf {{Assembly($"Scope{size - 2:D5}")}} {{Parts("Shared", "Enumerator")}} =
              some .classType /\
            scopes{{size}}.kindOf {{Assembly($"Scope{size - 1:D5}")}} {{Parts("Shared", "Enumerator")}} =
              some .valueType /\
            scopes{{size}}.kindOf {{Assembly($"Scope{size:D5}")}} {{Parts("Shared", "Enumerator")}} = none)
        #kernel_cost "platform missing {{size}}"
          (table{{size}}.kindOf runtimeAssembly {{Parts("System", "Absent")}} = none)
        """;
    var path = Path.Combine(tableDirectory, "PlatformTables.lean");
    File.WriteAllText(path, $$"""
        import CIL.Extraction.MetadataBinding
        open CIL CIL.Extraction Lean Elab Command
        {{KernelCostCommand}}
        /-- Logs what elaborating a command costs. -/
        elab "#elab_cost " label:str command:command : command => do
          let before <- IO.getNumHeartbeats
          elabCommand command
          let after <- IO.getNumHeartbeats
          logInfo m!"{label.getString} {after - before} heartbeats"
        /-- A runtime type outside the carried slices, as a reference resolves it. -/
        def named (name : String) (parts : List (List Nat)) : NamedType :=
          { scope := runtimeScopeBytes, name := bytesOf name, parts, kind := .external (some false),
            pinned := false, assembly := some runtimeAssembly }
        {{string.Join("\n", sizes.Select(Table))}}
        """);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.PlatformTableCost.Matches(output).ToDictionary(
        match => (match.Groups[1].Value, int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture)),
        match => long.Parse(match.Groups[3].Value, CultureInfo.InvariantCulture));
    if (costs.Count != (sites.Length + 1) * sizes.Length ||
        sites.Any(site => sizes.Any(size => costs[(site, size)] < KernelDecisionFloor)))
        throw new InvalidOperationException($"""Missing platform table costs: {output}""");
    var perDefinition = sizes.Select(size => (double)costs[("elaboration", size)] / (size + relied.Length)).ToArray();
    var rates = string.Join(", ", sizes.Zip(perDefinition).Select(pair =>
        string.Create(CultureInfo.InvariantCulture, $"{pair.Second:F0} at {pair.First}")));
    if (perDefinition.Zip(perDefinition.Skip(1)).Any(pair => pair.Second > pair.First * AllowedGrowth))
        throw new InvalidOperationException($"Platform elaboration exceeds {AllowedGrowth} times: {rates}");
    Console.WriteLine($"Elaborating a platform table costs {rates} heartbeats per definition");
    foreach (var site in sites)
    {
        var measured = string.Join(", ", sizes.Select(size =>
            string.Create(CultureInfo.InvariantCulture, $"{costs[(site, size)]} at {size}")));
        var grows = sizes.Zip(sizes.Skip(1))
            .Any(pair => costs[(site, pair.Second)] > costs[(site, pair.First)] * AllowedGrowth);
        if (grows)
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"""Platform {site} costs {measured} heartbeats, exceeding the growth limit of {AllowedGrowth}."""));
        Console.WriteLine($"PASS the platform {site} check costs {measured} heartbeats at that many definitions");
    }
}

// The heartbeats `decide +kernel` adds to the name clause of the call and field operand checks, which reads a typed
// name back and compares its bytes with the row's. Names of 20, 80 and 320 bytes share all but their last byte. The
// clause reads one byte per step, so the cost per byte may grow at most `AllowedGrowth` times from one length to the
// next.
void MetadataNameCosts()
{
    var nameDirectory = At("artifacts/LookupScaling/MetadataNames");
    Directory.CreateDirectory(nameDirectory);
    const string Prefix = "WriteLineToTheConsoleOfTheRuntimeEachValueThatTheCallerPassesAsAnIntegerOfThirtyTwoBits";
    int[] lengths = [20, 80, 320];
    string Statement(int length)
    {
        var name = string.Concat(Enumerable.Repeat(Prefix, length / Prefix.Length + 1))[..(length - 1)] + "0";
        var bytes = string.Join(", ", Encoding.UTF8.GetBytes(name));
        return $$"""
            /-- The {{length}} bytes of a row name. -/
            def bytes{{length}} : List Nat := [{{bytes}}]
            /-- The metadata name of those bytes. -/
            def name{{length}} : MetadataName := name!"{{name}}"
            #kernel_cost "name spells {{length}}" (name{{length}}.spells bytes{{length}} = true)
            """;
    }
    var path = Path.Combine(nameDirectory, "MetadataNames.lean");
    File.WriteAllText(path, $$"""
        import CIL.Identity
        open CIL Lean Elab Command
        {{KernelCostCommand}}
        {{string.Join("\n", lengths.Select(Statement))}}
        """);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.MetadataNameCost.Matches(output).ToDictionary(
        match => int.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture),
        match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
    if (costs.Count != lengths.Length)
        throw new InvalidOperationException("Missing metadata name costs:\n" + output);
    double PerByte(int length) => (double)costs[length] / length;
    var measured = string.Join(", ", lengths.Select(length =>
        string.Create(CultureInfo.InvariantCulture, $"{costs[length]} at {length} bytes")));
    var flat = lengths.Zip(lengths.Skip(1)).All(pair => PerByte(pair.Second) <= PerByte(pair.First) * AllowedGrowth);
    if (lengths.Min(length => costs[length]) < KernelDecisionFloor || !flat)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"A metadata name spells its bytes at {measured} heartbeats; per byte, the limit is " +
            $"{AllowedGrowth} times the cost at the shorter length."));
    Console.WriteLine($"PASS a metadata name spells its bytes at {measured} heartbeats");
}

// `runtimeModel` searches a literal tree of model entries by name code and compares one method reference at the leaf,
// so a lookup in 256 entries costs the four extra tree levels over 16 and no more, whether it queries the first, the
// middle or the last entry; a scan of the entries would make the last cost more. The agreement check runs one
// lookup per live call site, so its cost per site stays flat over 8, 32 and 128 sites. Each site calls a distinct
// method, so the kernel cannot reuse one site's lookup for another.
void ModelTableCosts()
{
    var tableDirectory = At("artifacts/LookupScaling/ModelTables");
    Directory.CreateDirectory(tableDirectory);
    const int modelLookupDepth = 75;
    const int layoutLookupDepth = 210;
    int[] tableSizes = [16, 256];
    int[] siteCounts = [8, 32, 128];
    string[] positions = ["first", "middle", "last"];
    int Queried(string position, int size) => position switch { "first" => 0, "middle" => size / 2, _ => size - 1 };
    string Entries(int size) => string.Join(",\n  ", Enumerable.Range(0, size).Select(index =>
        $$"""
        ModelEntry.exact .call (method name!"Model{{index:D4}}") { convention := 0 }
          (.memory (.divRemOut {{index}}))
        """));
    string RawRows(int size) => string.Join(", ", Enumerable.Range(0, size - 1).Select(i => $"row \"L{i}\" 1"));
    string Table(int size) => $$"""
        /-- {{size}} modelled methods. -/
        def entries{{size}} : List ModelEntry := [
          {{Entries(size)}}]
        /-- Their literal table. -/
        def table{{size}} : ModelTable := model_table% entries{{size}}
        {{string.Join("\n", positions.Select(position => Lookup(position, size)))}}
        /-- The target follows every unrelated layout in this table. -/
        def layouts{{size}} : LayoutEnvironment := {
          rawLayouts := [{{RawRows(size)}}, row "Target" 8]
          layouts := #[{{string.Join(", ", Enumerable.Repeat("layout 1", size - 1))}}, layout 8] }
        set_option maxRecDepth {{layoutLookupDepth}} in
        example : runtimeModel layouts{{size}} .call (sizeRef {{size - 1}}) =
            some (.constant 8) := by rfl
        """;
    string Lookup(string position, int size)
    {
        var index = Queried(position, size);
        var claim = $$"""
            table{{size}}.find {} .call (method name!"Model{{index:D4}}") = some (.memory (.divRemOut {{index}}))
            """;
        return $$"""
            set_option maxRecDepth {{modelLookupDepth}} in
            example : {{claim}} := by rfl
            #kernel_cost "model lookup {{position}} {{size}}" ({{claim}})
            """;
    }
    string Call(int index) => $$""".call (method name!"Model{{index:D4}}") {}""";
    string Site(int index) => $$"""
        ⟨{{index}}, 40, .call { method := method name!"Model{{index:D4}}", declared := { convention := 0 },
          target := .external "", typeArguments := [], parameterCount := 0, returnsValue := false }⟩
        """.ReplaceLineEndings(" ");
    string Sites(int count) => $$"""
        /-- {{count}} live calls of distinct modelled methods, the call at index i to method i. -/
        def raw{{count}} : RawMethod := { shell with code := [
          {{string.Join(",\n  ", Enumerable.Range(0, count).Select(Site))}}] }
        /-- Each site names the next method in the list, wrapping at its end. -/
        def code{{count}} : List Instruction :=
          [{{string.Join(", ", Enumerable.Range(0, count).Select(index => Call((index + 1) % count)))}}]
        /-- The same sites keeping the calls to their own methods. -/
        def calls{{count}} : List Instruction :=
          [{{string.Join(", ", Enumerable.Range(0, count).Select(Call))}}]
        #kernel_cost "model calls {{count}}"
          (ModelsAgree catalog {} .scalar raw{{count}} (List.replicate {{count}} true) calls{{count}})
        #kernel_cost "model agreement {{count}}"
          (all3 (fun raw live emitted => !live || !catalog.siteAgrees {} .scalar raw emitted)
            raw{{count}}.code (List.replicate {{count}} true) code{{count}} = true)
        """;
    var path = Path.Combine(tableDirectory, "ModelTables.lean");
    File.WriteAllText(path, $$"""
        import CIL.Extraction.CallAgreement
        open CIL CIL.Extraction Lean Elab Command
        {{KernelCostCommand}}
        /-- A static method of no parameters named `name`. -/
        def method (name : MetadataName) : MethodRef :=
          { owner := .atom "Tests" "Models" .classType, name, hasThis := false, genericArity := 0, returnType := .void,
            parameters := [] }
        /-- Only the final position in each layout table carries the eight-byte target. -/
        def sizeRef (position : Nat) : MethodRef :=
          { owner := unsafeOwner, name := name!"SizeOf", hasThis := false, genericArity := 1,
            parameters := [], returnType := .primitive .int32,
            methodArguments := [.aggregate "Target" position] }
        /-- The raw row binds a size query to its named type. -/
        def row (identity : String) (size : Nat) : RawLayout :=
          { identity, fields := [], explicit := false, packing := 0, declaredSize := size }
        /-- The computed row supplies the byte count read by the size query. -/
        def layout (size : Nat) : ComputedLayout := .mk (.mk size []) 1
        {{string.Join("\n", tableSizes.Select(Table))}}
        /-- The larger table of modelled calls. -/
        def catalog : ModelCatalog where
          table := table256
        /-- A method shell whose code each fixture supplies. -/
        def shell : RawMethod :=
          { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
            attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
            initLocals := true, maxStack := 1, genericParameters := [], code := [] }
        /-- Interleave the three sizes so each median samples the same period of machine load. -/
        def checkScaling (label : String) (limit : Nat) (measure : Nat → Nat → IO Nat) : IO Unit := do
          let sizes := #[512, 1024, 2048]
          let timers := (sizes.map measure).toList.zipIdx
          let mut samples : Array (Array Nat) := Array.replicate sizes.size #[]
          for trial in [:9] do
            for (timer, index) in timers do
              let elapsed <- timer trial
              samples := samples.modify index (·.push elapsed)
          let mut previous := 0
          for (count, values) in sizes.toList.zip samples.toList do
            let elapsed := values.qsortOrd[4]!
            IO.println s!"{label} {count}: {elapsed} ns"
            if elapsed == 0 || (previous != 0 && elapsed * 100 > previous * limit) then
              throw (IO.userError s!"{label} exceeded {limit}% of the preceding time per doubling")
            previous := elapsed
        /-- Repeated DivRem queries against two identical oversized rows. -/
        def timeOversizedTuple (count : Nat) : Nat → IO Nat :=
          let identity := integerPairIdentity "System.UInt64"
          let row : RawLayout := {
            identity, explicit := false, packing := 0, declaredSize := 0,
            fields := List.replicate count ⟨.unsigned64, none⟩ }
          let layout : ComputedLayout := ⟨⟨16, [⟨0, 8, false⟩, ⟨8, 8, false⟩]⟩, 8⟩
          let environment := LayoutEnvironment.callLayouts {
            rawLayouts := [row, row], layouts := #[layout, layout] }
          fun trial => do
            let start <- IO.monoNanosNow
            for i in [:count] do
              let pair := TypeExpr.aggregate identity ((i + trial) % 2)
              if integerPairResult environment pair .uint64 8 then
                throw (IO.userError "DivRem accepted an oversized tuple")
            return (← IO.monoNanosNow) - start
        #eval checkScaling "DivRem oversized tuple queries" 250 timeOversizedTuple
        /-- Decide the production relation on the supplied body. -/
        @[noinline] def agreedNops (raw : RawMethod) (reachable : List Bool) (body : Method) : Bool :=
          decide (RuntimeModelsAgree raw reachable body)
        /-- Prepare the body, reachability and links before timing a walk. -/
        def timeNops (live : Bool) (count : Nat) : Nat → IO Nat :=
          let raw := { shell with code := List.replicate count (.mk 0 0 .none) }
          let links := if live then [] else (List.range count).reverse.map fun pc => (pc, Link.direct pc)
          let body : Method := { code := List.replicate count .nop, links, locals := [], returnsValue := false }
          let reachable := List.replicate count live
          fun trial => do
            let start <- IO.monoNanosNow
            unless agreedNops { raw with token := trial } reachable body do
              throw (IO.userError "RuntimeModelsAgree refused nops")
            return (← IO.monoNanosNow) - start
        #eval checkScaling "RuntimeModelsAgree live nops" 230 (timeNops true)
        #eval checkScaling "RuntimeModelsAgree dead nops with reversed links" 230 (timeNops false)
        {{string.Join("\n", siteCounts.Select(Sites))}}
        """);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    foreach (var line in output.Split('\n').Where(line =>
        line.StartsWith("RuntimeModelsAgree ", StringComparison.Ordinal) ||
        line.StartsWith("DivRem ", StringComparison.Ordinal)))
        Console.WriteLine(line.TrimEnd());
    var costs = LookupPatterns.ModelTableCost.Matches(output).ToDictionary(
        match => (match.Groups[1].Value, int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture)),
        match => long.Parse(match.Groups[3].Value, CultureInfo.InvariantCulture));
    if (costs.Count != positions.Length * tableSizes.Length + 2 * siteCounts.Length ||
        costs.Values.Min() < KernelDecisionFloor)
        throw new InvalidOperationException("Missing model table costs:\n" + output);
    foreach (var position in positions)
    {
        var lookups = tableSizes.Select(size => costs[("lookup " + position, size)]).ToArray();
        var lookupMeasure = string.Join(", ", tableSizes.Select(size =>
            string.Create(CultureInfo.InvariantCulture, $"{costs[("lookup " + position, size)]} at {size} entries")));
        if (lookups[1] > lookups[0] * AllowedModelLookupGrowth)
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"A model lookup of the {position} entry costs {lookupMeasure} heartbeats; the limit is " +
                $"{AllowedModelLookupGrowth} times the cost in the smaller table."));
        Console.WriteLine($"PASS a model lookup of the {position} entry costs {lookupMeasure} heartbeats");
    }
    double PerSite(int count) => (double)costs[("agreement", count)] / count;
    var agreementMeasure = string.Join(", ", siteCounts.Select(count =>
        string.Create(CultureInfo.InvariantCulture, $"{costs[("agreement", count)]} at {count} sites")));
    if (!siteCounts.Zip(siteCounts.Skip(1)).All(pair => PerSite(pair.Second) <= PerSite(pair.First) * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"The model agreement check costs {agreementMeasure} heartbeats; per site, the limit is {AllowedGrowth} " +
            $"times the cost at the smaller count."));
    Console.WriteLine($"PASS the model agreement check costs {agreementMeasure} heartbeats");
    var callCosts = siteCounts.Select(count => (Count: count, Total: costs[("calls", count)])).ToArray();
    var callMeasure = string.Join(", ", callCosts.Select(sample =>
        FormattableString.Invariant($"{sample.Total} at {sample.Count} calls")));
    if (callCosts.Zip(callCosts.Skip(1)).Any(pair =>
        pair.Second.Total * pair.First.Count > pair.First.Total * pair.Second.Count))
        throw new InvalidOperationException($"Modelled call heartbeats per site increased ({callMeasure}).");
    Console.WriteLine($"PASS modelled call heartbeats per site are nonincreasing ({callMeasure})");
}

var source = Path.Combine(directory, "Assembly");
Directory.CreateDirectory(source);
File.WriteAllText(Path.Combine(source, "Lookups.csproj"), """
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
</Project>
""");
string Method(string name, int statements) =>
    $"public static ulong {name}(ulong x, ulong y) {{ ulong word = x; " +
    string.Concat(Enumerable.Repeat("word = word * y + x; ", statements)) + "return word; } ";
// A body with a call at every statement, to measure what its link table and link facts cost.
string Calling(string name, int calls) =>
    $"public static ulong {name}(ulong x, ulong y) {{ ulong word = x; " +
    string.Concat(Enumerable.Repeat("word = Step(word, y); ", calls)) + "return word; } ";
// A long body with two calls, where the link table stays the same size as the body grows.
string Sparse(string name, int statements) =>
    $"public static ulong {name}(ulong x, ulong y) {{ ulong word = Step(x, y); " +
    string.Concat(Enumerable.Repeat("word = word * y + x; ", statements)) +
    "word = Step(word, y); return word; } ";
File.WriteAllText(Path.Combine(source, "Lookups.cs"), "public static class Lookups { " +
    Method("Short", ShortStatements) + Method("Middle", MiddleStatements) + Method("Long", LongStatements) +
    "public static ulong Step(ulong a, ulong b) { return a * b + a; } " +
    Calling("Few", FewCalls) + Calling("Many", ManyCalls) +
    Sparse("SparseShort", SparseShortStatements) + Sparse("SparseLong", SparseLongStatements) + "}");
Run(["dotnet", "build", Path.Combine(source, "Lookups.csproj"), "-c", "Release"]);
var assembly = Path.Combine(source, "bin/Lookups.dll");

// The heartbeats `text` costs, imports included.
long Heartbeats(string path, string text, bool equations = true) => Reported(path, text, equations).Count;

// The heartbeats `text` costs, imports included, and Lean's output.
(long Count, string Output) Reported(string path, string text, bool equations = true)
{
    var (count, output) = CountHeartbeats(path, text);
    // Each file reports the last equation's axioms once; a report per equation would walk the body each time.
    if (equations && LookupPatterns.EquationAxioms.Count(output) != 1)
        throw new InvalidOperationException("Instruction equations must depend on propext alone:\n" + output);
    return (count, output);
}

// The heartbeats of each part of one file after the first, each read between two counts and less the cost of reading
// a count. Three counts follow the first part, so every part is read after the evaluator has run.
long[] PartHeartbeats(string path, IReadOnlyList<string> parts)
{
    const string Reading = "#eval show IO Nat from IO.getNumHeartbeats\n";
    var text = new StringBuilder(parts[0]).Append(Reading).Append(Reading).Append(Reading);
    foreach (var part in parts.Skip(1)) text.Append(part).Append(Reading);
    File.WriteAllText(path, text.ToString());
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    if (output.Contains("sorryAx", StringComparison.Ordinal))
        throw new InvalidOperationException("A measured file depends on sorryAx: " + path);
    long[] readings = [.. HeartbeatCount.Matches(output)
        .Select(match => long.Parse(match.Groups[1].Value, CultureInfo.InvariantCulture))];
    if (readings.Length != parts.Count + 2)
        throw new InvalidOperationException($"Expected {parts.Count + 2} heartbeat counts in {path}:\n{output}");
    var reading = readings[2] - readings[1];
    return [.. Enumerable.Range(3, parts.Count - 1).Select(index => readings[index] - readings[index - 1] - reading)];
}

// The kernel heartbeats of deciding `statement` after `header`, less those of stating it, read in one file with the
// statement first. The file closes namespace `scope`, which the header opens.
long DecideCost(string path, string header, string statement, string scope)
{
    var costs = PartHeartbeats(path, [header, $"example : Prop := {statement}\n",
        $"theorem valid : {statement} := by decide +kernel\n#print axioms valid\n", $"end {scope}\n"]);
    return costs[1] - costs[0];
}

// The last pc is the farthest from the head of the code list. Its equation must keep the statement
// stepping tactics rewrite with, depend on `propext` alone, and still be fetched by `cil_code`.
(long Count, string Output) Checked(string path, string text, string binder, string method, string equation,
    int last, string verifyAfter = "")
{
    var statement = $"example {binder}: {method}.code[{last}]? = some CIL.Instruction.ret";
    var checks = $"""

        {statement} := {equation}
        {statement} := by simp only [cil_code]
        """;
    // CountHeartbeats reads the first count. The independent equality is checked outside the measured row.
    if (verifyAfter.Length > 0)
        checks = $"""
            {checks}
            #eval show IO Nat from IO.getNumHeartbeats
            {verifyAfter}
            """;
    return Reported(path, $"""{text}{checks}""");
}

// The extraction with its call check and its method evidence theorem each reporting the heartbeats it costs alone.
string WithEvidenceCosts(string extracted)
{
    const string Command = """
        /-- Elaboration and kernel checking of one command, labelled in the report. -/
        elab "#evidence_cost " label:str " in " command:command : command => do
          let before <- IO.getNumHeartbeats
          Lean.Elab.Command.elabCommand command
          let after <- IO.getNumHeartbeats
          Lean.logInfo m!"evidence {label.getString} {after - before} heartbeats"

        """;
    var namespaces = LookupPatterns.ExtractedNamespace.Matches(extracted).Count;
    var calls = LookupPatterns.CallsTheorem.Matches(extracted).Count;
    var evidence = LookupPatterns.EvidenceTheorem.Matches(extracted).Count;
    if (namespaces != 1 || calls != 1 || evidence != 1)
        throw new InvalidOperationException("Missing the namespace, call check or evidence theorem of method0.");
    var labelled = LookupPatterns.ExtractedNamespace.Replace(extracted, match => Command + match.Value);
    labelled = LookupPatterns.CallsTheorem.Replace(labelled,
        match => "#evidence_cost \"calls\" in\n" + match.Value);
    return LookupPatterns.EvidenceTheorem.Replace(labelled,
        match => "#evidence_cost \"assembly\" in\n" + match.Value);
}

// The heartbeats of the call check and of the evidence theorem that `WithEvidenceCosts` reports.
(long Calls, long Assembly) EvidenceCosts(string output)
{
    var costs = LookupPatterns.EvidenceCost.Matches(output).ToDictionary(match => match.Groups[1].Value,
        match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
    return costs.Count == 2 && costs.TryGetValue("calls", out var calls) &&
        costs.TryGetValue("assembly", out var assembled)
        ? (calls, assembled)
        : throw new InvalidOperationException("Missing the call check and evidence theorem costs:\n" + output);
}

// The three places `cil_instruction_equations` states lookup equations for one method: its extraction, a
// hand-written body with a parameter, and the shared template of the extraction.
(int Instructions, long[] Heartbeats, (long Calls, long Assembly) Evidence) Measure(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var shared = Path.Combine(output, "Shared");
    Run(["dotnet", ExtractorPath, "templates", shared, output]);
    var templates = File.ReadAllText(Path.Combine(shared, "Templates.lean"));
    using var module = Mono.Cecil.ModuleDefinition.ReadModule(assembly);
    var instructions = module.GetType("Lookups").Methods.Single(method => method.Name == name).Body.Instructions.Count;
    var depth = LookupPatterns.RecursionDepth.Match(extracted);
    if (!depth.Success || !IsDecodedMethod(extracted, 0) || !LookupPatterns.FirstEquations.IsMatch(extracted) ||
        !templates.Contains("cil_template_code% (Input0.method0.code)", StringComparison.Ordinal) ||
        !templates.Contains("cil_instruction_equations method0", StringComparison.Ordinal))
        throw new InvalidOperationException($"Missing the decoded body, equations or recursion depth of {name}.");
    var last = instructions - 1;
    var extraction = Checked(Path.Combine(output, "Measured.lean"),
        WithEvidenceCosts(extracted) + $"\n#print axioms Extracted.method0_instruction{last}\n",
        "", "Extracted.method0", $"Extracted.method0_instruction{last}", last,
        $"#guard Extracted.method0Reachable == List.replicate {instructions} true");
    const string Binder = "(profile : CIL.FeatureProfile) (environment : CIL.LayoutEnvironment) ";
    var statements = name == "Short" ? ShortStatements : LongStatements;
    var operations = string.Join(", ", Enumerable.Repeat(".ldarg 1, .mul, .ldarg 0, .add", statements));
    var body = $$"""
        def method0 (profile : FeatureProfile) (environment : LayoutEnvironment) : Method :=
          { profile, environment, locals := [], returnsValue := true, code := [.ldarg 0, {{operations}}, .ret] }
        """;
    if (instructions != 4 * statements + 2)
        throw new InvalidOperationException($"The CIL no longer matches the multiply-add fixture for {name}.");
    var command = Checked(Path.Combine(output, "Body.lean"), $"""
        import CIL.InstructionEquations

        namespace Body
        open CIL
        {depth.Value}
        {body}
        cil_instruction_equations method0
        #print axioms method0_instruction{last}
        end Body
        """, Binder, "(Body.method0 profile environment)",
        $"Body.method0_instruction{last} profile environment", last);
    var template = Checked(Path.Combine(shared, "Measured.lean"), templates,
        Binder, "(Templates.method0 profile environment)",
        $"Templates.method0_instruction{last} profile environment", last, $$"""
            namespace Handwritten
            open CIL
            {{body}}
            open Lean Meta in
            run_cmd Elab.Command.liftTermElabM do
              forallTelescope (<- getConstInfo ``method0).type fun parameters _ => do
                let code := fun name => mkApp (mkConst ``Method.code) (mkAppN (mkConst name) parameters)
                let (expected, leftClosed) <- InstructionEquations.listElements (code ``method0)
                let (actual, rightClosed) <- InstructionEquations.listElements (code ``Templates.method0)
                unless leftClosed && rightClosed && expected.size == actual.size do
                  throwError "the hand-written and generated templates have different or open lengths"
                for pc in [:expected.size] do
                  unless <- isDefEq expected[pc]! actual[pc]! do
                    throwError "the hand-written and generated instructions differ at pc {pc}"
            end Handwritten
            """);
    return (instructions, [extraction.Count, command.Count, template.Count], EvidenceCosts(extraction.Output));
}

var imports = Path.Combine(directory, "Imports.lean");
var floor = Heartbeats(imports, "import CIL.Extraction.Translation\nimport CIL.SymbolicExecution\n" +
    "import CIL.Safety.Execution\nimport CIL.InstructionEquations\n", equations: false);
var templateChoiceCosts = TemplateChoiceCosts();
if (instructionEquationsOnly)
{
    Concurrently(() => InstructionEquationCosts(), templateChoiceCosts);
    return;
}

// The compile costs of the Short and Long methods, which the evidence check of a body with no call reads too.
(int Instructions, long[] Heartbeats, (long Calls, long Assembly) Evidence)[] InstructionEquationCosts()
{
    var runs = Concurrently(new[] { (Name: "Short", Memory: 0L), (Name: "Long", Memory: MediumLeanProcess) },
        run => ReservingMemory(run.Memory, () => Measure(run.Name)));
    var (brief, extended) = (runs[0], runs[1]);
    if (brief.Instructions < 500 || extended.Instructions < 4 * brief.Instructions - 8)
        throw new InvalidOperationException(
            $"Expected about 500 and 2,000 instructions; found {brief.Instructions} and {extended.Instructions}.");
    Console.WriteLine($"PASS {extended.Instructions} instructions compile at the emitted recursion depth");
    string[] producers = ["an extracted method", "a cil_instruction_equations body", "a generated template"];
    for (var producer = 0; producer < producers.Length; producer++)
    {
        double Cost((int Instructions, long[] Heartbeats, (long, long) Evidence) run) =>
            (double)(run.Heartbeats[producer] - floor) / run.Instructions;
        var growth = Cost(extended) / Cost(brief);
        var measured = string.Create(CultureInfo.InvariantCulture,
            $"{Cost(brief):F0} heartbeats per instruction at {brief.Instructions} instructions and " +
            $"{Cost(extended):F0} at {extended.Instructions}, {growth:F2} times as many");
        if (growth > AllowedGrowth)
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"Compiling {producers[producer]} costs {measured}; the limit is {AllowedGrowth}."));
        Console.WriteLine($"PASS compiling {producers[producer]} costs {measured}");
    }
    return runs;
}

// Each body has eight feature branches. Vary the number of distinct getters and inputs independently.
// Builds the fixture before returning the measurement, so no dotnet build runs beside a concurrent check.
Action TemplateChoiceCosts()
{
    var root = Path.Combine(directory, "TemplateChoices");
    var project = Path.Combine(root, "Assembly");
    Directory.CreateDirectory(project);
    File.Copy(Path.Combine(source, "Lookups.csproj"), Path.Combine(project, "Flags.csproj"), overwrite: true);
    string[] getters = ["Avx512F.IsSupported", "Aes.IsSupported", "Vector256.IsHardwareAccelerated",
        "Avx.IsSupported", "Sse2.IsSupported", "Ssse3.IsSupported", "Avx2.IsSupported", "Bmi2.X64.IsSupported"];
    int[] sizes = [2, 4, 8];
    string MethodWithFlags(int flags)
    {
        var branches = Enumerable.Range(0, getters.Length)
            .Select(i => $"if ({getters[i % flags]}) total += {i + 1};");
        return $$"""
            public static int Read{{flags}}(int word) { int total = word; {{string.Join(' ', branches)}} return total; }
            """;
    }
    File.WriteAllText(Path.Combine(project, "Flags.cs"), $$"""
        using System.Runtime.Intrinsics;
        using System.Runtime.Intrinsics.X86;
        public static class Flags { {{string.Join('\n', sizes.Select(MethodWithFlags))}} }
        """);
    Run(["dotnet", "build", Path.Combine(project, "Flags.csproj"), "-c", "Release"]);
    var image = Path.Combine(project, "bin/Flags.dll");
    int[] masks = [0, 7, 2, 5, 1, 6, 3, 4];
    foreach (var mask in masks.Append(15))
    {
        var wide = (mask & 1) != 0;
        var profile = new { name = $"choice{mask}", architecture = "x64", nativeWidth = 64, littleEndian = true,
            sse2 = true, ssse3 = true, sse41 = true, sse42 = true, avx = true, avx2 = true, x86Base64 = true,
            vector128Accelerated = true, vector256Accelerated = (mask & 4) != 0, bmi1 = true, bmi2 = true,
            avx512F = wide, avx512FVL = wide, avx512DQ = wide, avx512DQVL = wide, avx512Vbmi = (mask & 8) != 0,
            aes = (mask & 2) != 0, armAes = false, advSimd = false, armBase64 = false };
        var json = System.Text.Json.JsonSerializer.Serialize(profile);
        File.WriteAllText(Path.Combine(root, $"profile{mask}.json"), json);
    }
    return () =>
    {
        var cases = new List<(bool VaryInputs, int Size, int Flags, List<string> Paths)>();
        var extractions = new Dictionary<string, GeneratedExtraction>(StringComparer.Ordinal);
        foreach (var varyInputs in new[] { true, false })
            foreach (var size in sizes)
            {
                var flags = varyInputs ? 4 : size;
                // Two pairs of profiles agree on all observed getters as the number of distinct getters grows.
                string[] profiles = varyInputs ? [.. masks.Take(size).Select(mask => $"profile{mask}")] :
                    ["scalar", "arm64-advsimd", "profile7", "profile15"];
                var paths = new List<string>();
                foreach (var profile in profiles)
                {
                    var path = Path.Combine(root, $"Read{flags}-{profile}");
                    var specification = profile.StartsWith("profile", StringComparison.Ordinal)
                        ? $"@{Path.Combine(root, $"{profile}.json")}" : profile;
                    extractions.TryAdd(path, new(image, $"Flags::Read{flags}(int)", path, specification));
                    paths.Add(path);
                }
                cases.Add((varyInputs, size, flags, paths));
            }
        ExtractBatch("extract", "Flags", extractions.Values);
        var measured = Concurrently(cases, test =>
        {
            var (varyInputs, size, flags, paths) = test;
            var shared = Path.Combine(root, varyInputs ? $"Inputs{size}" : $"Flags{size}");
            Run(["dotnet", ExtractorPath, "templates", shared, .. paths]);
            var module = File.ReadAllText(Path.Combine(shared, "Templates.lean")).ReplaceLineEndings("\n");
            var start = module.IndexOf("/-- The stable managed identity", StringComparison.Ordinal);
            var last = module.LastIndexOf("#print axioms method0_instruction", StringComparison.Ordinal);
            using var manifest = System.Text.Json.JsonDocument.Parse(File.ReadAllText(Path.Combine(shared,
                "templates.json")));
            var features = manifest.RootElement.GetProperty("methods")[0].GetProperty("flags").EnumerateArray()
                .Select(flag => flag.GetString()!)
                .Select(flag => $"{char.ToUpperInvariant(flag[0])}{flag[1..]}").ToArray();
            var bindings = manifest.RootElement.GetProperty("profiles");
            int ObservedFlags(System.Text.Json.JsonElement binding)
            {
                var profile = binding.GetProperty("profile");
                return features.Aggregate(0, (bits, flag) =>
                    2 * bits + (profile.GetProperty(flag).GetBoolean() ? 1 : 0));
            }
            var leaves = bindings.EnumerateArray().Select(ObservedFlags).Distinct().Count();
            if (features.Length != flags || bindings.GetArrayLength() != paths.Count ||
                leaves != (varyInputs ? size : 2) || start < 0 || last < 0)
                throw new InvalidOperationException(
                    $"Unexpected dimensions at {paths.Count} inputs, {flags} flags.");
            var number = module[(last + "#print axioms method0_instruction".Length)..].Split('\n')[0];
            var count = int.Parse(number, CultureInfo.InvariantCulture) + 1;
            var header = module.IndexOf("/-!", StringComparison.Ordinal);
            var parts = new[] { module[..header], module[header..start], module[start..] };
            var costs = PartHeartbeats(Path.Combine(shared, "Costs.lean"), parts);
            Console.WriteLine($"""
                Template {Path.GetFileName(shared)}, {paths.Count} inputs, {flags} flags, {count} pcs:
                  {costs.Sum()} total heartbeats, {costs[1]} for selection, leaf proofs and equations
                """);
            return (test.VaryInputs, test.Size, Instructions: count, Total: costs.Sum(), Selection: costs[1]);
        });
        var pcs = measured[0].Instructions;
        if (measured.Any(row => row.Instructions != pcs))
            throw new InvalidOperationException("Template instruction counts differ.");
        var samples = measured.ToDictionary(row => (row.VaryInputs, row.Size));
        foreach (var varyInputs in new[] { true, false })
            foreach (var selectionOnly in new[] { true, false })
            {
                double PerUnit(int size)
                {
                    var cost = samples[(varyInputs, size)];
                    return (double)(selectionOnly ? cost.Selection : cost.Total) / (size * pcs);
                }
                foreach (var (smaller, larger) in sizes.Zip(sizes.Skip(1)))
                    if (PerUnit(larger) > AllowedGrowth * PerUnit(smaller))
                        throw new InvalidOperationException($"""
                            Template cost from {smaller} to {larger} exceeds {AllowedGrowth} per unit per pc.
                            Inputs varying: {varyInputs}. Selection only: {selectionOnly}.
                            Measured {PerUnit(smaller):F0} and {PerUnit(larger):F0} heartbeats.
                            """);
            }
    };
}

// A body with no call at three lengths. Its call check reads every pc's link by one walk, so it costs the same per
// instruction; its evidence theorem is assembled from the conjuncts' theorems and costs the same at every length.
// A conjunct stated through another term than `MethodEvidenceValid` states makes the assembly reduce the whole body.
void NoCallEvidenceCosts(
    IReadOnlyList<(int Instructions, long[] Heartbeats, (long Calls, long Assembly) Evidence)> runs)
{
    var (brief, extended) = (runs[0], runs[1]);
    var middleOutput = Path.Combine(directory, "Middle");
    Run(Extract("extract", assembly, "Lookups", "Lookups::Middle(ulong,ulong)", middleOutput));
    var middle = EvidenceCosts(Reported(Path.Combine(middleOutput, "Measured.lean"),
        WithEvidenceCosts(File.ReadAllText(Path.Combine(middleOutput, "Extracted.lean"))), equations: false).Output);
    (int Statements, long Calls, long Assembly)[] evidenceSamples = [
        (ShortStatements, brief.Evidence.Calls, brief.Evidence.Assembly),
        (MiddleStatements, middle.Calls, middle.Assembly),
        (LongStatements, extended.Evidence.Calls, extended.Evidence.Assembly)];
    var evidenceMeasured = string.Join("; ", evidenceSamples.Select(sample => string.Create(
        CultureInfo.InvariantCulture,
        $"{sample.Statements} statements = {(double)sample.Calls / sample.Statements:F0} per statement for the call " +
        $"check and {sample.Assembly} for the evidence theorem")));
    if (evidenceSamples.Any(sample => sample.Calls < KernelDecisionFloor || sample.Assembly < KernelDecisionFloor) ||
        evidenceSamples.Skip(1).Zip(evidenceSamples).Any(pair =>
            (double)pair.First.Calls / pair.First.Statements >
                (double)pair.Second.Calls / pair.Second.Statements * AllowedGrowth ||
            pair.First.Assembly > pair.Second.Assembly * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking the evidence of a body with no call costs {evidenceMeasured} heartbeats; the limit is " +
            $"{AllowedGrowth} times the cost per statement of the call check and the cost of the evidence theorem at " +
            $"the length before."));
    Console.WriteLine($"PASS checking the evidence of a body with no call costs {evidenceMeasured} heartbeats");
}

// The extraction of a body with many calls: its link table, key check, per-site facts and the checks that
// tie them together must each cost the same per call site at four times the size.
long CallingCost(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    return Heartbeats(Path.Combine(output, "Measured.lean"), File.ReadAllText(Path.Combine(output, "Extracted.lean")),
        equations: false);
}
void CallingCosts()
{
    var fewCost = (double)(CallingCost("Few") - floor) / FewCalls;
    var manyCost = (double)(CallingCost("Many") - floor) / ManyCalls;
    var callGrowth = manyCost / fewCost;
    var callsMeasured = string.Create(CultureInfo.InvariantCulture,
        $"{fewCost:F0} heartbeats per call at {FewCalls} calls and {manyCost:F0} at {ManyCalls}, " +
        $"{callGrowth:F2} times as many");
    if (callGrowth > AllowedCallGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Extracting a body with many calls costs {callsMeasured}; the limit is {AllowedCallGrowth}."));
    Console.WriteLine($"PASS extracting a body with many calls costs {callsMeasured}");
}

// The kernel heartbeats to recheck the proof that `written` embeds into `extraction`, both defined by
// `definitions`. The two link tables differ and their call sites sit at different pcs, so the kernel cannot close
// the link clause by comparing equal arguments: it must read both tables, and a read that scans the table per
// call grows with the call count. `cil_embed` states the proof as an auxiliary lemma, so that lemma is rechecked.
long EmbeddingCost(string name, string definitions)
{
    var path = Path.Combine(directory, name + ".lean");
    File.WriteAllText(path, $$"""
        import CIL.Embedding.Tactic
        set_option maxHeartbeats 0
        set_option maxRecDepth 100000
        open CIL
        namespace Embedded
        {{definitions}}
        theorem embeds : MethodEmbeds [extraction] 0 written := by cil_embed
        end Embedded
        open Lean in
        run_cmd do
          let env ← getEnv
          let some (.thmInfo declaration) := env.find? `Embedded.embeds | throwError "missing"
          let start ← IO.getNumHeartbeats
          let mut count : Nat := 0
          for name in declaration.value.getUsedConstants do
            let some (.thmInfo used) := env.find? name | continue
            let copy : Declaration := .thmDecl { used with name := name ++ `recheck }
            match env.toKernelEnv.addDeclCore 0 1000000 copy none with
            | .ok _ => count := count + 1
            | .error _ => throwError "Kernel rejected the recheck of {name}"
          let beats := (← IO.getNumHeartbeats) - start
          logInfo m!"{count} lemmas rechecked, {beats} kernel heartbeats"
        """ + "\n");
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var cost = LookupPatterns.EmbeddingRecheck.Match(output);
    if (!cost.Success || cost.Groups[1].Value == "0")
        throw new InvalidOperationException("Missing the embedding recheck cost:\n" + output);
    return long.Parse(cost.Groups[2].Value, CultureInfo.InvariantCulture);
}

// The method every embedded call names; the link at its pc chooses the body it enters.
const string EmbeddedCallees = """
/-- A one-argument method whose result each segment pops. -/
def callee : Extraction.MethodRef :=
  { owner := .atom "Tests" "Embedded" .classType, name := name!"Callee", hasThis := false, genericArity := 0,
    returnType := .atom "Tests" "Word" .valueType, parameters := [.atom "Tests" "Word" .valueType] }
""";

// A hand-written body embedded into an extraction with a dead block after each return.
string DeadBlocks(int calls) => $$"""
{{EmbeddedCallees}}
/-- What an extraction emits for one call followed by a dead block. -/
def extractedSegment : List Instruction :=
  [.ldarg 0, .call callee, .pop, .ret, .unadmitted 0]
/-- The hand-written segment without the dead block. -/
def writtenSegment : List Instruction := [.ldarg 0, .call callee, .pop, .ret]
/-- The extraction, whose calls sit at pcs 1, 6, 11 and so on, each linked to method 1. -/
def extraction : Method :=
  { locals := [], returnsValue := false,
    code := (List.replicate {{calls}} extractedSegment).flatten ++ [.ret],
    links := (List.range {{calls}}).map fun index => (5 * index + 1, .direct 1) }
/-- The proof's body, with calls at pcs 1, 5, 9 and so on, each linked to method 1. -/
def written : Method :=
  { extraction.withCode ((List.replicate {{calls}} writtenSegment).flatten ++ [.ret]) with
    links := (List.range {{calls}}).map fun index => (4 * index + 1, .direct 1) }
""";

// A body whose head branches over its first block to its second, embedded into an extraction that places the
// second block first, so the pc map descends once at every size.
string Reordered(int segments) => $$"""
{{EmbeddedCallees}}
/-- The block after the head, whose call is linked to method 1. -/
def first : List Instruction := [.ldarg 0, .call callee, .pop, .ret]
/-- The block the head branches to, whose call is linked to method 2. -/
def second : List Instruction := [.ldarg 1, .call callee, .pop, .ret]
/-- The links of `count` copies of a block starting at `start`, each call linked to `target`. -/
def blockLinks (start count target : Nat) : List (Nat × Link) :=
  (List.range count).map fun index => (start + 4 * index + 1, .direct target)
/-- The extraction, with the second block first. -/
def extraction : Method :=
  { locals := [], returnsValue := false,
    code := [.br 1] ++ (List.replicate {{segments}} second).flatten ++
      (List.replicate {{segments}} first).flatten ++ [.ret],
    links := blockLinks 1 {{segments}} 2 ++ blockLinks {{1 + 4 * segments}} {{segments}} 1 }
/-- The proof's body, with the blocks in source order. -/
def written : Method :=
  { extraction.withCode ([.br {{1 + 4 * segments}}] ++ (List.replicate {{segments}} first).flatten ++
      (List.replicate {{segments}} second).flatten ++ [.ret]) with
    links := blockLinks 1 {{segments}} 1 ++ blockLinks {{1 + 4 * segments}} {{segments}} 2 }
#guard let map := (MethodBinding.alignLive written.code.toArray extraction.code.toArray).toList
  (map.zip map.tail).countP (fun (left, right) => right < left) == 1
""";

// Fails when a fixture at the larger size costs more per call to embed than the allowed growth.
void CheckEmbeddingGrowth(string fixture, string description, Func<int, string> definitions, int callsPerSize,
    int few, int many)
{
    double Cost(int size) => (double)EmbeddingCost(fixture + size, definitions(size)) / (callsPerSize * size);
    var fewCost = Cost(few);
    var manyCost = Cost(many);
    var growth = manyCost / fewCost;
    var measured = string.Create(CultureInfo.InvariantCulture,
        $"{fewCost:F0} kernel heartbeats per call at {callsPerSize * few} calls and {manyCost:F0} at " +
        $"{callsPerSize * many}, {growth:F2} times as many");
    if (growth > AllowedEmbedGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Embedding {description} costs {measured}; the limit is {AllowedEmbedGrowth}."));
    Console.WriteLine($"PASS embedding {description} costs {measured}");
}
void EmbeddingCosts() => Concurrently(
    () => CheckEmbeddingGrowth("Embedding", "a body with many calls", DeadBlocks, 1, EmbedFewCalls, EmbedManyCalls),
    () => CheckEmbeddingGrowth("Reordered", "a body whose blocks the extraction reorders", Reordered, 2,
        ReorderFewSegments, ReorderManySegments));

// The text a method emits for its links and the kernel heartbeats to recheck that its table keys ascend, for a body
// with two calls: both depend on the calls, not on the length of the body.
(long Bytes, long Heartbeats) SparseLinkCost(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var linkLines = extracted.Split('\n').Where(line => LookupPatterns.LinkLine.IsMatch(line))
        .Sum(line => (long)line.Length + 1);
    if (linkLines == 0) throw new InvalidOperationException("The extraction of " + name + " has no link output.");
    var path = Path.Combine(output, "LinkAscend.lean");
    File.WriteAllText(path, extracted + """

        open Lean in
        run_cmd do
          let env ← getEnv
          let some (.thmInfo declaration) := env.find? `Extracted.method0_links_ascend
            | throwError "missing the link key check"
          let start ← IO.getNumHeartbeats
          let copy : Declaration := .thmDecl { declaration with name := declaration.name ++ `recheck }
          match env.toKernelEnv.addDeclCore 0 1000000 copy none with
          | .ok _ => pure ()
          | .error _ => throwError "Kernel rejected the link key check"
          logInfo m!"{(← IO.getNumHeartbeats) - start} kernel heartbeats"
        """ + "\n");
    var report = Run(["lake", "env", "lean", path], cwd: FixturePackage());
    var beats = LookupPatterns.KernelHeartbeats.Match(report);
    if (!beats.Success) throw new InvalidOperationException("Missing the link key recheck cost:\n" + report);
    return (linkLines, long.Parse(beats.Groups[1].Value, CultureInfo.InvariantCulture));
}
void SparseLinkCosts()
{
    var sparse = Concurrently(
        new[] { (Name: "SparseLong", Memory: LargeLeanProcess), (Name: "SparseShort", Memory: 0L) },
        run => ReservingMemory(run.Memory, () => SparseLinkCost(run.Name)));
    var (sparseLong, sparseShort) = (sparse[0], sparse[1]);
    var sparseMeasured = $"{sparseShort.Bytes} link bytes and {sparseShort.Heartbeats} kernel heartbeats at " +
        $"{SparseShortStatements} statements, {sparseLong.Bytes} and {sparseLong.Heartbeats} at {SparseLongStatements}";
    if (sparseLong.Bytes > sparseShort.Bytes * 1.1 ||
        sparseLong.Heartbeats > sparseShort.Heartbeats * AllowedCallGrowth)
        throw new InvalidOperationException(
            "A longer body with the same calls emits more link output: " + sparseMeasured);
    Console.WriteLine("PASS link output and key check of a body with two calls do not grow with the body: " +
        sparseMeasured);
}

// Subtract the same generated body's cost to isolate computed lookup from equation generation.
long ComputedLookupCost(int cases)
{
    var header = $$"""
        import CIL.InstructionEquations
        import CIL.Safety.SymbolicExecution
        open CIL.Safety
        def segment : List CIL.Instruction := [.ldarg 0, .ldarg 1, .add, .nop, .nop, .nop, .nop]
        def body : CIL.Method :=
          { locals := [], returnsValue := true,
            code := [.nop] ++ (List.replicate {{cases}} segment).flatten ++ [.ret] }
        cil_instruction_equations body
        """ + "\n";
    var path = Path.Combine(directory, "Computed" + cases + ".lean");
    return PartHeartbeats(path, [header, $$"""
        /-- Each repeated segment has its addition at the same relative offset. -/
        theorem fetched (index : Fin {{cases}}) : body.code[1 + 7 * index.val + 2]? = some .add := by
          cil_lookup []
        #print axioms fetched
        """ + "\n"])[0];
}
void ComputedLookupCosts()
{
    var fourCaseCost = ComputedLookupCost(4) / 4.0;
    var sixteenCaseCost = ComputedLookupCost(16) / 16.0;
    Console.WriteLine(FormattableString.Invariant(
        $"PASS computed lookup: {fourCaseCost:F0} heartbeats/case at 4; {sixteenCaseCost:F0} at 16"));
    if (sixteenCaseCost > fourCaseCost * AllowedGrowth)
        throw new Exception("Computed lookup cost per case grows with the segment count.");
}

// Each distinct metadata token of a body adds a row lookup and a decode to the kernel's metadata check, so the cost
// per token may not grow with the number of tokens, whichever table the token names: user strings, instance fields
// of a class, and methods (whose count also grows the number of methods of the extraction and so the metadata
// carried).
const int FewTokens = 125;
const int ManyTokens = 500;
// Each called method is an extracted method with a certificate of its own, and composing the certificate of an
// extraction of about 500 methods exceeds the default heartbeat budget, so the call counts stay below that.
const int FewCalledMethods = 25;
const int ManyCalledMethods = 100;
var tokenSource = Path.Combine(directory, "TokenAssembly");
Directory.CreateDirectory(tokenSource);
File.WriteAllText(Path.Combine(tokenSource, "Tokens.csproj"), """
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize></PropertyGroup>
</Project>
""");
string Join(int count, Func<int, string> piece) => string.Concat(Enumerable.Range(0, count).Select(piece));
string StringMethod(int count, string name) =>
    $"public static ulong {name}(ulong x) {{ " + Join(count, index => $"Use(\"{name}{index}\"); ") + "return x; } ";
string FieldMethod(int count, string name) =>
    $"public static ulong {name}(Wide{count} w) {{ return 0UL" + Join(count, index => $" + w.F{index}") + "; } " +
    $"public sealed class Wide{count} {{ " + Join(count, index => $"public ulong F{index}; ") + "} ";
string CallMethod(int count, string name) =>
    $"public static ulong {name}(ulong x) {{ " + Join(count, index => $"x = {name}{index}(x); ") + "return x; } " +
    Join(count, index => $"static ulong {name}{index}(ulong x) => x + {index + 1}UL; ");
File.WriteAllText(Path.Combine(tokenSource, "Tokens.cs"),
    "public static class Tokens { public static void Use(string text) { } " +
    StringMethod(FewTokens, "StringsFew") + StringMethod(ManyTokens, "StringsMany") +
    FieldMethod(FewTokens, "FieldsFew") + FieldMethod(ManyTokens, "FieldsMany") +
    CallMethod(FewCalledMethods, "CallsFew") + CallMethod(ManyCalledMethods, "CallsMany") + "}");
Run(["dotnet", "build", Path.Combine(tokenSource, "Tokens.csproj"), "-c", "Release"]);
var tokenAssembly = Path.Combine(tokenSource, "bin/Tokens.dll");
// The heartbeats per token of the whole extraction, less the imports, and of its call check alone. A call check that
// reads each pc's link by a scan of the link table grows with the tokens that each carry a link.
(double Total, double Calls) TokenCost(string name, string selector, int count, Regex distinctToken)
{
    var output = Path.Combine(directory, "Tokens" + name);
    Run(Extract("extract", tokenAssembly, "Tokens", selector, output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var distinct = distinctToken.Count(extracted);
    if (distinct < count)
        throw new InvalidOperationException($"Expected {count} distinct tokens in {name}; found {distinct}.");
    var report = Reported(Path.Combine(output, "Measured.lean"), WithEvidenceCosts(extracted), equations: false);
    return ((double)(report.Count - floor) / count, (double)EvidenceCosts(report.Output).Calls / count);
}
void TokenCosts() => Concurrently(new[]
{
    ("Strings", "Tokens::StringsFew(ulong)", "Tokens::StringsMany(ulong)",
        LookupPatterns.StringToken, FewTokens, ManyTokens),
    ("Fields", $"Tokens::FieldsFew(Tokens/Wide{FewTokens})", $"Tokens::FieldsMany(Tokens/Wide{ManyTokens})",
        LookupPatterns.FieldToken, FewTokens, ManyTokens),
    ("Calls", "Tokens::CallsFew(ulong)", "Tokens::CallsMany(ulong)", LookupPatterns.CallToken, FewCalledMethods,
        ManyCalledMethods)
}, row =>
{
    var (kind, few, many, pattern, fewCount, manyCount) = row;
    var costs = Concurrently(new[] { (Name: kind + "Many", Selector: many, Count: manyCount),
        (Name: kind + "Few", Selector: few, Count: fewCount) },
        run => ReservingMemory(run.Name.EndsWith("Many", StringComparison.Ordinal) ? MediumLeanProcess : 0,
            () => TokenCost(run.Name, run.Selector, run.Count, pattern)));
    var (manyTokens, fewTokens) = (costs[0], costs[1]);
    var tokenGrowth = manyTokens.Total / fewTokens.Total;
    var callCheckGrowth = manyTokens.Calls / fewTokens.Calls;
    var tokensMeasured = string.Create(CultureInfo.InvariantCulture,
        $"{tokenGrowth:F2} times as much per token as {fewCount}, and {callCheckGrowth:F2} times for the call check");
    if (tokenGrowth > AllowedGrowth || callCheckGrowth > AllowedGrowth)
        throw new Exception(string.Create(CultureInfo.InvariantCulture,
            $"Checking {manyCount} {kind.ToLowerInvariant()} tokens costs {tokensMeasured}; the limit is " +
            $"{AllowedGrowth}."));
    Console.WriteLine(
        $"PASS metadata check of {manyCount} distinct {kind.ToLowerInvariant()} tokens costs {tokensMeasured}");
});

// One method's body check reads the literal lookup tables of its own metadata slice by name, so its kernel cost is its
// own slice and tokens times a logarithm: independent of the number of methods in the extraction and of the rows
// that other methods carry.
const double AllowedBodyGrowth = 1.1;
int[] chainLengths = [8, 32, 128];
int[] bulkSizes = [125, 500];
int[] fieldCounts = [10, 100, 200];
int[] stringTokenCounts = [125, 500, 1000];
var bodySource = Path.Combine(directory, "BodyAssembly");
Directory.CreateDirectory(bodySource);
File.WriteAllText(Path.Combine(bodySource, "Bodies.csproj"),
    File.ReadAllText(Path.Combine(tokenSource, "Tokens.csproj")));
string Chain(int count) =>
    $"public static ulong Chain{count}(ulong x) {{ " +
    Join(count, index => $"x = Chain{count}_{index}(x); ") + "return x; } " +
    Join(count, index => $"static ulong Chain{count}_{index}(ulong x) => x + {index + 1}UL; ");
string Rows(int count) =>
    $"public static ulong Rows{count}(ulong x) {{ x = Small{count}(x); return Bulk{count}(x); }} " +
    $"static ulong Small{count}(ulong x) => x + 1UL; " +
    $"static ulong Bulk{count}(ulong x) {{ " + Join(count, index => $"Use(\"r{count}_{index}\"); ") + "return x; } ";
// A method that reads one field of a class with `count` fields carries that class's field rows.
string Fields(int count) =>
    $"public sealed class Wide{count} {{ " + Join(count, index => $"public ulong F{index}; ") + "} " +
    $"public static ulong Read{count}(Wide{count} w) => w.F{count / 2}; ";
// A method of `count` string tokens has `2 * count + 2` instructions.
string Strings(int count) =>
    $"public static ulong Strings{count}(ulong x) {{ " + Join(count, index => $"Use(\"s{count}_{index}\"); ") +
    "return x; } ";
File.WriteAllText(Path.Combine(bodySource, "Bodies.cs"),
    "public static class Bodies { public static void Use(string text) { } " +
    string.Concat(chainLengths.Select(Chain)) + string.Concat(bulkSizes.Select(Rows)) +
    string.Concat(fieldCounts.Select(Fields)) + string.Concat(stringTokenCounts.Select(Strings)) + "}");
Run(["dotnet", "build", Path.Combine(bodySource, "Bodies.csproj"), "-c", "Release"]);
var bodyAssembly = Path.Combine(bodySource, "bin/Bodies.dll");
// The index of a method in an extraction, found by the name in its signature.
string MethodNumber(string extracted, string method, string name)
{
    return LookupPatterns.BodySignature.Matches(extracted)
        .FirstOrDefault(match => match.Groups["method"].Value == method)?.Groups[1].Value
        ?? throw new InvalidOperationException($"Method {method} is not in the extraction {name}.");
}
// Measure the body proof net of its statement, and the full cost of materializing and certifying the lookup trees.
(long Body, long Tables) BodyChecks(string image, string name, string entry, string method,
    string? tablesMethod = null, int? receiverBases = null)
{
    var output = Path.Combine(directory, "Body" + name);
    Run(Extract("extract", image, "Bodies", entry.Contains('(') ? entry : $"Bodies::{entry}(ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var prefix = "method" + MethodNumber(extracted, method, name);
    var body = prefix + "_body_validated";
    var narrowed = NarrowEvidence(extracted, body);
    var bodyProof = LookupPatterns.BodyObligation.Matches(narrowed).Single(match => match.Groups["name"].Value == body);
    var commands = new List<(Match Command, string Audit)> { (bodyProof, body) };
    if (tablesMethod is not null)
    {
        var tableMethod = "method" + MethodNumber(extracted, tablesMethod, name);
        var tableDefinition = LookupPatterns.EvaluatedTables.Matches(narrowed)
            .Single(match => match.Groups["method"].Value == tableMethod);
        var tableProof = LookupPatterns.TablesObligation.Matches(narrowed)
            .Single(match => match.Groups["method"].Value == tableMethod);
        commands.Add((tableDefinition, tableMethod + "Tables_eq"));
        commands.Add((tableProof, tableMethod + "_tables_valid"));
    }
    var parts = new List<string>();
    int openAt = 0, bodyAt = 0;
    var tablesAt = new List<int>();
    var start = 0;
    foreach (var (command, audit) in commands.OrderBy(entry => entry.Command.Index))
    {
        parts.Add(narrowed[start..command.Index]);
        // PartHeartbeats excludes the header from its result.
        if (audit == body)
        {
            openAt = parts.Count - 1;
            parts.Add($"theorem {body}_open : {command.Groups["statement"].Value} := sorry\n");
            bodyAt = parts.Count - 1;
        }
        else tablesAt.Add(parts.Count - 1);
        parts.Add(command.Value);
        start = command.Index + command.Length;
    }
    var baseCount = receiverBases is { } count
        ? $"#guard {prefix}Original.objectBases.length == {count}\n#guard {prefix}Names.bases.length == {count}\n"
        : "";
    parts.Add(string.Join('\n', commands.Select(entry => $"#print axioms {entry.Audit}")) + "\n" +
        baseCount + "end Extracted\n");
    var costs = PartHeartbeats(Path.Combine(output, "BodyChecked.lean"), parts);
    return (costs[bodyAt] - costs[openAt], tablesAt.Sum(index => costs[index]));
}
long BodyCheck(string image, string name, string entry, string method) =>
    BodyChecks(image, name, entry, method).Body;
void BodyCheckCosts()
{
    double[] chainCosts = [], stringCosts = [];
    (long Body, long Tables)[] rowChecks = [], fieldChecks = [];
    // Every body is measured at once, before any check below reads the costs.
    Concurrently(
        () => stringCosts = Concurrently(stringTokenCounts, count => ReservingMemory(
            count == stringTokenCounts[^1] ? LargeLeanProcess : count == stringTokenCounts[^2] ? MediumLeanProcess : 0,
            () => BodyCheck(bodyAssembly, "Strings" + count, "Strings" + count, "Strings" + count)) /
            (2.0 * count + 2)),
        () => rowChecks = Concurrently(bulkSizes, count =>
            BodyChecks(bodyAssembly, "Rows" + count, "Rows" + count, $"Small{count}", $"Bulk{count}")),
        () => chainCosts = Concurrently(chainLengths, count =>
            (double)BodyCheck(bodyAssembly, "Chain" + count, "Chain" + count, $"Chain{count}_{count - 1}")),
        () => fieldChecks = Concurrently(fieldCounts, count => BodyChecks(bodyAssembly, "Fields" + count,
            $"Bodies::Read{count}(Bodies/Wide{count})", $"Read{count}", $"Read{count}")));
    var rowCosts = rowChecks.Select(check => (double)check.Body).ToArray();
    for (var step = 1; step < chainCosts.Length; step++)
    {
        var growth = chainCosts[step] / chainCosts[step - 1];
        Console.WriteLine(FormattableString.Invariant(
            $"PASS body check of one method in {chainLengths[step - 1]} and {chainLengths[step]} methods: ") +
            FormattableString.Invariant($"{chainCosts[step - 1]:F0} and {chainCosts[step]:F0} heartbeats, ") +
            FormattableString.Invariant($"{growth:F2} times"));
        if (growth > AllowedBodyGrowth)
            throw new Exception(FormattableString.Invariant(
                $"One body check costs {growth:F2} times as much at {chainLengths[step]} methods ") +
                FormattableString.Invariant($"as at {chainLengths[step - 1]}; the limit is {AllowedBodyGrowth}."));
    }
    var rowGrowth = rowCosts[1] / rowCosts[0];
    Console.WriteLine(FormattableString.Invariant(
        $"PASS body check of one method against {bulkSizes[0]} and {bulkSizes[1]} metadata rows: ") +
        FormattableString.Invariant($"{rowGrowth:F2} times"));
    if (rowGrowth > AllowedBodyGrowth)
        throw new Exception(FormattableString.Invariant(
            $"One body check costs {rowGrowth:F2} times as much against {bulkSizes[1]} rows ") +
            FormattableString.Invariant($"as against {bulkSizes[0]}; the limit is {AllowedBodyGrowth}."));
    // The body check of a method of many string tokens costs the same per instruction at every size: numerals of its
    // byte literal with equal low bytes would collide in the kernel's caches unless the literal is one joined code.
    for (var step = 1; step < stringCosts.Length; step++)
    {
        var growth = stringCosts[step] / stringCosts[step - 1];
        Console.WriteLine(FormattableString.Invariant(
            $"PASS body check of a method of {stringTokenCounts[step - 1]} and {stringTokenCounts[step]} ") +
            FormattableString.Invariant($"string tokens: {stringCosts[step - 1]:F0} and {stringCosts[step]:F0} ") +
            FormattableString.Invariant($"heartbeats per instruction, {growth:F2} times"));
        if (growth > AllowedBodyGrowth)
            throw new Exception(FormattableString.Invariant(
                $"One body check costs {growth:F2} times as much per instruction at ") +
                FormattableString.Invariant($"{stringTokenCounts[step]} string ") +
                FormattableString.Invariant(
                    $"tokens as at {stringTokenCounts[step - 1]}; the limit is {AllowedBodyGrowth}."));
    }
    // The kernel's decision that a method's literal tables are the decoder's costs the rows that method carries,
    // times a logarithm, and is made once per method.
    var tablesFew = rowChecks[0].Tables;
    var tablesMany = rowChecks[1].Tables;
    var tablesGrowth = tablesMany / (double)tablesFew;
    Console.WriteLine(FormattableString.Invariant(
        $"PASS tables check of a method carrying {bulkSizes[0]} and {bulkSizes[1]} user string rows: ") +
        FormattableString.Invariant($"{tablesFew} and {tablesMany} heartbeats, ") +
        FormattableString.Invariant(
            $"{tablesGrowth / (bulkSizes[1] / (double)bulkSizes[0]):F2} times the cost per row"));
    if (tablesGrowth > AllowedBodyGrowth * bulkSizes[1] / bulkSizes[0])
        throw new Exception(FormattableString.Invariant(
            $"The tables check costs {tablesGrowth:F2} times as much for {bulkSizes[1]} rows ") +
            FormattableString.Invariant($"as for {bulkSizes[0]}."));

    // A method reading one field of a class with 10, 100 and 200 fields carries those field rows. Its body check does
    // one lookup of the field's index, so it stays flat. Its tables check is a fixed part plus a part linear in the
    // rows carried: the increment from 100 to 200 fields is 100/90 of the increment from 10 to 100, and a quadratic
    // walk of the rows makes it more than three times as large.
    const double AllowedFieldIncrementRatio = 1.5;
    var fieldBody = fieldChecks.Select(check => (double)check.Body).ToArray();
    var fieldTables = fieldChecks.Select(check => (double)check.Tables).ToArray();
    var fieldBodyGrowth = fieldBody[^1] / fieldBody[0];
    Console.WriteLine(FormattableString.Invariant(
        $"PASS body check of a method reading one of {fieldCounts[0]}, {fieldCounts[1]} and ") +
        FormattableString.Invariant($"{fieldCounts[2]} fields: ") +
        FormattableString.Invariant($"{fieldBody[0]:F0}, {fieldBody[1]:F0} and {fieldBody[2]:F0} heartbeats, ") +
        FormattableString.Invariant($"{fieldBodyGrowth:F2} times"));
    if (fieldBodyGrowth > AllowedBodyGrowth)
        throw new Exception(FormattableString.Invariant(
            $"The body check costs {fieldBodyGrowth:F2} times as much with {fieldCounts[2]} fields ") +
            FormattableString.Invariant($"as with {fieldCounts[0]}; the limit is {AllowedBodyGrowth}."));
    var fieldIncrementRatio = (fieldTables[2] - fieldTables[1]) / (fieldTables[1] - fieldTables[0]);
    Console.WriteLine(FormattableString.Invariant(
        $"PASS tables check of a method reading one of {fieldCounts[0]}, {fieldCounts[1]} and ") +
        FormattableString.Invariant($"{fieldCounts[2]} fields: ") +
        FormattableString.Invariant($"{fieldTables[0]:F0}, {fieldTables[1]:F0} and {fieldTables[2]:F0} heartbeats, ") +
        FormattableString.Invariant($"increments in the ratio {fieldIncrementRatio:F2}"));
    if (fieldIncrementRatio > AllowedFieldIncrementRatio)
        throw new Exception(FormattableString.Invariant(
            $"The tables check grows by {fieldIncrementRatio:F2} times as much from {fieldCounts[1]} to ") +
            FormattableString.Invariant(
                $"{fieldCounts[2]} fields as from {fieldCounts[0]} to {fieldCounts[1]}; ") +
            FormattableString.Invariant($"the limit is {AllowedFieldIncrementRatio}."));
}

// `spelled?` reads a name's bytes in one pass, and `cil_kernel_rfl` equates the result with the name's literal:
// the cost grows with the length of the name and no faster. Each proof is read after the same statement closed with
// `sorry` in its file, so the statement's own elaboration is not counted.
const double AllowedSpellingGrowth = 1.1;
var spellingLengths = new[] { 20, 80, 320 };
long SpellingCheck(int length)
{
    var name = string.Concat(Enumerable.Range(0, length).Select(index => (char)('a' + index % 26)));
    var bytes = string.Join(", ", name.Select(character => (int)character));
    var statement = $"CIL.Extraction.spelled? [{bytes}] = some \"{name}\"";
    var costs = PartHeartbeats(Path.Combine(directory, $"Spelling{length}.lean"),
        ["import CIL.Extraction.KernelEquation\n", $"theorem spells_open : {statement} := sorry\n",
            $"theorem spells : {statement} := by cil_kernel_rfl\n"]);
    return costs[1] - costs[0];
}
void SpellingCosts()
{
    var spellingCosts = spellingLengths.Select(length => (double)SpellingCheck(length)).ToArray();
    for (var step = 1; step < spellingLengths.Length; step++)
    {
        var lengthRatio = spellingLengths[step] / (double)spellingLengths[step - 1];
        var growth = spellingCosts[step] / spellingCosts[step - 1];
        Console.WriteLine(FormattableString.Invariant(
            $"PASS spelling a name of {spellingLengths[step - 1]} and {spellingLengths[step]} bytes: ") +
            FormattableString.Invariant($"{spellingCosts[step - 1]:F0} and {spellingCosts[step]:F0} heartbeats, ") +
            FormattableString.Invariant($"{growth / lengthRatio:F2} times the cost per byte"));
        if (growth > AllowedSpellingGrowth * lengthRatio)
            throw new Exception(FormattableString.Invariant(
                $"Spelling {spellingLengths[step]} bytes costs {growth:F2} times as much as ") +
                FormattableString.Invariant($"{spellingLengths[step - 1]}; ") +
                FormattableString.Invariant($"the limit is {AllowedSpellingGrowth * lengthRatio:F1}."));
    }
}

// A name stored as its bytes (`byteString`) gives `bytesOf` those bytes without encoding the name, so reading them
// grows with the name's length and no faster, and the name's definition and one read cost less than reading the
// bytes of its literal. Each read is measured after the same statement is stated, so its elaboration is not counted.
const double AllowedStoredGrowth = 1.1;
long[] StoredCosts(int length)
{
    var name = string.Concat(Enumerable.Range(0, length).Select(index => (char)('a' + index % 26)));
    var hex = string.Concat(name.Select(character => ((int)character).ToString("X2", CultureInfo.InvariantCulture)));
    var sum = name.Sum(character => (int)character);
    var literal = $"\"{name}\"";
    string Read(string text) => $"(CIL.Extraction.bytesOf {text}).foldl (fun a b => a + b) 0 = {sum}";
    var costs = PartHeartbeats(Path.Combine(directory, $"Stored{length}.lean"),
        ["import CIL.Extraction.MetadataBytes\n",
            $"def stored : String :=\n  CIL.Extraction.byteString (CIL.Extraction.fixedBytes {length} 0x{hex})\n" +
                $"    \"{name}\" (by cil_kernel_rfl)\n",
            $"example : Prop := {Read("stored")}\n", $"theorem reads_stored : {Read("stored")} := by decide +kernel\n",
            $"example : Prop := {Read(literal)}\n",
            $"theorem reads_literal : {Read(literal)} := by decide +kernel\n"]);
    return [costs[0], costs[2] - costs[1], costs[4] - costs[3]];
}
void StoredNameCosts()
{
    var storedCosts = spellingLengths.Select(StoredCosts).ToArray();
    for (var step = 0; step < spellingLengths.Length; step++)
    {
        var (definition, stored, literal) = (storedCosts[step][0], storedCosts[step][1], storedCosts[step][2]);
        Console.WriteLine(FormattableString.Invariant(
            $"PASS reading the bytes of a stored name of {spellingLengths[step]} bytes: {stored} heartbeats, ") +
            FormattableString.Invariant($"{definition} to define it, {literal} for its literal"));
        if (definition + stored >= literal)
            throw new Exception(FormattableString.Invariant(
                $"Defining and reading a stored name of {spellingLengths[step]} bytes costs {definition + stored} ") +
                FormattableString.Invariant($"heartbeats, not below the {literal} of reading its literal."));
        if (step == 0) continue;
        var lengthRatio = spellingLengths[step] / (double)spellingLengths[step - 1];
        var growth = stored / (double)storedCosts[step - 1][1];
        if (growth > AllowedStoredGrowth * lengthRatio)
            throw new Exception(FormattableString.Invariant(
                $"Reading a stored name of {spellingLengths[step]} bytes costs {growth:F2} times as much as ") +
                FormattableString.Invariant($"{spellingLengths[step - 1]}; ") +
                FormattableString.Invariant($"the limit is {AllowedStoredGrowth * lengthRatio:F1}."));
    }
}

// `indirectTarget` selects the body of a `calli` by comparing the pointer's owner with each catalog entry's, and a
// proof decides it by `cil_kernel_rfl`: the kernel's cost grows with the owner's length and no faster.
void IndirectTargetCosts()
{
    var targetDirectory = At("artifacts/LookupScaling/IndirectTarget");
    Directory.CreateDirectory(targetDirectory);
    int[] ownerLengths = [64, 256, 1024];
    // The selection's heartbeats, less those of its statement closed with `sorry` and read before it in the same file.
    long Selection(int length)
    {
        var owner = string.Concat(Enumerable.Range(0, length).Select(index => (char)('a' + index % 26)));
        var identity = $$"""⟨"{{owner}}", 6, []⟩""";
        var header = """
            import CIL.Safety.Execution
            import CIL.Extraction.KernelEquation
            def signature : CIL.ManagedSignature :=
              ⟨.primitive .int32, [.primitive .int32]⟩
            """ + "\n";
        var statement = $$"""
            CIL.Safety.indirectTarget signature [⟨⟨"other", 6, []⟩, 2⟩, ⟨{{identity}}, 1⟩]
                ⟨signature, some {{identity}}⟩ = some 1
            """;
        var costs = PartHeartbeats(Path.Combine(targetDirectory, $"Owner{length}.lean"),
            [header, $"theorem selected_open : {statement} := sorry\n",
                $"theorem selected : {statement} := by cil_kernel_rfl\n"]);
        return costs[1] - costs[0];
    }
    var costs = ownerLengths.Select(length => (double)Selection(length)).ToArray();
    for (var step = 1; step < ownerLengths.Length; step++)
    {
        var lengthRatio = ownerLengths[step] / (double)ownerLengths[step - 1];
        var growth = costs[step] / costs[step - 1];
        Console.WriteLine(FormattableString.Invariant(
            $"PASS selecting a calli body for an owner of {ownerLengths[step - 1]} and {ownerLengths[step]} bytes: ") +
            FormattableString.Invariant($"{costs[step - 1]:F0} and {costs[step]:F0} heartbeats, ") +
            FormattableString.Invariant($"{growth / lengthRatio:F2} times the cost per byte"));
        if (growth > AllowedSpellingGrowth * lengthRatio)
            throw new Exception(FormattableString.Invariant(
                $"Selecting a calli body for an owner of {ownerLengths[step]} bytes costs {growth:F2} times ") +
                FormattableString.Invariant($"as much as for {ownerLengths[step - 1]}; ") +
                FormattableString.Invariant($"the limit is {AllowedSpellingGrowth * lengthRatio:F1}."));
    }
}

// The instance reader carries its receiver's full base chain. The static reader names only the argument and field.
// Fixed-width identifiers keep longer UTF-8 names out of the measured cost difference.
const double AllowedChainIncrementRatio = 2.5;
int[] baseDepths = [4, 8, 16];
var deepSource = Path.Combine(directory, "DeepAssembly");
Directory.CreateDirectory(deepSource);
File.WriteAllText(Path.Combine(deepSource, "Deep.csproj"), """
<Project Sdk="Microsoft.NET.Sdk">
  <PropertyGroup><TargetFramework>net11.0</TargetFramework><Optimize>true</Optimize>
    <AssemblyName>Bodies</AssemblyName></PropertyGroup>
</Project>
""");
string DeepType(int depth, int index) => $"Deep{depth:D2}_{index:D2}";
string Deep(int depth)
{
    var classes = Join(depth, index =>
    {
        var reader = index + 1 == depth ? "public ulong ReadField() => F;" : "";
        return $"public class {DeepType(depth, index + 1)} : {DeepType(depth, index)} {{ {reader} }} ";
    });
    return $"public class {DeepType(depth, 0)} {{ public ulong F; }} {classes}" +
        $"public static ulong ReadDeep{depth:D2}({DeepType(depth, depth)} o) => o.F; ";
}
File.WriteAllText(Path.Combine(deepSource, "Deep.cs"),
    "public static class Bodies { " + string.Concat(baseDepths.Select(Deep)) + "}");
Run(["dotnet", "build", Path.Combine(deepSource, "Deep.csproj"), "-c", "Release"]);
var deepAssembly = Path.Combine(deepSource, "bin/Bodies.dll");
void BaseDepthCosts()
{
    foreach (var instance in new[] { false, true })
    {
        var receiver = instance ? "instance" : "static";
        var costs = Concurrently(baseDepths, depth =>
        {
            var leaf = "Bodies/" + DeepType(depth, depth);
            var method = instance ? "ReadField" : $"ReadDeep{depth:D2}";
            var entry = instance ? $"{leaf}::{method}()" : $"Bodies::{method}({leaf})";
            return BodyChecks(deepAssembly, $"Deep-{receiver}-{depth}", entry, method,
                receiverBases: instance ? depth : 0).Body;
        });
        var first = costs[1] - costs[0];
        var second = costs[2] - costs[1];
        var result = $"{receiver} field read at depths {string.Join("/", baseDepths)}: " +
            $"{string.Join("/", costs)} heartbeats";
        if (second > Math.Max(0, first) * AllowedChainIncrementRatio)
            throw new InvalidOperationException($"{result}; increments {first} and {second} exceed " +
                $"the {AllowedChainIncrementRatio} growth limit.");
        Console.WriteLine($"PASS {result}; increments {first} and {second} stay within {AllowedChainIncrementRatio}.");
    }
}

// The kernel heartbeats of the scalar certificate of a body whose segments each address an array element, with
// or without a `readonly.` prefix, and branch to the next segment, less those of stating the same certificate.
// Each instruction carries the byte offset extraction writes, so no two sites present the kernel the same check.
long ArrayAddressCost(bool prefixed, int sites)
{
    var flag = prefixed ? "true" : "false";
    var header = $$"""
        import CIL.Extraction.Scalars
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace ArrayAddresses
        open CIL CIL.Extraction
        def intType : TypeExpr := .primitive .int32
        def width (prefixed : Bool) : Nat := if prefixed then 6 else 5
        def bytes (prefixed : Bool) : Nat := if prefixed then 12 else 10
        def segment (prefixed : Bool) (index : Nat) : List RawInstruction :=
          let base := index * bytes prefixed
          let address := base + bytes prefixed - 8
          [⟨base, 2, .none⟩, ⟨base + 1, 3, .none⟩] ++
            (if prefixed then [⟨base + 2, 65054, .none⟩] else []) ++
            [⟨address, 143, .type intType⟩, ⟨address + 5, 38, .none⟩,
              ⟨address + 6, 43, .target ((index + 1) * width prefixed)⟩]
        def raw (prefixed : Bool) (sites : Nat) : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [.array intType, intType], locals := [], initLocals := true, maxStack := 2,
          genericParameters := [],
          code := (List.range sites).flatMap (segment prefixed) ++ [⟨sites * bytes prefixed, 42, .none⟩] }
        def featureSegment (prefixed : Bool) : FeatureCertificate :=
          [some ⟨[], []⟩, some ⟨[none], []⟩] ++
            (if prefixed then [some ⟨[none, none], []⟩] else []) ++
            [some ⟨[none, none], []⟩, some ⟨[none], []⟩, some ⟨[], []⟩]
        def features (prefixed : Bool) (sites : Nat) : FeatureCertificate :=
          (List.replicate sites (featureSegment prefixed)).flatten ++ [some ⟨[], []⟩]
        def stateSegment (prefixed : Bool) : ScalarCertificate :=
          [some [], some [.array .signed32]] ++
            (if prefixed then [some [.word32, .array .signed32]] else []) ++
            [some [.word32, .array .signed32], some [.reference], some []]
        def states (prefixed : Bool) (sites : Nat) : ScalarCertificate :=
          (List.replicate sites (stateSegment prefixed)).flatten ++ [some []]
        def codeSegment (prefixed : Bool) (index : Nat) : List Instruction :=
          [.ldarg 0, .ldarg 1] ++ (if prefixed then [.nop] else []) ++
            [.ldelema intType prefixed, .pop, .br ((index + 1) * width prefixed)]
        def code (prefixed : Bool) (sites : Nat) : List Instruction :=
          (List.range sites).flatMap (codeSegment prefixed) ++ [.ret]
        """ + "\n";
    var statement = $"ScalarFlowValid (raw {flag} {sites}) (features {flag} {sites}) " +
        $"(states {flag} {sites}) (code {flag} {sites})";
    var path = Path.Combine(directory, $"ArrayAddresses{(prefixed ? "Prefixed" : "")}{sites}.lean");
    return DecideCost(path, header, statement, "ArrayAddresses");
}
void ArrayAddressCosts() => Concurrently(new[] { false, true }, prefixed =>
{
    var label = prefixed ? "readonly element addresses" : "element addresses";
    var perSite = new[] { FewAddresses, MoreAddresses, ManyAddresses }
        .Select(sites => (Sites: sites, Cost: (double)ReservingMemory(AddressMemory(sites), () =>
            ArrayAddressCost(prefixed, sites)) / sites)).ToArray();
    var addressesMeasured = string.Join("; ", perSite.Select(run =>
        string.Create(CultureInfo.InvariantCulture, $"{run.Cost:F0} kernel heartbeats per address at {run.Sites}")));
    if (perSite.Skip(1).Any(run => run.Cost > perSite[0].Cost * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking the scalar certificate of {label} costs {addressesMeasured}; the limit is {AllowedGrowth} " +
            $"times the cost per address at {FewAddresses}."));
    Console.WriteLine($"PASS checking the scalar certificate of {label} costs {addressesMeasured}");
});

// The kernel heartbeats of the feature and scalar certificates of a body whose segments each copy a block, with or
// without an `unaligned.` prefix, and branch to the next segment, less those of stating them. The indirect access
// rule reads the instructions next to each site from an index built once per body. Instructions carry byte offsets.
void IndirectAccessCosts()
{
    var accessDirectory = At("artifacts/LookupScaling/IndirectAccess");
    Directory.CreateDirectory(accessDirectory);
    long Cost(bool prefixed, int sites)
    {
        var flag = prefixed ? "true" : "false";
        var header = $$"""
            import CIL.Extraction.Scalars
            set_option maxRecDepth 100000
            set_option maxHeartbeats 0
            namespace IndirectAccesses
            open CIL CIL.Extraction
            def word : TypeExpr := .primitive .uint64
            def width (prefixed : Bool) : Nat := if prefixed then 6 else 5
            def bytes (prefixed : Bool) : Nat := if prefixed then 10 else 7
            def segment (prefixed : Bool) (index : Nat) : List RawInstruction :=
              let base := index * bytes prefixed
              let copy := base + bytes prefixed - 4
              [⟨base, 2, .none⟩, ⟨base + 1, 2, .none⟩, ⟨base + 2, 2, .none⟩] ++
                (if prefixed then [⟨base + 3, 65042, .integer 1⟩] else []) ++
                [⟨copy, 65047, .none⟩, ⟨copy + 2, 43, .target ((index + 1) * width prefixed)⟩]
            def raw (prefixed : Bool) (sites : Nat) : RawMethod := {
              token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
              callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
              parameters := [word], locals := [], initLocals := true, maxStack := 3,
              genericParameters := [],
              code := (List.range sites).flatMap (segment prefixed) ++
                [⟨sites * bytes prefixed, 42, .none⟩] }
            def featureSegment (prefixed : Bool) : FeatureCertificate :=
              [some ⟨[], []⟩, some ⟨[none], []⟩, some ⟨[none, none], []⟩] ++
                (if prefixed then [some ⟨[none, none, none], []⟩] else []) ++
                [some ⟨[none, none, none], []⟩, some ⟨[], []⟩]
            def features (prefixed : Bool) (sites : Nat) : FeatureCertificate :=
              (List.replicate sites (featureSegment prefixed)).flatten ++ [some ⟨[], []⟩]
            def stateSegment (prefixed : Bool) : ScalarCertificate :=
              [some [], some [.word64], some [.word64, .word64]] ++
                (if prefixed then [some [.word64, .word64, .word64]] else []) ++
                [some [.word64, .word64, .word64], some []]
            def states (prefixed : Bool) (sites : Nat) : ScalarCertificate :=
              (List.replicate sites (stateSegment prefixed)).flatten ++ [some []]
            def codeSegment (prefixed : Bool) (index : Nat) : List Instruction :=
              [.ldarg 0, .ldarg 0, .ldarg 0] ++ (if prefixed then [.nop] else []) ++
                [.cpblk (if prefixed then 1 else 8), .br ((index + 1) * width prefixed)]
            def code (prefixed : Bool) (sites : Nat) : List Instruction :=
              (List.range sites).flatMap (codeSegment prefixed) ++ [.ret]
            """ + "\n";
        var statement = $"FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw {flag} {sites}) .scalar " +
            $"(features {flag} {sites}) ((features {flag} {sites}).map Option.isSome) (code {flag} {sites}) ∧ " +
            $"ScalarFlowValid (raw {flag} {sites}) (features {flag} {sites}) (states {flag} {sites}) " +
            $"(code {flag} {sites})";
        var path = Path.Combine(accessDirectory, $"Blocks{(prefixed ? "Prefixed" : "")}{sites}.lean");
        return DecideCost(path, header, statement, "IndirectAccesses");
    }
    Concurrently(new[] { false, true }, prefixed =>
    {
        var label = prefixed ? "unaligned block copies" : "block copies";
        var perSite = new[] { FewAddresses, MoreAddresses, ManyAddresses }
            .Select(sites => (Sites: sites, Cost: (double)ReservingMemory(AddressMemory(sites), () =>
                Cost(prefixed, sites)) / sites)).ToArray();
        var measured = string.Join("; ", perSite.Select(run =>
            string.Create(CultureInfo.InvariantCulture, $"{run.Cost:F0} kernel heartbeats per copy at {run.Sites}")));
        if (perSite.Skip(1).Any(run => run.Cost > perSite[0].Cost * AllowedGrowth))
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"Checking the feature and scalar certificates of {label} costs {measured}; the limit is " +
                $"{AllowedGrowth} times the cost per copy at {FewAddresses}."));
        Console.WriteLine($"PASS checking the feature and scalar certificates of {label} costs {measured}");
    });
}

// The kernel heartbeats of the feature certificate of a body that loads, stores and addresses four int32 locals in
// turn, popping each address, less those of stating the same certificate. A local load, store or address checks
// its opcode and index alone.
long LocalAccessCost(int accesses)
{
    var cycles = accesses / 4;
    var header = $$"""
        import CIL.Extraction.Features
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace LocalAccesses
        open CIL CIL.Extraction
        def intType : TypeExpr := .primitive .int32
        def localCount : Nat := 4
        def segment (index : Nat) : List RawInstruction :=
          [⟨0, 17, .local (index % localCount)⟩, ⟨0, 19, .local ((index + 1) % localCount)⟩,
            ⟨0, 18, .local ((index + 2) % localCount)⟩, ⟨0, 38, .none⟩]
        def raw (cycles : Nat) : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [], locals := List.replicate localCount intType, initLocals := true,
          maxStack := 1, genericParameters := [],
          code := (List.range cycles).flatMap segment ++ [⟨0, 42, .none⟩] }
        def unknown : List (Nat × W32) := []
        def features (cycles : Nat) : FeatureCertificate :=
          (List.replicate cycles [some ⟨[], unknown⟩, some ⟨[none], unknown⟩, some ⟨[], unknown⟩,
            some ⟨[none], unknown⟩]).flatten ++ [some ⟨[], unknown⟩]
        def codeSegment (index : Nat) : List Instruction :=
          [.ldloc (index % localCount), .stloc ((index + 1) % localCount),
            .ldloca ((index + 2) % localCount), .pop]
        def code (cycles : Nat) : List Instruction := (List.range cycles).flatMap codeSegment ++ [.ret]
        """ + "\n";
    var statement = $"FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw {cycles}) .scalar " +
        $"(features {cycles}) (List.replicate {accesses + 1} true) (code {cycles})";
    var path = Path.Combine(directory, $"LocalAccesses{accesses}.lean");
    return DecideCost(path, header, statement, "LocalAccesses");
}
void LocalAccessCosts()
{
    var perAccess = new[] { FewLocalAccesses, MoreLocalAccesses, ManyLocalAccesses }
        .Select(accesses => (Accesses: accesses, Cost: (double)LocalAccessCost(accesses) / accesses)).ToArray();
    var accessesMeasured = string.Join("; ", perAccess.Select(run =>
        string.Create(CultureInfo.InvariantCulture,
            $"{run.Cost:F0} kernel heartbeats per instruction at {run.Accesses}")));
    if (perAccess.Skip(1).Any(run => run.Cost > perAccess[0].Cost * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking the feature certificate of local loads, stores and addresses costs {accessesMeasured}; " +
            $"the limit is {AllowedGrowth} times the cost per instruction at {FewLocalAccesses}."));
    Console.WriteLine(
        $"PASS checking the feature certificate of local loads, stores and addresses costs {accessesMeasured}");
}
// The kernel heartbeats of a check over a body that stores each of its locals once and then loads or addresses
// it, less those of stating the same check. Integer locals take a constant and are popped after a load or after
// `ldloca`; native-int locals take a method address and are
// consumed by `calli`, which makes each a pointer local. The check is the scalar certificate, or for pointer
// locals also the closed argument storage. Instructions carry byte offsets.
long LocalSlotCost(LocalSlots slots, int count, bool storage = false)
{
    var pointers = slots == LocalSlots.Pointer;
    var addressed = slots == LocalSlots.Addressed;
    var slotType = pointers ? "intPtr" : "int32";
    var kind = pointers ? ".methodPointer signature" : ".word32";
    var push = pointers ? "65030, .call handler" : "22, .none";
    var load = addressed ? "18, .local index" : "17, .local index";
    var consume = pointers ? "41, .indirectCall .void [] false false 0" : "38, .none";
    // ldftn and calli carry a four-byte token; ldc.i4.0 and pop are one byte, and the local forms two.
    var pushBytes = pointers ? 6 : 1;
    var consumeBytes = pointers ? 5 : 1;
    var loaded = addressed ? ".reference" : "kind";
    const string identity = """{ owner := "T::Scaling", token := 2, arguments := [] }""";
    var pushed = pointers ? $".ldftn {identity} signature" : ".ldc_i4 0";
    var emittedLoad = addressed ? ".ldloca index" : ".ldloc index";
    var consumed = pointers ? ".calli signature false" : ".pop";
    var header = $$"""
        import CIL.Extraction.Scalars
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace LocalSlots
        open CIL CIL.Extraction
        def slotType : TypeExpr := .primitive .{{slotType}}
        def handler : CallSite :=
          { declared := { convention := 0 }, method := {
              owner := .atom "T" "Scaling" .classType, name := name!"", hasThis := false, genericArity := 0,
              returnType := .void, parameters := [] },
            target := .managed 2, typeArguments := [], parameterCount := 0, returnsValue := false }
        def signature : ManagedSignature := ⟨.void, []⟩
        def kind : ScalarKind := {{kind}}
        def bytes : Nat := {{pushBytes + 4 + consumeBytes}}
        def segment (index : Nat) : List RawInstruction :=
          let base := index * bytes
          [⟨base, {{push}}⟩, ⟨base + {{pushBytes}}, 19, .local index⟩, ⟨base + {{pushBytes + 2}}, {{load}}⟩,
            ⟨base + {{pushBytes + 4}}, {{consume}}⟩]
        def raw (slots : Nat) : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [], locals := List.replicate slots slotType, initLocals := true, maxStack := 1,
          genericParameters := [],
          code := (List.range slots).flatMap segment ++ [⟨slots * bytes, 42, .none⟩] }
        def features (slots : Nat) : FeatureCertificate :=
          (List.replicate slots [some ⟨[], []⟩, some ⟨[none], []⟩, some ⟨[], []⟩, some ⟨[none], []⟩]).flatten ++
            [some ⟨[], []⟩]
        def states (slots : Nat) : ScalarCertificate :=
          (List.replicate slots [some [], some [kind], some [], some [{{loaded}}]]).flatten ++ [some []]
        def codeSegment (index : Nat) : List Instruction :=
          [{{pushed}}, .stloc index, {{emittedLoad}}, {{consumed}}]
        def code (slots : Nat) : List Instruction := (List.range slots).flatMap codeSegment ++ [.ret]
        """ + "\n";
    var statement = storage ? $"(closedArguments [] (raw {count})).isSome = true"
        : $"ScalarFlowValid (raw {count}) (features {count}) (states {count}) (code {count})";
    var path = Path.Combine(directory, $"{slots}{(storage ? "Storage" : "Locals")}{count}.lean");
    return DecideCost(path, header, statement, "LocalSlots");
}
void LocalSlotCosts()
{
    (LocalSlots Slots, bool Storage, string Label)[] localChecks =
    [
        (LocalSlots.Integer, false, "the scalar certificate of integer locals"),
        (LocalSlots.Addressed, false, "the scalar certificate of addressed integer locals"),
        (LocalSlots.Pointer, false, "the scalar certificate of native-int locals consumed by calli"),
        (LocalSlots.Pointer, true, "the closed argument storage of native-int locals consumed by calli"),
    ];
    foreach (var (slots, storage, label) in localChecks)
    {
        // Each local is stored once and loaded or addressed once, between a push and a pop or call; `ret` ends
        // the body.
        var perInstruction = new[] { FewLocals, MoreLocals, ManyLocals }
            .Select(count => (Count: count, Cost: (double)ReservingMemory(
                count == ManyLocals ? MediumLeanProcess : 0, () => LocalSlotCost(slots, count, storage)) /
                (4 * count + 1)))
            .ToArray();
        var localsMeasured = string.Join("; ", perInstruction.Select(run => string.Create(CultureInfo.InvariantCulture,
            $"{run.Cost:F0} kernel heartbeats per instruction at {run.Count} locals")));
        if (perInstruction.Skip(1).Any(run => run.Cost > perInstruction[0].Cost * AllowedLocalGrowth))
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"Checking {label} costs {localsMeasured}; the limit is {AllowedLocalGrowth} " +
                $"times the cost per instruction at {FewLocals} locals."));
        Console.WriteLine($"PASS checking {label} costs {localsMeasured}");
    }
}

// The kernel heartbeats of the feature certificate of a body of fixed length over `count` int32 locals, less those of
// stating the same certificate. Each segment loads, stores and addresses a local, then addresses the argument and
// stores a constant into it, so the local and argument sites of the check are all exercised.
long FeatureLocalCost(int count)
{
    var header = $$"""
        import CIL.Extraction.Features
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace FeatureLocals
        open CIL CIL.Extraction
        def intType : TypeExpr := .primitive .int32
        def localCount : Nat := {{count}}
        def segment (index : Nat) : List RawInstruction :=
          [⟨0, 17, .local (index % localCount)⟩, ⟨0, 19, .local ((index + 1) % localCount)⟩,
            ⟨0, 18, .local ((index + 2) % localCount)⟩, ⟨0, 38, .none⟩, ⟨0, 15, .argument 0⟩, ⟨0, 38, .none⟩,
            ⟨0, 22, .none⟩, ⟨0, 16, .argument 0⟩]
        def raw (segments : Nat) : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [intType], locals := List.replicate localCount intType, initLocals := true,
          maxStack := 1, genericParameters := [],
          code := (List.range segments).flatMap segment ++ [⟨0, 42, .none⟩] }
        def unknown : List (Nat × W32) := []
        def features (segments : Nat) : FeatureCertificate :=
          (List.replicate segments [some ⟨[], unknown⟩, some ⟨[none], unknown⟩, some ⟨[], unknown⟩,
            some ⟨[none], unknown⟩, some ⟨[], unknown⟩, some ⟨[none], unknown⟩, some ⟨[], unknown⟩,
            some ⟨[some 0], unknown⟩]).flatten ++ [some ⟨[], unknown⟩]
        def codeSegment (index : Nat) : List Instruction :=
          [.ldloc (index % localCount), .stloc ((index + 1) % localCount),
            .ldloca ((index + 2) % localCount), .pop, .ldarga 0, .pop, .ldc_i4 0, .starg 0]
        def code (segments : Nat) : List Instruction := (List.range segments).flatMap codeSegment ++ [.ret]
        """ + "\n";
    var statement = $"FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw {FeatureLocalSegments}) .scalar " +
        $"(features {FeatureLocalSegments}) (List.replicate {FeatureLocalInstructions} true) " +
        $"(code {FeatureLocalSegments})";
    var path = Path.Combine(directory, $"FeatureLocals{count}.lean");
    return DecideCost(path, header, statement, "FeatureLocals");
}
void FeatureLocalCosts()
{
    var perFeatureInstruction = new[] { FewFeatureLocals, MoreFeatureLocals, ManyFeatureLocals }
        .Select(count => (Count: count, Cost: (double)FeatureLocalCost(count) / FeatureLocalInstructions)).ToArray();
    var featureLocalsMeasured = string.Join("; ", perFeatureInstruction.Select(run => string.Create(
        CultureInfo.InvariantCulture, $"{run.Cost:F0} kernel heartbeats per instruction at {run.Count} locals")));
    if (perFeatureInstruction.Skip(1).Any(run => run.Cost > perFeatureInstruction[0].Cost * AllowedLocalGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking the feature certificate of {FeatureLocalInstructions} instructions costs " +
            $"{featureLocalsMeasured}; the limit is {AllowedLocalGrowth} times the cost per instruction at " +
            $"{FewFeatureLocals} locals."));
    Console.WriteLine($"PASS checking the feature certificate of {FeatureLocalInstructions} instructions costs " +
        featureLocalsMeasured);
}

// One literal certificate state, written as the extractor writes states, so a fact costs only what the check costs.
static string KnownFactState(IEnumerable<int> stack, IEnumerable<int> words) =>
    $"some ⟨[{string.Join(", ", stack.Select(word => $"some {word}"))}], " +
    $"[{string.Join(", ", words.Select((word, index) => $"({index}, {word})"))}]⟩";

// The literal certificate of the body `KnownFactCost` checks: round `round` stores the word `round + 1`.
static string KnownFactCertificate(int facts, int rounds)
{
    var states = new List<string>();
    for (var index = 0; index < facts; index++)
    {
        var stored = new int[index];
        states.Add(KnownFactState([], stored));
        states.Add(KnownFactState([0], stored));
    }
    var words = new int[facts];
    for (var round = 0; round < rounds; round++)
    {
        states.Add(KnownFactState([], words));
        states.Add(KnownFactState([round + 1], words));
        words[round % facts] = round + 1;
        states.Add(KnownFactState([], words));
        states.Add(KnownFactState([round + 1], words));
    }
    states.Add(KnownFactState([], words));
    return string.Join(",\n  ", states);
}

// The kernel heartbeats of the certificate of a body storing zero into `facts` of `ManyKnownFacts` int32 locals and
// then running `rounds` rounds that each store into one of them in turn and load it, less those of stating it.
long KnownFactCost(int facts, int rounds)
{
    var header = $$"""
        import CIL.Extraction.Features
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace KnownFacts
        open CIL CIL.Extraction
        def intType : TypeExpr := .primitive .int32
        def facts : Nat := {{facts}}
        def rounds : Nat := {{rounds}}
        def raw : RawMethod := {
          token := 1, owner := "Scaling", hasThis := false, explicitThis := false,
          callingConvention := 0, attributes := 0, implementation := 0, returnType := .void,
          parameters := [], locals := List.replicate {{ManyKnownFacts}} intType, initLocals := true,
          maxStack := 1, genericParameters := [],
          code := (List.range facts).flatMap (fun index => [⟨0, 22, .none⟩, ⟨0, 19, .local index⟩]) ++
            (List.range rounds).flatMap (fun round => [⟨0, 32, .integer (round + 1 : Nat)⟩,
              ⟨0, 19, .local (round % facts)⟩, ⟨0, 17, .local (round % facts)⟩, ⟨0, 38, .none⟩]) ++
            [⟨0, 42, .none⟩] }
        def features : FeatureCertificate := [
          {{KnownFactCertificate(facts, rounds)}}]
        def code : List Instruction :=
          (List.range facts).flatMap (fun index => [.ldc_i4 0, .stloc index]) ++
            (List.range rounds).flatMap (fun round =>
              [.ldc_i4 (BitVec.ofNat 32 (round + 1)), .stloc (round % facts), .ldloc (round % facts), .pop]) ++
            [.ret]
        """ + "\n";
    var statement = $"FeatureFlowValid #[] (fun _ => none) (fun _ => none) raw .scalar features " +
        $"(List.replicate {2 * facts + 4 * rounds + 1} true) code";
    var path = Path.Combine(directory, $"KnownFacts{facts}-{rounds}.lean");
    return DecideCost(path, header, statement, "KnownFacts");
}
void KnownFactCosts()
{
    // Subtract the stores alone, whose states together hold about the square of the facts.
    int[] factCounts = [FewKnownFacts, MoreKnownFacts, ManyKnownFacts];
    var factCosts = factCounts
        .Select(facts => (double)(KnownFactCost(facts, KnownFactRounds) - KnownFactCost(facts, 0))).ToArray();
    var factIncrementRatio = (factCosts[2] - factCosts[1]) / (factCosts[1] - factCosts[0]);
    var perFactState = (factCosts[2] - factCosts[1]) / ((ManyKnownFacts - MoreKnownFacts) * 4.0 * KnownFactRounds);
    var factsMeasured = string.Join("; ", factCounts.Zip(factCosts, (facts, cost) =>
        string.Create(CultureInfo.InvariantCulture, $"{cost:F0} kernel heartbeats at {facts} facts"))) +
        string.Create(CultureInfo.InvariantCulture,
            $"; increments in the ratio {factIncrementRatio:F2} (linear 4, quadratic 16); {perFactState:F0} per fact " +
            $"per state, {perFactState * ManyKnownFacts * 4 * KnownFactRounds:F0} for {ManyKnownFacts} facts in " +
            $"{4 * KnownFactRounds} states");
    if (factIncrementRatio > AllowedFactIncrementRatio)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking the feature certificate of {KnownFactRounds} rounds of known facts costs {factsMeasured}; the " +
            $"limit on the ratio is {AllowedFactIncrementRatio}."));
    Console.WriteLine(
        $"PASS checking the feature certificate of {KnownFactRounds} rounds of known facts costs {factsMeasured}");
}

var layoutIdentityCosts = LayoutIdentityCosts();
// The longest checks come first, so their processes ask for a slot first.
Concurrently(BodyCheckCosts, TokenCosts, SparseLinkCosts, () => NoCallEvidenceCosts(InstructionEquationCosts()),
    IndirectAccessCosts, CallingCosts, ArrayAddressCosts, LocalSlotCosts, KnownFactCosts, FeatureLocalCosts,
    () => ReservingMemory(MediumLeanProcess, LocalAccessCosts),
    () => ReservingMemory(LargeLeanProcess, DecodedDefinitionCosts),
    () => ReservingMemory(LargeLeanProcess, MethodDecodeCosts), templateChoiceCosts, EmbeddingCosts, BaseDepthCosts,
    ComputedLookupCosts, SpellingCosts, StoredNameCosts, IndirectTargetCosts, NativeTableCosts,
    ExceptionDecisionCosts, CheckNarrowedResolution, () => ReturnResolutionCosts(), ArgumentResolutionCosts,
    ElementShapeCosts, () => ShapeResolutionCosts(), LineageCosts, CallCheckCosts, StaticFactCosts,
    StaticIdentityCosts, DecodedProgramCosts, PrefixEntryCosts, RunCosts, ClosedArgumentsCosts, layoutIdentityCosts,
    TypeIdentityCosts, MetadataNameCosts, PlatformTableCosts, ImportLinkCosts);

/// <summary>How the generated bodies of the local slot checks use each local.</summary>
enum LocalSlots
{
    /// <summary>An int32 local that takes a constant and is loaded and popped.</summary>
    Integer,
    /// <summary>An int32 local that takes a constant and whose address is taken and popped.</summary>
    Addressed,
    /// <summary>A native-int local that takes a method address and is loaded by `calli`.</summary>
    Pointer,
}

/// <summary>
/// A program shape of the closure cost row: the program of each size, and the methods and link callees of the
/// closure of its method 0.
/// </summary>
record ClosureShape(string Name, int[] Sizes, Func<int, int[][]> Program, Func<int, int> Methods,
    Func<int, int> Edges);

/// <summary>The patterns that read the cost reports and the link output of the fixtures above.</summary>
static partial class LookupPatterns
{
    [GeneratedRegex(
        @"\bmark ([0-9]+) ([0-9]+) (rfl list|rfl index|kernel list|kernel index|stepper) (start|end) ([0-9]+)")]
    internal static partial Regex RunMark { get; }

    [GeneratedRegex(@"\bevidence (calls|assembly) ([0-9]+) heartbeats")]
    internal static partial Regex EvidenceCost { get; }

    [GeneratedRegex(@"(?m)^namespace Extracted\r?$")]
    internal static partial Regex ExtractedNamespace { get; }

    [GeneratedRegex(@"(?m)^theorem method0_calls_validated ")]
    internal static partial Regex CallsTheorem { get; }

    [GeneratedRegex(@"(?m)^theorem method0_evidence_validated ")]
    internal static partial Regex EvidenceTheorem { get; }

    [GeneratedRegex(@"closed arguments [0-9]+ [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex ClosedArguments { get; }

    [GeneratedRegex(@"resolution (fact|simplifier|objects) ([0-9]+) heartbeats")]
    internal static partial Regex ReturnResolution { get; }

    [GeneratedRegex(@"static identities ([0-9]+) heartbeats")]
    internal static partial Regex StaticIdentities { get; }

    [GeneratedRegex(@"call check ([0-9]+) heartbeats")]
    internal static partial Regex CallCheck { get; }

    [GeneratedRegex(@"lineage (rejected|located) ([0-9]+) heartbeats")]
    internal static partial Regex Lineage { get; }

    [GeneratedRegex(@"([0-9]+) lemmas rechecked, ([0-9]+) kernel heartbeats")]
    internal static partial Regex EmbeddingRecheck { get; }

    [GeneratedRegex(@"([0-9]+) kernel heartbeats")]
    internal static partial Regex KernelHeartbeats { get; }

    [GeneratedRegex(@"^@\[cil_code\] def method0Link")]
    internal static partial Regex LinkLine { get; }

    [GeneratedRegex(@"\b((?:un)?equal [0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex TypeDecision { get; }

    [GeneratedRegex(@"\bname spells ([0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex MetadataNameCost { get; }

    [GeneratedRegex(@"\bmodel (lookup (?:first|middle|last)|agreement|calls) ([0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex ModelTableCost { get; }

    [GeneratedRegex(@"\bplatform ([a-z]+) ([0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex PlatformTableCost { get; }

    /// <summary>The cost of selecting and checking distinct imported calls.</summary>
    [GeneratedRegex(@"import links (\d+) (\d+) heartbeats")]
    internal static partial Regex ImportLinkCost { get; }

    [GeneratedRegex(@"\b((?:thrownEqual|thrownUnequal|clrUnequal|raisesEqual) [A-Za-z]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex ExceptionDecision { get; }

    [GeneratedRegex(@"table step [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex NativeTableStep { get; }

    [GeneratedRegex(@"table load first [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex NativeTableLoadFirst { get; }

    [GeneratedRegex(@"table load last [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex NativeTableLoadLast { get; }

    [GeneratedRegex(@"decode [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex ValueDecoding { get; }

    [GeneratedRegex(@"decoded method [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex DecodedMethod { get; }

    [GeneratedRegex(@"decoded definition [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex DecodedDefinition { get; }

    [GeneratedRegex(@"prefix (body|ascending|descending|shuffled) [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex PrefixEntry { get; }

    [GeneratedRegex(@"decoded program [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex DecodedProgram { get; }

    [GeneratedRegex(@"\b(list )?closure (chain|longchain|fan|tail) ([0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex ClosureCost { get; }

    [GeneratedRegex(@"\bmark index ([0-9]+) (start|end|equations|lookups) ([0-9]+)")]
    internal static partial Regex HeartbeatMark { get; }

    [GeneratedRegex(@"(?m)^set_option maxRecDepth [0-9]+")]
    internal static partial Regex RecursionDepth { get; }

    [GeneratedRegex(@"(?m)^cil_instruction_equations method0\r?$")]
    internal static partial Regex FirstEquations { get; }

    [GeneratedRegex(@"_instruction[0-9]+' depends on axioms: \[propext\]")]
    internal static partial Regex EquationAxioms { get; }

    [GeneratedRegex("""\(\d+, \.text "[^"]*"\)""")]
    internal static partial Regex StringToken { get; }

    [GeneratedRegex(@"\(\d+, \.field ")]
    internal static partial Regex FieldToken { get; }

    [GeneratedRegex(@"\(\d+, \.call ")]
    internal static partial Regex CallToken { get; }

    [GeneratedRegex("""def method(\d+)Signature : String := "[^"]*?Bodies(?:/[^":(]+)?::(?<method>[^"(]*)\(""")]
    internal static partial Regex BodySignature { get; }

    [GeneratedRegex(@"(?m)^theorem (?<name>method\d+_body_validated) : (?<statement>[^\r\n]*?) := ⟨[^\r\n]*⟩\r?\n")]
    internal static partial Regex BodyObligation { get; }

    [GeneratedRegex(@"(?m)^cil_evaluated (?<method>method\d+)Tables : [^\r\n]+\r?\n")]
    internal static partial Regex EvaluatedTables { get; }

    [GeneratedRegex(@"(?m)^theorem (?<method>method\d+)_tables_valid : [^\r\n]+\r?\n")]
    internal static partial Regex TablesObligation { get; }
}
