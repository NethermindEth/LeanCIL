#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include GeneratedEvidence.cs

using System.Globalization;
using System.Text;
using System.Text.RegularExpressions;

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
if (args.Contains("--return-resolution-only", StringComparer.Ordinal)) return;
CallCheckCosts();
DecodeCosts();
MethodDecodeCosts();
StaticFactCosts();
StaticIdentityCosts();
DecodedDefinitionCosts();
DecodedProgramCosts();
PrefixEntryCosts();
ClosureCosts();
ClosedArgumentsCosts();

Run(["dotnet", "run", "--file", At("Tests/MetadataFieldPrefixes.cs"), "-c", "Release"]);
BuildLeanTestLibraries("Certificate index, feature getter, layout and home index libraries",
    "Tests.FlowIndex", "Tests.CertificateFlow", "Tests.FeatureGetter", "Tests.ExtractionHomeIndexes",
    "Tests.LayoutAccumulation", "Tests.LayoutProjectionIndexes");

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

var directory = At("artifacts/LookupScaling");
Directory.CreateDirectory(directory);

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
        ["methods", "depth", "body", "layouts", "enum-depth", "enum-layouts", "step-methods", "step-body"];
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
            var type = ".atom runtimeScope \"System.Byte\"";
            var expected = "some .unsigned8";
            if (dimension == "depth")
                type = string.Concat(Enumerable.Repeat(".enum \"Nested\" (", size)) + type + new string(')', size);
            if (dimension == "layouts")
            {
                type = ".aggregate \"Point\" 0";
                expected = "none";
            }
            if (dimension is "enum-depth" or "enum-layouts")
            {
                var depth = dimension == "enum-depth" ? size : 1;
                type = string.Concat(Enumerable.Repeat(".enum \"Nested\" (", depth)) +
                    ".array (.aggregate \"Point\" 0)" + new string(')', depth);
                expected = "none";
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
            var costs = LookupPatterns.ReturnResolution().Matches(output).Cast<Match>().ToArray();
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
                perItem: dimension is "methods" or "depth" or "enum-depth" or "step-methods"))
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
    const string Int32Type = ".atom runtimeScope \"System.Int32\"";
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
            var costs = LookupPatterns.ReturnResolution().Matches(output).Cast<Match>().ToArray();
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
              { owner := .atom "Fixture" "Holder", index := 0, type := .atom "Fixture" "Pair", name := name!"Field" }
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
        var costs = LookupPatterns.ReturnResolution().Matches(output).Cast<Match>().ToArray();
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
              { owner := .atom "Fixture" "Holder", index := 0, type := .atom "Fixture" "Pair", name := name!"Field" }
            def body : Method := {
              code := [{{code}}], locals := [], returnsValue := false, declared := {},
              staticSites := [{{sites}}] }
            def evidence : BodyEvidence :=
              { bytes := [], tokens := { operands := [] }, metadata := {}, identities := [bytesOf "Fixture"],
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
        var cost = LookupPatterns.StaticIdentities().Match(output);
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
    var costs = LookupPatterns.ReturnResolution().Matches(output).Cast<Match>().ToArray();
    if (costs.Length != 2)
        throw new InvalidOperationException("Missing element shape costs: " + output);
    return (types, long.Parse(costs[0].Groups[2].Value, CultureInfo.InvariantCulture),
        long.Parse(costs[1].Groups[2].Value, CultureInfo.InvariantCulture));
}

// Fails when the shape facts or reads of distinct operands cost over 1.35 times more per operand than at the size
// before: fields of one struct up to 128, and fields and value types of a struct each up to 512, read by a
// 512-instruction body. A fact that walks the layouts to its struct costs 1.7 times as much per operand at 512 as
// at 128 for fields and 3.2 times for value types. Every row is measured before the first failure is reported.
void ShapeResolutionCosts()
{
    const double AllowedShapeGrowth = 1.35;
    var resolutionDirectory = At("artifacts/LookupScaling/ShapeResolution");
    Directory.CreateDirectory(resolutionDirectory);
    (string Name, string Label, int[] Sizes, bool Spread, bool Value)[] rows =
    [
        ("Struct", "field shape {0} with every field in one struct", [8, 32, 128], false, false),
        ("Spread", "field shape {0} with each field in its own struct", [8, 32, 128, 512], true, false),
        ("Value", "value shape {0} with each type a struct of its own", [8, 32, 128, 512], true, true),
    ];
    var failures = new List<string>();
    foreach (var row in rows)
    {
        var samples = new List<(int Size, long Facts, long Reads)>();
        foreach (var size in row.Sizes)
        {
            var output = RunShapeFixture(resolutionDirectory, row.Name, size, row.Spread, row.Value);
            var costs = LookupPatterns.ReturnResolution().Matches(output).Cast<Match>().ToArray();
            if (costs.Length != size + 1)
                throw new InvalidOperationException("Missing shape resolution costs: " + output);
            long Sum(string label) => costs.Where(match => match.Groups[1].Value == label)
                .Sum(match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
            samples.Add((size, Sum("fact"), Sum("simplifier")));
        }
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
        var costs = LookupPatterns.Lineage().Matches(output).Cast<Match>().ToArray();
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
string RunShapeFixture(string directory, string name, int size, bool spread, bool value)
{
    var structs = spread ? size : 1;
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
    for (var operand = 0; operand < size; operand++)
    {
        var owner = spread ? operand : 0;
        operands.AppendLine(value
            ? $"def operand{operand} : TypeExpr := .aggregate \"T::S{owner}\" {owner}"
            : $"def operand{operand} : FieldRef := {{ owner := .aggregate \"T::S{owner}\" {owner}, " +
                $"index := {(spread ? 0 : operand)}, type := .atom runtimeScope \"System.Int32\", " +
                $"name := name!\"f{operand}\" }}");
        facts.AppendLine($"#resolution_cost \"fact\" in cil_{(value ? "value" : "field")}_shape environment " +
            $"operand{operand}");
    }
    var reads = string.Join(", ", Enumerable.Range(0, size).Select(operand =>
        $"body.{(value ? "valueShape" : "fieldShape")} operand{operand}"));
    var shapes = string.Join(", ", Enumerable.Range(0, size).Select(operand =>
        value ? ".aggregate 4" : $".value {(spread ? 0 : 4 * operand)} 4 false"));
    var shapeType = value ? "ValueShape" : "FieldShape";
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
        #resolution_cost "simplifier" in
        theorem body_reads : ([{{reads}}] : List {{shapeType}}) = [{{shapes}}] := by simp only [cil_code]
        #print axioms operand{{size - 1}}_shape
        #print axioms body_reads
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
            $"ManagedCallsValid [⟨[], callee⟩] [] (fun _ => false) raw (List.replicate {2 * sites} true) body";
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
              token := 1, owner := "Tests::Scaling", hasThis := false, explicitThis := false,
              callingConvention := 0, attributes := 0, implementation := 0,
              returnType := .void, parameters := [], locals := [], initLocals := true, maxStack := 1,
              genericParameters := [], code := [] }
            def callMethod : MethodRef := {
              owner := .atom "Tests" "Scaling", name := name!"", hasThis := false, genericArity := 0,
              returnType := .void, parameters := [] }
            def site : RawInstruction := ⟨0, 40, .call {
              method := callMethod, target := .managed 1, typeArguments := [], parameterCount := 0,
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
        var cost = LookupPatterns.CallCheck().Match(output);
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
            declared := { returnType := .atom runtimeScope "System.Byte" } }
        theorem method0_returnsValue : method0.returnsValue = true := rfl
        theorem method0_declared :
          method0.declared = { returnType := .atom runtimeScope "System.Byte" } := rfl
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
    var costs = LookupPatterns.ExceptionDecision().Matches(output).ToDictionary(
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
        var cost = LookupPatterns.ValueDecoding().Match(output);
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

// Deciding prefix entry over the destination mask must stay within `AllowedLocalGrowth` per instruction from 500 to
// 8000 instructions.
void PrefixEntryCosts()
{
    const int SegmentLength = 4;
    var directory = At("artifacts/LookupScaling/PrefixEntry");
    Directory.CreateDirectory(directory);
    var samples = new List<(int Instructions, long Cost)>();
    foreach (var instructions in new[] { 500, 2000, 8000 })
    {
        var path = Path.Combine(directory, $"Instructions{instructions}.lean");
        File.WriteAllText(path, $$"""
            import CIL.Extraction.Scalars
            set_option maxRecDepth 100000
            set_option maxHeartbeats 0
            open CIL CIL.Extraction Lean Elab Command
            {{KernelCostCommand}}
            namespace PrefixEntryCost
            /-- The element type of every address. -/
            def intType : TypeExpr := .atom runtimeScope "System.Int32"
            /-- One segment: a `readonly.` prefix, the element address it modifies, a pop and a branch
                to the prefix of the next segment. -/
            def segment (index : Nat) : List RawInstruction :=
              let start := {{SegmentLength}} * index
              [⟨start, 65054, .none⟩, ⟨start + 1, 143, .type intType⟩, ⟨start + 2, 38, .none⟩,
                ⟨start + 3, 43, .target (start + {{SegmentLength}})⟩]
            /-- A body of {{instructions}} raw instructions. -/
            def raw : List RawInstruction := (List.range {{instructions / SegmentLength}}).flatMap segment
            #kernel_cost "prefix entry {{instructions}}"
              prefixEntryFreeWith (branchTargetMask raw).testBit 0 raw = true
            end PrefixEntryCost
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.PrefixEntry().Match(output);
        if (!cost.Success) throw new InvalidOperationException($"Missing the prefix entry cost:\n{output}");
        samples.Add((instructions, long.Parse(cost.Groups[1].Value, CultureInfo.InvariantCulture)));
    }
    var perInstruction = samples.Select(sample => (double)sample.Cost / sample.Instructions).ToArray();
    var measured = string.Join("; ", samples.Select(sample => string.Create(CultureInfo.InvariantCulture,
        $"{(double)sample.Cost / sample.Instructions:F1} at {sample.Instructions}")));
    if (samples.Any(sample => sample.Cost < KernelDecisionFloor) ||
        perInstruction.Skip(1).Zip(perInstruction).Any(pair => pair.First > pair.Second * AllowedLocalGrowth))
        throw new InvalidOperationException(
            $"Deciding prefix entry costs {measured} heartbeats per instruction; the limit is " +
            $"{AllowedLocalGrowth} times the cost per instruction at the size before.");
    Console.WriteLine($"PASS deciding prefix entry costs {measured} heartbeats per instruction");
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
            def uint32 : TypeExpr := .atom runtimeScope "System.UInt32"
            /-- A static method with four parameters, four zero-initialized locals and {{instructions}} raw
                instructions. -/
            def source : RawMethod :=
              { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
                attributes := 0, implementation := 0, returnType := .void, parameters := List.replicate 4 uint32,
                locals := List.replicate 4 uint32, initLocals := true,
                maxStack := 8, genericParameters := [], code := raw }
            #kernel_cost "decoded method {{instructions}}"
              (Method.ofRaw? .scalar {} [] source []).any (fun method =>
                method.code.length == {{instructions}} &&
                  (method.code.zip code).all (fun pair => pair.1.sameValue pair.2) &&
                  method.locals == List.replicate 4 (.i32 0) && method.parameterHomes.isEmpty &&
                  method.links.isEmpty) = true
            end DecodedMethodCost
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.DecodedMethod().Match(output);
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
                locals := List.replicate 4 (.atom runtimeScope "System.UInt32"), initLocals := true,
                maxStack := 8, genericParameters := [],
                code := (List.range {{instructions / SegmentLength}}).flatMap segment }
            #command_cost "decoded definition {{instructions}}"
              cil_decoded_method method := Method.ofRaw? profile environment [] source []
            end DecodedDefinitionCost
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.DecodedDefinition().Match(output);
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
              Method.ofBody? profile environment item.links item.body item.original item.arguments =
                some method
            #command_cost "decoded program {{records}}"
              theorem decoded ({{items}} : MethodEvidence) ({{methods}} : CIL.Method)
            {{facts}} :
                  decodedProgram? profile environment [{{items.Replace(" ", ", ")}}] =
                    some [{{methods.Replace(" ", ", ")}}] :=
                decodedProgram?_eq_some {{bodies}}
            end DecodedProgramCost
            """ + "\n");
        var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
        var cost = LookupPatterns.DecodedProgram().Match(output);
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

// A closure search reads each of its n methods by index from a program of P methods and gives each of the e callees
// their link tables enter one packed table entry, so it costs O(n * P + e) kernel steps. Each shape grows one term:
// a chain whose closure is the whole program grows n * P, one method calling seven others grows e, and a closure of
// four methods at the start of a longer program grows P. A search that folded over its state instead costs time
// quadratic in e.
void ClosureCosts()
{
    var closureDirectory = At("artifacts/LookupScaling/Closures");
    Directory.CreateDirectory(closureDirectory);
    // Four times the units of n * P + e may cost at most this much more per unit.
    const double AllowedClosureGrowth = 1.15;
    ClosureShape[] shapes =
    [
        new("chain", [8, 32, 128], size => [.. Enumerable.Range(0, size).Select(int[] (index) =>
            index + 1 < size ? [index + 1] : [])], size => size, size => size - 1),
        new("fan", [32, 128, 512], size => [[.. Enumerable.Range(0, size).Select(index => 1 + index % 7)],
            .. Enumerable.Repeat(Array.Empty<int>(), 7)], _ => 8, size => size),
        new("tail", [128, 512, 2048], size => [[1], [2], [3], .. Enumerable.Repeat(Array.Empty<int>(), size - 3)],
            _ => 4, _ => 3)
    ];
    string Statement(ClosureShape shape, int size)
    {
        var program = shape.Program(size);
        return $$"""
            /-- The {{shape.Name}} program of size {{size}}. -/
            def {{shape.Name}}{{size}} : Program :=
              [{{string.Join(", ", program.Select(callees => $"stub [{string.Join(", ", callees)}]"))}}]
            #kernel_cost "closure {{shape.Name}} {{size}}"
              (({{shape.Name}}{{size}}.closure 0).map Prod.snd =
                some [{{string.Join(", ", Enumerable.Range(0, shape.Methods(size)))}}])
            """;
    }
    var path = Path.Combine(closureDirectory, "Closures.lean");
    File.WriteAllText(path, $$"""
        import CIL.Safety.ProgramClosure
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        open CIL Lean Elab Command
        {{KernelCostCommand}}
        /-- A method whose link table enters `callees` in order, one call pc each. -/
        def stub (callees : List Nat) : Method :=
          { code := [], locals := [], returnsValue := false,
            links := callees.zipIdx.map fun (callee, pc) => (pc, .direct callee) }
        {{string.Join("\n", shapes.SelectMany(shape => shape.Sizes.Select(size => Statement(shape, size))))}}
        """ + "\n");
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.ClosureCost().Matches(output).ToDictionary(
        match => (match.Groups[1].Value, int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture)),
        match => long.Parse(match.Groups[3].Value, CultureInfo.InvariantCulture));
    if (costs.Count != shapes.Sum(shape => shape.Sizes.Length) || costs.Values.Min() < KernelDecisionFloor)
        throw new InvalidOperationException("Missing closure costs:\n" + output);
    foreach (var shape in shapes)
    {
        var units = shape.Sizes.Select(size =>
            (double)shape.Methods(size) * shape.Program(size).Length + shape.Edges(size)).ToArray();
        if (ClosureGrowth(units, [.. units.Select(unit => unit * unit)]) <= AllowedClosureGrowth)
            throw new InvalidOperationException($"The {shape.Name} bound accepts a cost quadratic in n * P + e");
        var growth = ClosureGrowth(units, [.. shape.Sizes.Select(size => (double)costs[(shape.Name, size)])]);
        var measured = string.Join(", ", shape.Sizes.Select(size =>
            string.Create(CultureInfo.InvariantCulture, $"{costs[(shape.Name, size)]} at {size}")));
        if (growth > AllowedClosureGrowth)
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"The {shape.Name} closure costs {measured} heartbeats; its cost per unit of n * P + e grows " +
                $"{growth:F2} times, more than {AllowedClosureGrowth}"));
        Console.WriteLine(string.Create(CultureInfo.InvariantCulture,
            $"PASS the {shape.Name} closure costs {measured} heartbeats, {growth:F2} times as much per unit of " +
            $"n * P + e between its last sizes as between its first"));
    }
}

// How many times as much each added unit costs between the last two sizes as between the first two.
static double ClosureGrowth(double[] units, double[] costs) =>
    (costs[2] - costs[1]) / (units[2] - units[1]) / ((costs[1] - costs[0]) / (units[1] - units[0]));

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
              parameters := List.replicate {{parameters}} (.atom runtimeScope "System.UInt32"),
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
        var cost = LookupPatterns.ClosedArguments().Match(output);
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
        costs.Add((entries, Measured(LookupPatterns.NativeTableStep(), "step"),
            Measured(LookupPatterns.NativeTableLoadFirst(), "first load"),
            Measured(LookupPatterns.NativeTableLoadLast(), "last load")));
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
    var costs = LookupPatterns.TypeDecision().Matches(output).ToDictionary(
        match => match.Groups[1].Value, match => long.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture));
    if (costs.Count != 4) throw new InvalidOperationException("Missing type identity decision costs:\n" + output);
    return costs;
}
var decisions = TypeDecisionCosts();
foreach (var outcome in new[] { "equal", "unequal" })
{
    long shortName = decisions[outcome + " 20"], longName = decisions[outcome + " 80"];
    var measured = $"{shortName} heartbeats at 20 characters and {longName} at 80";
    if (Math.Min(shortName, longName) < KernelDecisionFloor || Math.Max(shortName, longName) > TypeDecisionLimit ||
        longName > shortName * AllowedNameGrowth)
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Deciding {outcome} type identities costs {measured}; the limits are {TypeDecisionLimit} heartbeats " +
            $"and {AllowedNameGrowth} times as many at 80 characters."));
    Console.WriteLine($"PASS deciding {outcome} type identities costs {measured}");
}
MetadataNameCosts();
ModelTableCosts();

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
    var costs = LookupPatterns.MetadataNameCost().Matches(output).ToDictionary(
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
    int[] tableSizes = [16, 256];
    int[] siteCounts = [8, 32, 128];
    string[] positions = ["first", "middle", "last"];
    int Queried(string position, int size) => position switch { "first" => 0, "middle" => size / 2, _ => size - 1 };
    string Entries(int size) => string.Join(",\n  ", Enumerable.Range(0, size).Select(index =>
        $"ModelEntry.exact .call (method name!\"Model{index:D4}\") (.memory (.divRemOut {index}))"));
    string Table(int size) => $$"""
        /-- {{size}} modelled methods. -/
        def entries{{size}} : List ModelEntry := [
          {{Entries(size)}}]
        /-- Their literal table. -/
        def table{{size}} : ModelTable := model_table% entries{{size}}
        {{string.Join("\n", positions.Select(position => Lookup(position, size)))}}
        """;
    string Lookup(string position, int size) => $$"""
        #kernel_cost "model lookup {{position}} {{size}}"
          (table{{size}}.find {} .call (method name!"Model{{Queried(position, size):D4}}") =
            some (.memory (.divRemOut {{Queried(position, size)}})))
        """;
    string Emitted(int index) => $".memory (.divRemOut {index})";
    string Site(int index) =>
        $"⟨{index}, 40, .call {{ method := method name!\"Model{index:D4}\", target := .external \"\", " +
        "typeArguments := [], parameterCount := 0, returnsValue := true }⟩";
    string Sites(int count) => $$"""
        /-- {{count}} live calls of distinct modelled methods, the call at index i to method i. -/
        def raw{{count}} : RawMethod := { shell with code := [
          {{string.Join(",\n  ", Enumerable.Range(0, count).Select(Site))}}] }
        /-- The model each call emits. -/
        def code{{count}} : List Instruction :=
          [{{string.Join(", ", Enumerable.Range(0, count).Select(Emitted))}}]
        #kernel_cost "model agreement {{count}}"
          (ModelsAgree catalog {} .scalar raw{{count}} (List.replicate {{count}} true) code{{count}})
        """;
    var path = Path.Combine(tableDirectory, "ModelTables.lean");
    File.WriteAllText(path, $$"""
        import CIL.Extraction.RuntimeModels
        open CIL CIL.Extraction Lean Elab Command
        {{KernelCostCommand}}
        /-- A static method of no parameters named `name`. -/
        def method (name : MetadataName) : MethodRef :=
          { owner := .atom "Tests" "Models", name, hasThis := false, genericArity := 0, returnType := .void,
            parameters := [] }
        {{string.Join("\n", tableSizes.Select(Table))}}
        /-- The larger table, accounting for every `divRemOut` emission. -/
        def catalog : ModelCatalog where
          table := table256
          lowered
            | .memory (.divRemOut width) => some (.memory (.divRemOut width))
            | _ => none
        /-- A method shell whose code each fixture supplies. -/
        def shell : RawMethod :=
          { token := 0, owner := "", hasThis := false, explicitThis := false, callingConvention := 0,
            attributes := 0, implementation := 0, returnType := .void, parameters := [], locals := [],
            initLocals := true, maxStack := 1, genericParameters := [], code := [] }
        {{string.Join("\n", siteCounts.Select(Sites))}}
        """);
    var output = Run(["lake", "env", "lean", "-DElab.async=false", path], cwd: FixturePackage());
    var costs = LookupPatterns.ModelTableCost().Matches(output).ToDictionary(
        match => (match.Groups[1].Value, int.Parse(match.Groups[2].Value, CultureInfo.InvariantCulture)),
        match => long.Parse(match.Groups[3].Value, CultureInfo.InvariantCulture));
    if (costs.Count != positions.Length * tableSizes.Length + siteCounts.Length ||
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
    if (equations && Regex.Matches(output, @"_instruction[0-9]+' depends on axioms: \[propext\]").Count != 1)
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
    long[] readings = [.. HeartbeatCount().Matches(output)
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
    int last)
{
    var statement = $"example {binder}: {method}.code[{last}]? = some CIL.Instruction.ret";
    return Reported(path, text + $"""

        {statement} := {equation}
        {statement} := by simp only [cil_code]
        """);
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
    var namespaces = LookupPatterns.ExtractedNamespace().Matches(extracted).Count;
    var calls = LookupPatterns.CallsTheorem().Matches(extracted).Count;
    var evidence = LookupPatterns.EvidenceTheorem().Matches(extracted).Count;
    if (namespaces != 1 || calls != 1 || evidence != 1)
        throw new InvalidOperationException("Missing the namespace, call check or evidence theorem of method0.");
    var labelled = LookupPatterns.ExtractedNamespace().Replace(extracted, match => Command + match.Value);
    labelled = LookupPatterns.CallsTheorem().Replace(labelled,
        match => "#evidence_cost \"calls\" in\n" + match.Value);
    return LookupPatterns.EvidenceTheorem().Replace(labelled,
        match => "#evidence_cost \"assembly\" in\n" + match.Value);
}

// The heartbeats of the call check and of the evidence theorem that `WithEvidenceCosts` reports.
(long Calls, long Assembly) EvidenceCosts(string output)
{
    var costs = LookupPatterns.EvidenceCost().Matches(output).ToDictionary(match => match.Groups[1].Value,
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
    // The body decodes in full, so the extraction defines it from its decoder; the template still lists one
    // instruction per line after its header, and the hand-written body copies that code.
    const string Header =
        "@[cil_code] def method0 (profile : FeatureProfile) (environment : LayoutEnvironment) : Method := ";
    var definition = Regex.Match(templates, @"(?m)^" + Regex.Escape(Header) + @"[^\r\n]*(\r?\n  [^\r\n]*)+");
    var depth = Regex.Match(extracted, @"(?m)^set_option maxRecDepth [0-9]+");
    if (!definition.Success || !depth.Success ||
        !IsDecodedMethod(extracted, 0) ||
        !Regex.IsMatch(extracted, @"(?m)^cil_instruction_equations method0\r?$") ||
        !templates.Contains("cil_instruction_equations method0", StringComparison.Ordinal))
        throw new InvalidOperationException($"Missing the definition, equations or recursion depth of {name}.");
    var instructions = definition.Groups[1].Captures.Count;
    var last = instructions - 1;
    var extraction = Checked(Path.Combine(output, "Measured.lean"),
        WithEvidenceCosts(extracted) + $"\n#print axioms Extracted.method0_instruction{last}\n",
        "", "Extracted.method0", $"Extracted.method0_instruction{last}", last);
    const string Binder = "(profile : CIL.FeatureProfile) (environment : CIL.LayoutEnvironment) ";
    var body = "def method0 (profile : FeatureProfile) (environment : LayoutEnvironment) : Method := " +
        definition.Value[Header.Length..];
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
        $"Templates.method0_instruction{last} profile environment", last);
    return (instructions, [extraction.Count, command.Count, template.Count], EvidenceCosts(extraction.Output));
}

var imports = Path.Combine(directory, "Imports.lean");
var floor = Heartbeats(imports, "import CIL.Extraction.Translation\nimport CIL.SymbolicExecution\n" +
    "import CIL.Safety.Execution\nimport CIL.InstructionEquations\n", equations: false);
var brief = Measure("Short");
var extended = Measure("Long");
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

// A body with no call at three lengths. Its call check reads every pc's link by one walk, so it costs the same per
// instruction; its evidence theorem is assembled from the conjuncts' theorems and costs the same at every length.
// A conjunct stated through another term than `MethodEvidenceValid` states makes the assembly reduce the whole body.
var middleOutput = Path.Combine(directory, "Middle");
Run(Extract("extract", assembly, "Lookups", "Lookups::Middle(ulong,ulong)", middleOutput));
var middle = EvidenceCosts(Reported(Path.Combine(middleOutput, "Measured.lean"),
    WithEvidenceCosts(File.ReadAllText(Path.Combine(middleOutput, "Extracted.lean"))), equations: false).Output);
(int Statements, long Calls, long Assembly)[] evidenceSamples = [
    (ShortStatements, brief.Evidence.Calls, brief.Evidence.Assembly),
    (MiddleStatements, middle.Calls, middle.Assembly),
    (LongStatements, extended.Evidence.Calls, extended.Evidence.Assembly)];
var evidenceMeasured = string.Join("; ", evidenceSamples.Select(sample => string.Create(CultureInfo.InvariantCulture,
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

// The extraction of a body with many calls: its link table, key check, per-site facts and the checks that
// tie them together must each cost the same per call site at four times the size.
long CallingCost(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    return Heartbeats(Path.Combine(output, "Measured.lean"), File.ReadAllText(Path.Combine(output, "Extracted.lean")),
        equations: false);
}
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
    var cost = LookupPatterns.EmbeddingRecheck().Match(output);
    if (!cost.Success || cost.Groups[1].Value == "0")
        throw new InvalidOperationException("Missing the embedding recheck cost:\n" + output);
    return long.Parse(cost.Groups[2].Value, CultureInfo.InvariantCulture);
}

// The method every embedded call names; the link at its pc chooses the body it enters.
const string EmbeddedCallees = """
/-- A one-argument method whose result each segment pops. -/
def callee : Extraction.MethodRef :=
  { owner := .atom "Tests" "Embedded", name := name!"Callee", hasThis := false, genericArity := 0,
    returnType := .atom "Tests" "Word", parameters := [.atom "Tests" "Word"] }
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
CheckEmbeddingGrowth("Embedding", "a body with many calls", DeadBlocks, 1, EmbedFewCalls, EmbedManyCalls);
CheckEmbeddingGrowth("Reordered", "a body whose blocks the extraction reorders", Reordered, 2,
    ReorderFewSegments, ReorderManySegments);

// The text a method emits for its links and the kernel heartbeats to recheck that its table keys ascend, for a body
// with two calls: both depend on the calls, not on the length of the body.
(long Bytes, long Heartbeats) SparseLinkCost(string name)
{
    var output = Path.Combine(directory, name);
    Run(Extract("extract", assembly, "Lookups", $"Lookups::{name}(ulong,ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var linkLines = extracted.Split('\n').Where(line => LookupPatterns.LinkLine().IsMatch(line))
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
    var beats = LookupPatterns.KernelHeartbeats().Match(report);
    if (!beats.Success) throw new InvalidOperationException("Missing the link key recheck cost:\n" + report);
    return (linkLines, long.Parse(beats.Groups[1].Value, CultureInfo.InvariantCulture));
}
var sparseShort = SparseLinkCost("SparseShort");
var sparseLong = SparseLinkCost("SparseLong");
var sparseMeasured = $"{sparseShort.Bytes} link bytes and {sparseShort.Heartbeats} kernel heartbeats at " +
    $"{SparseShortStatements} statements, {sparseLong.Bytes} and {sparseLong.Heartbeats} at {SparseLongStatements}";
if (sparseLong.Bytes > sparseShort.Bytes * 1.1 || sparseLong.Heartbeats > sparseShort.Heartbeats * AllowedCallGrowth)
    throw new InvalidOperationException("A longer body with the same calls emits more link output: " + sparseMeasured);
Console.WriteLine("PASS link output and key check of a body with two calls do not grow with the body: " +
    sparseMeasured);

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
var fourCaseCost = ComputedLookupCost(4) / 4.0;
var sixteenCaseCost = ComputedLookupCost(16) / 16.0;
Console.WriteLine(FormattableString.Invariant(
    $"PASS computed lookup: {fourCaseCost:F0} heartbeats/case at 4; {sixteenCaseCost:F0} at 16"));
if (sixteenCaseCost > fourCaseCost * AllowedGrowth)
    throw new Exception("Computed lookup cost per case grows with the segment count.");

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
(double Total, double Calls) TokenCost(string name, string selector, int count, string distinctPattern)
{
    var output = Path.Combine(directory, "Tokens" + name);
    Run(Extract("extract", tokenAssembly, "Tokens", selector, output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var distinct = Regex.Matches(extracted, distinctPattern).Count;
    if (distinct < count)
        throw new InvalidOperationException($"Expected {count} distinct tokens in {name}; found {distinct}.");
    var report = Reported(Path.Combine(output, "Measured.lean"), WithEvidenceCosts(extracted), equations: false);
    return ((double)(report.Count - floor) / count, (double)EvidenceCosts(report.Output).Calls / count);
}
foreach (var (kind, few, many, pattern, fewCount, manyCount) in new[]
{
    ("Strings", "Tokens::StringsFew(ulong)", "Tokens::StringsMany(ulong)",
        @"\(\d+, \.text ""[^""]*""\)", FewTokens, ManyTokens),
    ("Fields", $"Tokens::FieldsFew(Tokens/Wide{FewTokens})", $"Tokens::FieldsMany(Tokens/Wide{ManyTokens})",
        @"\(\d+, \.field ", FewTokens, ManyTokens),
    ("Calls", "Tokens::CallsFew(ulong)", "Tokens::CallsMany(ulong)", @"\(\d+, \.call ", FewCalledMethods,
        ManyCalledMethods)
})
{
    var manyTokens = TokenCost(kind + "Many", many, manyCount, pattern);
    var fewTokens = TokenCost(kind + "Few", few, fewCount, pattern);
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
}

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
    var number = Regex.Match(extracted, @"def method(\d+)Signature : String := ""[^""]*Bodies::" +
        Regex.Escape(method) + @"\(").Groups[1].Value;
    return number.Length == 0
        ? throw new InvalidOperationException($"Method {method} is not in the extraction {name}.")
        : number;
}
// The heartbeats of the method's `method{n}_body_validated` and, for `tablesMethod`, of that method's
// `tables_valid`, read in one file of the extraction narrowed to the body obligation. Each is read after the same
// statement closed with `sorry`, which is subtracted.
(long Body, long Tables) BodyChecks(string name, string entry, string method, string? tablesMethod = null)
{
    var output = Path.Combine(directory, "Body" + name);
    Run(Extract("extract", bodyAssembly, "Bodies", entry.Contains('(') ? entry : $"Bodies::{entry}(ulong)", output));
    var extracted = File.ReadAllText(Path.Combine(output, "Extracted.lean"));
    var body = $"method{MethodNumber(extracted, method, name)}_body_validated";
    var narrowed = NarrowEvidence(extracted, body);
    var obligations = new List<(Match Proof, string Kind)> { (Obligation(narrowed, body, @"⟨[^\r\n]*⟩"), "body") };
    if (tablesMethod is not null)
        obligations.Add((Obligation(narrowed, $"method{MethodNumber(extracted, tablesMethod, name)}_tables_valid",
            @"by decide \+kernel"), "tables"));
    var parts = new List<string>();
    var readAt = new Dictionary<string, int>();
    var start = 0;
    foreach (var (proof, kind) in obligations.OrderBy(obligation => obligation.Proof.Index))
    {
        parts.Add(narrowed[start..proof.Index]);
        var statement = proof.Groups["statement"].Value;
        parts.Add($"theorem {proof.Groups["name"].Value}_open : {statement} := sorry\n");
        readAt[kind] = parts.Count - 1;
        parts.Add(proof.Value);
        start = proof.Index + proof.Length;
    }
    parts.Add(narrowed[start..]);
    var costs = PartHeartbeats(Path.Combine(output, "BodyChecked.lean"), parts);
    long Cost(string kind) => costs[readAt[kind]] - costs[readAt[kind] - 1];
    return (Cost("body"), tablesMethod is null ? 0 : Cost("tables"));
}
// The line of obligation `theorem` in `narrowed`, proved by a term matching `proof`.
static Match Obligation(string narrowed, string theorem, string proof)
{
    var line = Regex.Match(narrowed,
        @"(?m)^theorem (?<name>" + theorem + @") : (?<statement>[^\r\n]*?) := " + proof + @"\r?\n");
    return line.Success ? line : throw new InvalidOperationException("Missing obligation " + theorem);
}
long BodyCheck(string name, string entry, string method) => BodyChecks(name, entry, method).Body;
var chainCosts = chainLengths.Select(count => (double)BodyCheck("Chain" + count, "Chain" + count,
    $"Chain{count}_{count - 1}")).ToArray();
var rowChecks = bulkSizes.Select(count =>
    BodyChecks("Rows" + count, "Rows" + count, $"Small{count}", $"Bulk{count}")).ToArray();
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
    $"PASS body check of one method against {bulkSizes[0]} and {bulkSizes[1]} metadata rows: {rowGrowth:F2} times"));
if (rowGrowth > AllowedBodyGrowth)
    throw new Exception(FormattableString.Invariant(
        $"One body check costs {rowGrowth:F2} times as much against {bulkSizes[1]} rows ") +
        FormattableString.Invariant($"as against {bulkSizes[0]}; the limit is {AllowedBodyGrowth}."));
// The body check of a method of many string tokens costs the same per instruction at every size: numerals of its
// byte literal with equal low bytes would collide in the kernel's caches unless the literal is one joined code.
var stringCosts = stringTokenCounts.Select(count =>
    BodyCheck("Strings" + count, "Strings" + count, "Strings" + count) / (2.0 * count + 2)).ToArray();
for (var step = 1; step < stringCosts.Length; step++)
{
    var growth = stringCosts[step] / stringCosts[step - 1];
    Console.WriteLine(FormattableString.Invariant(
        $"PASS body check of a method of {stringTokenCounts[step - 1]} and {stringTokenCounts[step]} ") +
        FormattableString.Invariant($"string tokens: {stringCosts[step - 1]:F0} and {stringCosts[step]:F0} ") +
        FormattableString.Invariant($"heartbeats per instruction, {growth:F2} times"));
    if (growth > AllowedBodyGrowth)
        throw new Exception(FormattableString.Invariant(
            $"One body check costs {growth:F2} times as much per instruction at {stringTokenCounts[step]} string ") +
            FormattableString.Invariant(
                $"tokens as at {stringTokenCounts[step - 1]}; the limit is {AllowedBodyGrowth}."));
}
// The kernel's decision that a method's literal tables are the decoder's costs the rows that method carries, times a
// logarithm, and is made once per method.
var tablesFew = rowChecks[0].Tables;
var tablesMany = rowChecks[1].Tables;
var tablesGrowth = tablesMany / (double)tablesFew;
Console.WriteLine(FormattableString.Invariant(
    $"PASS tables check of a method carrying {bulkSizes[0]} and {bulkSizes[1]} user string rows: ") +
    FormattableString.Invariant($"{tablesFew} and {tablesMany} heartbeats, ") +
    FormattableString.Invariant($"{tablesGrowth / (bulkSizes[1] / (double)bulkSizes[0]):F2} times the cost per row"));
if (tablesGrowth > AllowedBodyGrowth * bulkSizes[1] / bulkSizes[0])
    throw new Exception(FormattableString.Invariant(
        $"The tables check costs {tablesGrowth:F2} times as much for {bulkSizes[1]} rows ") +
        FormattableString.Invariant($"as for {bulkSizes[0]}."));

// A method reading one field of a class with 10, 100 and 200 fields carries those field rows. Its body check does one
// lookup of the field's index, so it stays flat. Its tables check is a fixed part plus a part linear in the rows
// carried: the increment from 100 to 200 fields is 100/90 of the increment from 10 to 100, and a quadratic walk of the
// rows makes it more than three times as large.
const double AllowedFieldIncrementRatio = 1.5;
var fieldChecks = fieldCounts.Select(count => BodyChecks("Fields" + count,
    $"Bodies::Read{count}(Bodies/Wide{count})", $"Read{count}", $"Read{count}")).ToArray();
var fieldBody = fieldChecks.Select(check => (double)check.Body).ToArray();
var fieldTables = fieldChecks.Select(check => (double)check.Tables).ToArray();
var fieldBodyGrowth = fieldBody[^1] / fieldBody[0];
Console.WriteLine(FormattableString.Invariant(
    $"PASS body check of a method reading one of {fieldCounts[0]}, {fieldCounts[1]} and {fieldCounts[2]} fields: ") +
    FormattableString.Invariant($"{fieldBody[0]:F0}, {fieldBody[1]:F0} and {fieldBody[2]:F0} heartbeats, ") +
    FormattableString.Invariant($"{fieldBodyGrowth:F2} times"));
if (fieldBodyGrowth > AllowedBodyGrowth)
    throw new Exception(FormattableString.Invariant(
        $"The body check costs {fieldBodyGrowth:F2} times as much with {fieldCounts[2]} fields ") +
        FormattableString.Invariant($"as with {fieldCounts[0]}; the limit is {AllowedBodyGrowth}."));
var fieldIncrementRatio = (fieldTables[2] - fieldTables[1]) / (fieldTables[1] - fieldTables[0]);
Console.WriteLine(FormattableString.Invariant(
    $"PASS tables check of a method reading one of {fieldCounts[0]}, {fieldCounts[1]} and {fieldCounts[2]} fields: ") +
    FormattableString.Invariant($"{fieldTables[0]:F0}, {fieldTables[1]:F0} and {fieldTables[2]:F0} heartbeats, ") +
    FormattableString.Invariant($"increments in the ratio {fieldIncrementRatio:F2}"));
if (fieldIncrementRatio > AllowedFieldIncrementRatio)
    throw new Exception(FormattableString.Invariant(
        $"The tables check grows by {fieldIncrementRatio:F2} times as much from {fieldCounts[1]} to ") +
        FormattableString.Invariant(
            $"{fieldCounts[2]} fields as from {fieldCounts[0]} to {fieldCounts[1]}; ") +
        FormattableString.Invariant($"the limit is {AllowedFieldIncrementRatio}."));

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
              ⟨.atom CIL.Extraction.runtimeScope "System.Int32", [.atom CIL.Extraction.runtimeScope "System.Int32"]⟩
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
IndirectTargetCosts();

// A method reading a field declared `depth` base classes up carries one row and one link per class of the chain, and
// its body check walks the chain once. The cost is a fixed part plus a part linear in the depth, so the increment from
// depth 8 to 16 is twice the increment from 4 to 8; a quadratic walk makes it four times.
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
string Deep(int depth) =>
    $"public class Deep{depth}_0 {{ public ulong F; }} " +
    Join(depth, index => $"public class Deep{depth}_{index + 1} : Deep{depth}_{index} {{ }} ") +
    $"public static ulong ReadDeep{depth}(Deep{depth}_{depth} o) => o.F; ";
File.WriteAllText(Path.Combine(deepSource, "Deep.cs"),
    "public static class Bodies { " + string.Concat(baseDepths.Select(Deep)) + "}");
Run(["dotnet", "build", Path.Combine(deepSource, "Deep.csproj"), "-c", "Release"]);
bodyAssembly = Path.Combine(deepSource, "bin/Bodies.dll");
var depthCosts = baseDepths.Select(depth => (double)BodyCheck("Deep" + depth,
    $"Bodies::ReadDeep{depth}(Bodies/Deep{depth}_{depth})", $"ReadDeep{depth}")).ToArray();
var incrementRatio = (depthCosts[2] - depthCosts[1]) / (depthCosts[1] - depthCosts[0]);
Console.WriteLine(FormattableString.Invariant(
    $"PASS body check of a field read through {baseDepths[0]}, {baseDepths[1]} and {baseDepths[2]} base classes: ") +
    FormattableString.Invariant($"{depthCosts[0]:F0}, {depthCosts[1]:F0} and {depthCosts[2]:F0} heartbeats, ") +
    FormattableString.Invariant($"increments in the ratio {incrementRatio:F2} (linear 2, quadratic 4)"));
if (incrementRatio > AllowedChainIncrementRatio)
    throw new Exception(FormattableString.Invariant(
        $"The body check grows by {incrementRatio:F2} times as much from depth {baseDepths[1]} to {baseDepths[2]} ") +
        FormattableString.Invariant(
            $"as from {baseDepths[0]} to {baseDepths[1]}; the limit is {AllowedChainIncrementRatio}."));

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
        def intType : TypeExpr := .atom runtimeScope "System.Int32"
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
    var statement = $"ScalarFlowValid #[] (raw {flag} {sites}) (features {flag} {sites}) " +
        $"(states {flag} {sites}) (code {flag} {sites})";
    var path = Path.Combine(directory, $"ArrayAddresses{(prefixed ? "Prefixed" : "")}{sites}.lean");
    return DecideCost(path, header, statement, "ArrayAddresses");
}
foreach (var prefixed in new[] { false, true })
{
    var label = prefixed ? "readonly element addresses" : "element addresses";
    var perSite = new[] { FewAddresses, MoreAddresses, ManyAddresses }
        .Select(sites => (Sites: sites, Cost: (double)ArrayAddressCost(prefixed, sites) / sites)).ToArray();
    var addressesMeasured = string.Join("; ", perSite.Select(run =>
        string.Create(CultureInfo.InvariantCulture, $"{run.Cost:F0} kernel heartbeats per address at {run.Sites}")));
    if (perSite.Skip(1).Any(run => run.Cost > perSite[0].Cost * AllowedGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking the scalar certificate of {label} costs {addressesMeasured}; the limit is {AllowedGrowth} " +
            $"times the cost per address at {FewAddresses}."));
    Console.WriteLine($"PASS checking the scalar certificate of {label} costs {addressesMeasured}");
}
IndirectAccessCosts();

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
            def word : TypeExpr := .atom runtimeScope "System.UInt64"
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
                [.memory (.copyBlock (if prefixed then 1 else 8)), .br ((index + 1) * width prefixed)]
            def code (prefixed : Bool) (sites : Nat) : List Instruction :=
              (List.range sites).flatMap (codeSegment prefixed) ++ [.ret]
            """ + "\n";
        var statement = $"FeatureFlowValid #[] (fun _ => none) (fun _ => none) (raw {flag} {sites}) .scalar " +
            $"(features {flag} {sites}) ((features {flag} {sites}).map Option.isSome) (code {flag} {sites}) ∧ " +
            $"ScalarFlowValid #[] (raw {flag} {sites}) (features {flag} {sites}) (states {flag} {sites}) " +
            $"(code {flag} {sites})";
        var path = Path.Combine(accessDirectory, $"Blocks{(prefixed ? "Prefixed" : "")}{sites}.lean");
        return DecideCost(path, header, statement, "IndirectAccesses");
    }
    foreach (var prefixed in new[] { false, true })
    {
        var label = prefixed ? "unaligned block copies" : "block copies";
        var perSite = new[] { FewAddresses, MoreAddresses, ManyAddresses }
            .Select(sites => (Sites: sites, Cost: (double)Cost(prefixed, sites) / sites)).ToArray();
        var measured = string.Join("; ", perSite.Select(run =>
            string.Create(CultureInfo.InvariantCulture, $"{run.Cost:F0} kernel heartbeats per copy at {run.Sites}")));
        if (perSite.Skip(1).Any(run => run.Cost > perSite[0].Cost * AllowedGrowth))
            throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
                $"Checking the feature and scalar certificates of {label} costs {measured}; the limit is " +
                $"{AllowedGrowth} times the cost per copy at {FewAddresses}."));
        Console.WriteLine($"PASS checking the feature and scalar certificates of {label} costs {measured}");
    }
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
        def intType : TypeExpr := .atom runtimeScope "System.Int32"
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
// The kernel heartbeats of a check over a body that stores each of its locals once and then loads or addresses
// it, less those of stating the same check. Integer locals take a constant and are popped after a load or after
// `ldloca`; native-int locals take a method address and are
// consumed by `calli`, which makes each a pointer local. The check is the scalar certificate, or for pointer
// locals also the closed argument storage. Instructions carry byte offsets.
long LocalSlotCost(LocalSlots slots, int count, bool storage = false)
{
    var pointers = slots == LocalSlots.Pointer;
    var addressed = slots == LocalSlots.Addressed;
    var slotType = pointers ? "System.IntPtr" : "System.Int32";
    var kind = pointers ? ".methodPointer signature" : ".word32";
    var push = pointers ? "65030, .call handler" : "22, .none";
    var load = addressed ? "18, .local index" : "17, .local index";
    var consume = pointers ? "41, .indirectCall .void [] false false 0" : "38, .none";
    // ldftn and calli carry a four-byte token; ldc.i4.0 and pop are one byte, and the local forms two.
    var pushBytes = pointers ? 6 : 1;
    var consumeBytes = pointers ? 5 : 1;
    var loaded = addressed ? ".reference" : "kind";
    var pushed = pointers ? ".managed (.address ⟨⟨\"Scaling\", 2, []⟩, 0⟩ signature)" : ".ldc_i4 0";
    var emittedLoad = addressed ? ".ldloca index" : ".ldloc index";
    var consumed = pointers ? ".managed (.call signature [] false)" : ".pop";
    var header = $$"""
        import CIL.Extraction.Scalars
        set_option maxRecDepth 100000
        set_option maxHeartbeats 0
        namespace LocalSlots
        open CIL CIL.Extraction
        def slotType : TypeExpr := .atom runtimeScope "{{slotType}}"
        def handler : CallSite :=
          { method := {
              owner := .void, name := name!"", hasThis := false, genericArity := 0,
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
        : $"ScalarFlowValid #[] (raw {count}) (features {count}) (states {count}) (code {count})";
    var path = Path.Combine(directory, $"{slots}{(storage ? "Storage" : "Locals")}{count}.lean");
    return DecideCost(path, header, statement, "LocalSlots");
}
(LocalSlots Slots, bool Storage, string Label)[] localChecks =
[
    (LocalSlots.Integer, false, "the scalar certificate of integer locals"),
    (LocalSlots.Addressed, false, "the scalar certificate of addressed integer locals"),
    (LocalSlots.Pointer, false, "the scalar certificate of native-int locals consumed by calli"),
    (LocalSlots.Pointer, true, "the closed argument storage of native-int locals consumed by calli"),
];
foreach (var (slots, storage, label) in localChecks)
{
    // Each local is stored once and loaded or addressed once, between a push and a pop or call; `ret` ends the body.
    var perInstruction = new[] { FewLocals, MoreLocals, ManyLocals }
        .Select(count => (Count: count, Cost: (double)LocalSlotCost(slots, count, storage) / (4 * count + 1)))
        .ToArray();
    var localsMeasured = string.Join("; ", perInstruction.Select(run => string.Create(CultureInfo.InvariantCulture,
        $"{run.Cost:F0} kernel heartbeats per instruction at {run.Count} locals")));
    if (perInstruction.Skip(1).Any(run => run.Cost > perInstruction[0].Cost * AllowedLocalGrowth))
        throw new InvalidOperationException(string.Create(CultureInfo.InvariantCulture,
            $"Checking {label} costs {localsMeasured}; the limit is {AllowedLocalGrowth} " +
            $"times the cost per instruction at {FewLocals} locals."));
    Console.WriteLine($"PASS checking {label} costs {localsMeasured}");
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
        def intType : TypeExpr := .atom runtimeScope "System.Int32"
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
        def intType : TypeExpr := .atom runtimeScope "System.Int32"
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
    [GeneratedRegex(@"\bevidence (calls|assembly) ([0-9]+) heartbeats")]
    internal static partial Regex EvidenceCost();

    [GeneratedRegex(@"(?m)^namespace Extracted\r?$")]
    internal static partial Regex ExtractedNamespace();

    [GeneratedRegex(@"(?m)^theorem method0_calls_validated ")]
    internal static partial Regex CallsTheorem();

    [GeneratedRegex(@"(?m)^theorem method0_evidence_validated ")]
    internal static partial Regex EvidenceTheorem();

    [GeneratedRegex(@"closed arguments [0-9]+ [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex ClosedArguments();

    [GeneratedRegex(@"resolution (fact|simplifier) ([0-9]+) heartbeats")]
    internal static partial Regex ReturnResolution();

    [GeneratedRegex(@"static identities ([0-9]+) heartbeats")]
    internal static partial Regex StaticIdentities();

    [GeneratedRegex(@"call check ([0-9]+) heartbeats")]
    internal static partial Regex CallCheck();

    [GeneratedRegex(@"lineage (rejected|located) ([0-9]+) heartbeats")]
    internal static partial Regex Lineage();

    [GeneratedRegex(@"([0-9]+) lemmas rechecked, ([0-9]+) kernel heartbeats")]
    internal static partial Regex EmbeddingRecheck();

    [GeneratedRegex(@"([0-9]+) kernel heartbeats")]
    internal static partial Regex KernelHeartbeats();

    [GeneratedRegex(@"^@\[cil_code\] def method0Link")]
    internal static partial Regex LinkLine();

    [GeneratedRegex(@"\b((?:un)?equal [0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex TypeDecision();

    [GeneratedRegex(@"\bname spells ([0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex MetadataNameCost();

    [GeneratedRegex(@"\bmodel (lookup first|lookup middle|lookup last|agreement) ([0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex ModelTableCost();

    [GeneratedRegex(@"\b((?:thrownEqual|thrownUnequal|clrUnequal|raisesEqual) [A-Za-z]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex ExceptionDecision();

    [GeneratedRegex(@"table step [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex NativeTableStep();

    [GeneratedRegex(@"table load first [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex NativeTableLoadFirst();

    [GeneratedRegex(@"table load last [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex NativeTableLoadLast();

    [GeneratedRegex(@"decode [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex ValueDecoding();

    [GeneratedRegex(@"decoded method [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex DecodedMethod();

    [GeneratedRegex(@"decoded definition [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex DecodedDefinition();

    [GeneratedRegex(@"prefix entry [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex PrefixEntry();

    [GeneratedRegex(@"decoded program [0-9]+ (-?[0-9]+) heartbeats")]
    internal static partial Regex DecodedProgram();

    [GeneratedRegex(@"\bclosure (chain|fan|tail) ([0-9]+) (-?[0-9]+) heartbeats")]
    internal static partial Regex ClosureCost();
}
