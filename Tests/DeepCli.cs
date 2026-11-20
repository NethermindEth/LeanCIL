#!/usr/bin/env dotnet
#:property PublishAot=false
#:include ../scripts/Verification.cs
#:include ../scripts/DeepChecks.cs
#:include ../scripts/FailureReports.cs
#:include ../scripts/LeanDiagnostics.cs
#:include ../scripts/BindingImage.cs
#:include ../scripts/DeepCheckInputs.cs
#:include MultiAssemblyFixture.cs
#:include DeepBinding.cs

using System.Reflection;
using System.Reflection.Metadata;
using System.Reflection.Metadata.Ecma335;
using System.Reflection.PortableExecutable;
using System.Text.Json;

using Program preparation = new();
preparation.EnsureExtractorBuilt();
MultiAssemblyFixture fixture = new("DeepCli");
var cli = args is [var executable] && !executable.StartsWith("--", StringComparison.Ordinal)
    ? new[] { Path.GetFullPath(executable) } : fixture.Cli;
const string libName = "DeepCli.Library";
var lib = fixture.Build("Library", libName,
    "namespace MultiFixture; public static class Mix { public static ulong Step(ulong x) => x * 3 + 1; }");
var app = fixture.Build("Application", "DeepCli.Application",
    "namespace MultiFixture; public static class Application { " +
        "public static ulong Direct(ulong x) => Mix.Step(x) + 1; }",
    references: $"<Reference Include=\"{libName}\"><HintPath>{lib}</HintPath></Reference>");
var output = fixture.Artifact("Direct");
Run([.. cli, "extract", app, "MultiFixture.Application::Direct(System.UInt64)", output, "--reference", lib]);
var proof = At("Tests/MultiAssembly/Direct.lean");
string[] verify = [.. cli, "verify", output, "--proof", proof, "--theorem", "MultiAssemblyProof.correctness"];
var digestFile = Path.Combine(fixture.Root, "inputs.sha256");
var digests = Sha(app) + "  " + Path.GetRelativePath(fixture.Root, app) + "\n" +
    Sha(lib) + "  " + Path.GetRelativePath(fixture.Root, lib) + "\n";
File.WriteAllText(digestFile, digests);

// Each fixture carries the actual platform identity and public key. A forwarded object has an
// ExportedType and an AssemblyRef. A defined object has one physical Field row.
static void WritePlatformImage(string path, AssemblyName name, FieldAttributes field, AssemblyName? forward = null)
{
    var rows = new MetadataBuilder();
    rows.AddModule(0, rows.GetOrAddString(name.Name + ".dll"), rows.GetOrAddGuid(Guid.Empty), default, default);
    rows.AddAssembly(rows.GetOrAddString(name.Name!), name.Version!, default,
        rows.GetOrAddBlob(name.GetPublicKey()!), AssemblyFlags.PublicKey, AssemblyHashAlgorithm.Sha1);
    var firstField = MetadataTokens.FieldDefinitionHandle(1);
    var firstMethod = MetadataTokens.MethodDefinitionHandle(1);
    rows.AddTypeDefinition(default, default, rows.GetOrAddString("<Module>"), default, firstField, firstMethod);
    var system = rows.GetOrAddString("System");
    var objectName = rows.GetOrAddString("Object");
    if (forward is null)
    {
        rows.AddTypeDefinition(TypeAttributes.Public, system, objectName, default, firstField, firstMethod);
        var signature = new BlobBuilder();
        new BlobEncoder(signature).Field().Type().Int32();
        rows.AddFieldDefinition(field, rows.GetOrAddString("Value"), rows.GetOrAddBlob(signature));
    }
    else
    {
        var target = rows.AddAssemblyReference(rows.GetOrAddString(forward.Name!), forward.Version!, default,
            rows.GetOrAddBlob(forward.GetPublicKeyToken()!), default, default);
        const TypeAttributes forwarder = (TypeAttributes)0x00200000;
        rows.AddExportedType(forwarder, system, objectName, target, 0);
    }
    var builder = new ManagedPEBuilder(PEHeaderBuilder.CreateLibraryHeader(),
        new MetadataRootBuilder(rows), new BlobBuilder());
    var bytes = new BlobBuilder();
    builder.Serialize(bytes);
    File.WriteAllBytes(path, bytes.ToArray());
}

void CheckPlatformObject()
{
    var runtime = Assembly.Load("System.Runtime").GetName();
    var core = typeof(object).Assembly.GetName();
    var reference = Path.Combine(fixture.Root, "reference-image.dll");
    var definition = Path.Combine(fixture.Root, "definition.dll");
    var previous = Path.Combine(fixture.Root, "previous-version.dll");

    void Check(string expected, params (string File, AssemblyName Name)[] platforms)
    {
        var extra = File.Exists(previous) ? Sha(previous) + "  " + Path.GetFileName(previous) + "\n" : "";
        File.WriteAllText(digestFile, digests + extra + string.Concat(platforms.Select(p =>
            Sha(p.File) + "  " + Path.GetFileName(p.File) + "\n")));
        var result = Execute([.. verify, "--deep-checks", digestFile, "--format", "json"]);
        if (expected == "failed")
        {
            if (result.Code == 0 || File.Exists(Path.Combine(output, "verified.json")))
                throw new InvalidOperationException("The changed platform definition was certified.");
            var failure = JsonSerializer.Deserialize<JsonElement>(result.Stdout).GetProperty("binding");
            var rejected = failure.GetProperty("facts").EnumerateArray()
                .Single(f => f.GetProperty("id").GetString() == "object-fields");
            if (rejected.GetProperty("status").GetString() != "failed" ||
                !rejected.GetProperty("reason").GetString()!.Contains("instance field 0x04000001", StringComparison.Ordinal))
                throw new InvalidOperationException("Expected the physical field diagnostic: " + result.Output);
            return;
        }
        if (result.Code != 0) throw new InvalidOperationException(result.Output);
        var binding = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "verified.json")))
            .GetProperty("binding");
        var fact = binding.GetProperty("facts").EnumerateArray()
            .Single(f => f.GetProperty("id").GetString() == "object-fields");
        if (fact.GetProperty("status").GetString() != expected ||
            fact.GetProperty("theorem").GetString() != (expected == "reconfirmed" ? "BindingAudit.objectFields" : null))
            throw new InvalidOperationException("Incorrect object-fields certificate: " + fact);
        if (File.Exists(previous))
        {
            var unused = binding.GetProperty("images").EnumerateArray()
                .Single(i => i.GetProperty("sha256").GetString() == Sha(previous));
            if (unused.GetProperty("role").GetString() != "unused")
                throw new InvalidOperationException("The facade selected the wrong version: " + unused);
        }
        foreach (var (file, assembly) in platforms)
        {
            var image = binding.GetProperty("images").EnumerateArray()
                .Single(i => i.GetProperty("identity").GetString() == assembly.FullName);
            if (image.GetProperty("role").GetString() != "platform" ||
                image.GetProperty("sha256").GetString() != Sha(file) ||
                image.GetProperty("status").GetString() != "reconfirmed")
                throw new InvalidOperationException("Incorrect platform image: " + image);
        }
    }

    WritePlatformImage(reference, runtime, FieldAttributes.Static);
    Check("reconfirmed", (reference, runtime));
    Console.WriteLine("PASS the exact platform reference permits a static field on System.Object");
    WritePlatformImage(reference, runtime, default, core);
    var older = typeof(object).Assembly.GetName();
    older.Version = new Version(core.Version!.Major - 1, 0, 0, 0);
    WritePlatformImage(previous, older, FieldAttributes.Public);
    Check("not covered", (reference, runtime));
    Console.WriteLine("PASS a facade with only an older destination leaves System.Object fields uncovered");
    WritePlatformImage(definition, core, FieldAttributes.Static);
    Check("reconfirmed", (reference, runtime), (definition, core));
    Console.WriteLine("PASS the platform facade resolves System.Object in its exact destination");
    WritePlatformImage(definition, core, FieldAttributes.Public);
    Check("failed", (reference, runtime), (definition, core));
    Console.WriteLine("PASS a rehashed instance field in the forwarded definition fails the object-fields check");
    File.WriteAllText(digestFile, digests);
}

if (args is ["--platform"])
{
    CheckPlatformObject();
    return;
}

void Refused(string name, string[] command, string? expectedStage = null)
{
    var result = Execute(command);
    if (result.Code == 0) throw new InvalidOperationException(name + " was accepted");
    if (expectedStage is not null)
    {
        var report = JsonSerializer.Deserialize<JsonElement>(result.Stdout);
        if (report.GetProperty("stage").GetString() != expectedStage ||
            report.GetProperty("binding").ValueKind != JsonValueKind.Null)
            throw new InvalidOperationException(name + " has the wrong failure boundary: " + result.Output);
    }
    Console.WriteLine("PASS " + name);
}

// The deep checks run only as an option of verify, so a command name that is not one of the listed commands
// is a usage error that runs nothing, whatever it is called.
void RefusedAsUnknownCommand(string[] cli, string output, string digestFile)
{
    foreach (var name in new[] { "audit" + "-binding", "audit", "binding-audit", "strict-binding", "deep-checks",
                 "deep", "verify-deep", "audit-deep" })
    {
        var result = Execute([.. cli, name, output, "--deep-checks", digestFile]);
        if (result.Code == 0 || !result.Output.Contains("Stage: arguments", StringComparison.Ordinal) ||
            !result.Output.Contains("Usage: leancil", StringComparison.Ordinal) ||
            result.Output.Contains("Binding:", StringComparison.Ordinal) ||
            result.Output.Contains("BindingAudit", StringComparison.Ordinal) ||
            result.Output.Contains("StrictBinding", StringComparison.Ordinal))
            throw new InvalidOperationException(name + " was not refused as an unknown command: " + result.Output);
    }
    Console.WriteLine("PASS unknown audit command names");
}

// The help text lists the deep checks only as an option of verify. The one audit command, audit-library, checks
// the theorems of a Lean library and runs no binding check.
void RequireNoSeparateAudit(string[] cli)
{
    var help = Execute([.. cli, "--help"]);
    // A command's usage wraps onto indented lines that do not start with `leancil`; each belongs to the command above.
    var commands = help.Stdout.ReplaceLineEndings("\n").Split('\n')
        .Aggregate(new List<string>(), (joined, raw) =>
        {
            var line = raw.Trim().StartsWith("Usage: ", StringComparison.Ordinal) ? raw.Trim()["Usage: ".Length..]
                : raw.Trim();
            if (line.StartsWith("leancil ", StringComparison.Ordinal)) joined.Add(line);
            else if (line.Length > 0 && raw.StartsWith(' ') && joined.Count > 0) joined[^1] = $"{joined[^1]} {line}";
            return joined;
        }).ToArray();
    var names = commands.Select(line => line.Split(' ')[1])
        .Where(name => !name.StartsWith("--", StringComparison.Ordinal)).ToArray();
    var audits = names.Where(name => name.Contains("audit", StringComparison.OrdinalIgnoreCase)).ToArray();
    var deepLines = commands.Where(line => line.Contains("--deep-checks", StringComparison.Ordinal)).ToArray();
    if (help.Code != 0 || !names.Contains("verify") || !audits.SequenceEqual(["audit-library"]) ||
        deepLines.Length != 1 || !deepLines[0].StartsWith("leancil verify ", StringComparison.Ordinal) ||
        help.Stdout.Contains("binding audit", StringComparison.OrdinalIgnoreCase))
        throw new InvalidOperationException("The help text names a separate audit entry: " + help.Output);
    Console.WriteLine("PASS help names no separate audit command");
}

if (args is not (["--consumer"] or ["--mutations"] or ["--controls"] or ["--final-mutations"]))
{
    Refused("missing digest option value", [.. verify, "--format", "json", "--deep-checks"], "arguments");
    Refused("duplicate digest option", [.. verify, "--format", "json", "--deep-checks", digestFile,
        "--deep-checks", digestFile], "arguments");
    Refused("missing digest file", [.. verify, "--deep-checks", digestFile + ".missing", "--format", "json"],
        "arguments");
    foreach (var content in new[] { "malformed\n", new string('0', 64) + "  " + app + "\n",
        Sha(app) + "  " + app + "\n" })
    {
        File.WriteAllText(digestFile, content);
        Refused("invalid or missing image digest", [.. verify, "--deep-checks", digestFile, "--format", "json"],
            "arguments");
    }
    File.WriteAllBytes(digestFile, [0xff]);
    Refused("invalid UTF-8 digest file", [.. verify, "--deep-checks", digestFile, "--format", "json"], "arguments");
    File.WriteAllText(digestFile, digests);
    foreach (var command in new[] { "verify-batch", "gates", "watch", "workspace", "check", "audit-library" })
        Refused(command + " rejects deep option", [.. cli, command, output, "--deep-checks", digestFile]);
    RefusedAsUnknownCommand(cli, output, digestFile);
    RequireNoSeparateAudit(cli);
    Refused("invalid proof root", [.. verify, "--proof-root", fixture.Root + ".missing", "--deep-checks",
        digestFile, "--format", "json"], "extraction integrity");
    File.Delete(Path.Combine(output, "verification.json"));
    if (args is ["--arguments"]) return;

    var ordinary = Execute(verify);
    if (ordinary.Code != 0 || !ordinary.Stdout.Contains("Binding: default", StringComparison.Ordinal) ||
        ordinary.Stdout.Split(": trusted", StringSplitOptions.None).Length != 13 ||
        ordinary.Output.Contains("BindingAudit", StringComparison.Ordinal))
        throw new InvalidOperationException("Default binding output or work changed: " + ordinary.Output);
    var deep = Execute([.. verify, "--deep-checks", digestFile]);
    string[] reconfirmed = ["body-bytes", "metadata-rows", "static-data"];
    if (deep.Code != 0 || !deep.Stdout.Contains("StrictBinding sources:", StringComparison.Ordinal) ||
        deep.Stdout.Split(": not covered", StringSplitOptions.None).Length != 10)
        throw new InvalidOperationException("Deep binding text is incomplete: " + deep.Output);
    string[] factNames =
    [
        "body-bytes", "metadata-rows", "platform-type-kinds", "enum-underlying-types", "value-tuple-field-order",
        "object-fields", "layout-content", "dispatch-catalogs", "static-data", "generic-constraints",
        "public-key-tokens", "import-identities"
    ];
    foreach (var fact in factNames)
        if (!ordinary.Stdout.Contains(fact + ": trusted", StringComparison.Ordinal) ||
            !deep.Stdout.Contains(fact + (reconfirmed.Contains(fact) ? ": reconfirmed" : ": not covered"),
                StringComparison.Ordinal))
            throw new InvalidOperationException("Binding text omitted wire name " + fact);
    Console.WriteLine("PASS default and deep binding text");
    CheckPlatformObject();

    var tables = fixture.Build("Table", "DeepCli.Table", """
        public static class Table {
            static System.ReadOnlySpan<uint> Words => [11, 13, 17, 19, 23, 29, 31, 37];
            public static uint Third() => Words[2];
        }
        """);
    var tableOutput = fixture.Artifact("Third");
    Run([.. cli, "extract", tables, "Table::Third()", tableOutput]);
    var tableDigest = Path.Combine(fixture.Root, "table.sha256");
    File.WriteAllText(tableDigest, Sha(tables) + "  " + Path.GetRelativePath(fixture.Root, tables) + "\n");
    var tableProof = Path.Combine(fixture.Root, "Third.lean");
    File.WriteAllText(tableProof, """
        import Extracted
        import CIL.Safety.Execution

        open CIL CIL.Safety
        namespace ExampleProof

        example : Extracted.methodEvidence.any (fun item => item.closed.staticFields.any
            (fun site => site.2.rvaSize == some 32)) = true := by decide +kernel

        theorem correctness : (invoke Extracted.program 64 0 [] Memory.empty).map Prod.snd =
            .ok [.scalar (.i32 17)] := by rfl
        #print axioms correctness
        end ExampleProof

        """);
    Run([.. cli, "verify", tableOutput, "--proof", tableProof, "--deep-checks", tableDigest]);
    var binding = JsonSerializer.Deserialize<JsonElement>(
        File.ReadAllText(Path.Combine(tableOutput, "verified.json"))).GetProperty("binding");
    var data = binding.GetProperty("facts").EnumerateArray().Single(fact =>
        fact.GetProperty("id").GetString() == "static-data");
    if (data.GetProperty("status").GetString() != "reconfirmed" ||
        data.GetProperty("theorem").GetString() != "BindingAudit.staticData")
        throw new InvalidOperationException("The compiled table has no audited physical-data theorem.");
    Console.WriteLine("PASS the third word comes from a 32-byte RVA field in the pinned table assembly");

    Run(["lake", "build", "StrictBinding.StaticData"], preparation.CheckoutPackage());
    var leanPath = tableOutput + Path.PathSeparator + preparation.CheckoutLeanPath();
    File.WriteAllText(Path.Combine(tableOutput, "RvaImage.lean"),
        "import StrictBinding.Image\nimport CIL.Extraction.FixedDigits\nnamespace RvaImage\n" +
        BindingImage.Definitions(File.ReadAllBytes(tables)) + "\nend RvaImage\n");
    File.Copy(At("Tests/StrictBinding/StaticSiteCases.lean"), Path.Combine(tableOutput, "StaticSiteCases.lean"), true);
    string[] modules = ["Extracted", "RvaImage", "StaticSiteCases"];
    foreach (var module in modules)
    {
        var log = Run([preparation.LeanExecutable, "--root=" + tableOutput, "-o",
            Path.Combine(tableOutput, module + ".olean"), Path.Combine(tableOutput, module + ".lean")],
            leanPath: leanPath);
        if (log.Contains("sorryAx", StringComparison.Ordinal))
            throw new InvalidDataException(module + " depends on sorryAx");
    }
    preparation.ReplayCheckedModules(modules, leanPath, "Kernel replay of static field descriptor checks");
    Console.WriteLine("PASS the pinned FieldRVA rejects a matching prefix, changed bytes and a missing RVA marker");
}
if (args is ["--text"]) return;
if (args is ["--mutations"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify);
if (args is ["--controls"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify, controlsOnly: true);
if (args is ["--final-mutations"])
    CheckDeepBinding(fixture.Root, cli, output, app, lib, libName, verify, finalOnly: true);
if (args is not (["--mutations"] or ["--controls"] or ["--final-mutations"]))
{
    var package = Path.Combine(fixture.Root, "Consumer");
    Directory.CreateDirectory(package);
    var revision = Run(["git", "rev-parse", "HEAD"], Root).Trim();
    File.WriteAllText(Path.Combine(package, "lakefile.toml"), $"""
        name = "deep_cli_consumer"
        [[require]]
        name = "leancil"
        git = {JsonSerializer.Serialize(Root.Replace('\\', '/'))}
        rev = "{revision}"
        """);
    File.Copy(At("lean-toolchain"), Path.Combine(package, "lean-toolchain"));
    var consumerProof = Path.Combine(package, "Proof.lean");
    File.Copy(proof, consumerProof);
    Run(["lake", "update"], package);
    string[] consumer = [.. cli, "verify", output, "--proof", consumerProof, "--theorem",
        "MultiAssemblyProof.correctness", "--proof-root", package, "--deep-checks", digestFile, "--format", "json"];
    var checkedConsumer = Execute(consumer);
    if (checkedConsumer.Code != 0) throw new InvalidOperationException(checkedConsumer.Output);
    var consumerReport = JsonSerializer.Deserialize<JsonElement>(checkedConsumer.Stdout);
    var binding = consumerReport.GetProperty("binding");
    if (binding.GetProperty("mode").GetString() != "deep" ||
        binding.GetProperty("facts").GetArrayLength() != 12 ||
        binding.GetProperty("facts")[0].GetProperty("status").GetString() != "reconfirmed")
        throw new InvalidOperationException("Consumer CLI did not retain deep binding");
    Console.WriteLine("PASS proof-root CLI deep verification");
    File.WriteAllText(consumerProof,
        "import Extracted\nnamespace MultiAssemblyProof\ntheorem correctness : False := by exact True.intro\n" +
        "end MultiAssemblyProof\n");
    var rejected = Execute(consumer);
    if (rejected.Code == 0 || File.Exists(Path.Combine(output, "verified.json")))
        throw new InvalidOperationException("Rejected consumer proof published a certificate");
    var failed = JsonSerializer.Deserialize<JsonElement>(rejected.Stdout);
    var failedFile = JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(Path.Combine(output, "failed.json")));
    var failureBinding = failed.GetProperty("binding");
    if (!JsonElement.DeepEquals(failureBinding, failedFile.GetProperty("binding")) ||
        failureBinding.GetProperty("facts").GetArrayLength() != 12 ||
        failureBinding.GetProperty("facts").EnumerateArray().Any(fact =>
            fact.GetProperty("status").GetString() != "not covered"))
        throw new InvalidOperationException("Failed consumer binding payload is inconsistent: " + rejected.Output);
    Console.WriteLine("PASS failed.json and JSON retain the same incomplete deep attempt");
}
