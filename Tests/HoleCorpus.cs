#!/usr/bin/env dotnet
#:property PublishAot=false
#:property AssemblyName=LeanCIL.IdentityTests
#:project ../Extractor/Extractor.csproj
#:package Mono.Cecil

extern alias IdentityExtractor;

using System.Diagnostics;
using System.Runtime.CompilerServices;
using System.Security.Cryptography;
using System.Text.Json;
using Mono.Cecil;
using Mono.Cecil.Cil;
using IdentityExtractor::Nethermind.LeanCIL;

// Dead instructions in the admitted scalar self-admission corpus, including compiler-generated bodies.
const string Usage = "Usage: HoleCorpus.cs [--update] [--baseline path] [--admission-report path]";
const string Profile = "scalar";
var root = Path.GetFullPath(Path.Combine(Path.GetDirectoryName(Source())!, ".."));
var baselinePath = Path.Combine(root, "Tests/HoleCorpusBaseline.txt");
string? admissionReport = null;
var update = false;
for (var index = 0; index < args.Length; index++)
    switch (args[index])
    {
        case "--update": update = true; break;
        case "--baseline" when index + 1 < args.Length: baselinePath = Path.GetFullPath(args[++index]); break;
        case "--admission-report" when index + 1 < args.Length:
            admissionReport = Path.GetFullPath(args[++index]);
            break;
        default: throw new ArgumentException(Usage);
    }

CheckInspection();
CheckRefusalReport();
CheckUndecodedCallee(Path.Combine(root, "Extractor/bin/Nethermind.LeanCIL.dll"));
var timer = Stopwatch.StartNew();
var assemblyPath = Path.Combine(root, "Extractor/bin/Nethermind.LeanCIL.dll");
var bytes = File.ReadAllBytes(assemblyPath);
var hash = Convert.ToHexStringLower(SHA256.HashData(bytes));
using var pinned = new PinnedAssemblies(bytes, hash, []);
var methods = pinned.Selected.GetTypes().SelectMany(type => type.Methods)
    .ToDictionary(method => method.FullName, StringComparer.Ordinal);
var directory = Path.Combine(root, "artifacts/HoleCorpus");
Directory.CreateDirectory(directory);
if (admissionReport is null)
{
    var manifest = Path.Combine(directory, "manifest.json");
    File.WriteAllText(manifest, JsonSerializer.Serialize(new
    {
        entries = methods.Keys.Order(StringComparer.Ordinal).Select(signature => new { signature, profile = Profile })
    }));
    admissionReport = Path.Combine(directory, "blockers.json");
    if (Blockers.Run([assemblyPath, "--manifest", manifest, "--output", admissionReport]) != 0)
        throw new InvalidOperationException("Corpus admission failed.");
}

using var document = JsonDocument.Parse(File.ReadAllText(admissionReport));
var report = document.RootElement;
var extractorBytes = File.ReadAllBytes(typeof(FeatureProfile).Assembly.Location);
var extractorHash = Convert.ToHexStringLower(SHA256.HashData(extractorBytes));
if (report.GetProperty("assemblySha256").GetString() != hash ||
    report.GetProperty("extractorSha256").GetString() != extractorHash ||
    report.GetProperty("initializedTypes").GetArrayLength() != 0)
    throw new InvalidDataException("Admission report does not match the corpus assembly, extractor or assumptions.");
var results = new List<MethodHoles>();
var seen = new HashSet<string>(StringComparer.Ordinal);
var skipped = 0;
foreach (var entry in report.GetProperty("entries").EnumerateArray())
{
    var signature = entry.GetProperty("signature").GetString()!;
    if (!seen.Add(signature) || !methods.TryGetValue(signature, out var method) ||
        entry.GetProperty("profile").GetString() != Profile ||
        entry.GetProperty("typeArguments").GetArrayLength() != 0)
        throw new InvalidDataException("Unexpected corpus admission entry: " + signature);
    switch (entry.GetProperty("status").GetString())
    {
        case "admitted": results.Add(Inspect(method)); break;
        case "blocked" or "notChecked": skipped++; break;
        default: throw new InvalidDataException("Unexpected admission status for " + signature);
    }
}
if (seen.Count != methods.Count)
    throw new InvalidDataException($"Admission report covers {seen.Count} of {methods.Count} methods.");

File.WriteAllText(Path.Combine(directory, "methods.json"),
    JsonSerializer.Serialize(new { skipped, methods = results }, new JsonSerializerOptions { WriteIndented = true }));
// A corpus with no admitted method would pass with nothing inspected.
if (results.Count == 0)
    throw new InvalidDataException("The admission report admits no corpus method, so no body was inspected.");
string[] rows = [.. results.SelectMany(Rows).Order(StringComparer.Ordinal)];
if (update) File.WriteAllText(baselinePath, string.Concat(rows.Select(row => row + "\n")));
var baseline = File.ReadAllLines(baselinePath).Where(line => line.Length != 0).ToArray();
var removed = baseline.Except(rows, StringComparer.Ordinal).ToArray();
var added = rows.Except(baseline, StringComparer.Ordinal).ToArray();
var homes = results.Count(result => result.Arguments.Length != 0);
var prefixes = results.Sum(result => result.Prefixes.Length);
Console.WriteLine($"{results.Count} admitted methods; {skipped} skipped refused methods; " +
    $"{homes} home differences; {prefixes} dead prefixes; {timer.Elapsed.TotalSeconds:F2} seconds");
foreach (var row in rows) Console.WriteLine(row);
if (!baseline.SequenceEqual(rows, StringComparer.Ordinal))
    throw new InvalidOperationException("Hole corpus differs from " + baselinePath + ":\n" +
        string.Join('\n', removed.Select(row => "- " + row).Concat(added.Select(row => "+ " + row))) +
        "\nReview the differences, then run HoleCorpus.cs --update.");
Console.WriteLine("PASS hole corpus matches the baseline");

static string Source([CallerFilePath] string path = "") => path;

static MethodHoles Inspect(MethodDefinition method)
{
    if (!method.HasBody) return new(method.FullName, [], []);
    var reachable = Reachability.Analyze(method, FeatureProfile.Scalar);
    var allHomes = new HashSet<int>();
    var liveHomes = new HashSet<int>();
    var prefixes = new List<DeadPrefix>();
    var instructions = method.Body.Instructions;
    for (var pc = 0; pc < instructions.Count; pc++)
    {
        var instruction = instructions[pc];
        var live = reachable.Contains(instruction);
        if (instruction.OpCode.Code is Code.Starg or Code.Starg_S or Code.Ldarga or Code.Ldarga_S)
        {
            var argument = MethodArguments.Index(method, (ParameterDefinition)instruction.Operand);
            allHomes.Add(argument);
            if (live) liveHomes.Add(argument);
        }
        if (!live && instruction.OpCode.OpCodeType == OpCodeType.Prefix)
            prefixes.Add(new(pc, instruction.Offset, instruction.OpCode.Name));
    }
    allHomes.ExceptWith(liveHomes);
    return new(method.FullName, allHomes.Order().ToArray(), prefixes.ToArray());
}

static IEnumerable<string> Rows(MethodHoles result)
{
    if (result.Arguments.Length != 0)
        yield return $"homes\t{result.Method}\t{string.Join(',', result.Arguments)}";
    foreach (var prefix in result.Prefixes)
        yield return $"prefix\t{result.Method}\tpc={prefix.Pc}\tIL_{prefix.Offset:x4}\t{prefix.Opcode}";
}

static void CheckInspection()
{
    using var module = ModuleDefinition.CreateModule("HoleChecks", ModuleKind.Dll);
    var owner = new TypeDefinition("", "Receiver", TypeAttributes.Public, module.TypeSystem.Object);
    module.Types.Add(owner);
    var method = new MethodDefinition("Body", MethodAttributes.Public, module.TypeSystem.Void);
    owner.Methods.Add(method);
    var first = new ParameterDefinition(module.TypeSystem.Int32);
    var second = new ParameterDefinition(module.TypeSystem.Int32);
    method.Parameters.Add(first);
    method.Parameters.Add(second);
    var finish = Instruction.Create(OpCodes.Ret);
    Instruction[] body =
    [
        Instruction.Create(OpCodes.Ldarga_S, first), Instruction.Create(OpCodes.Pop),
        Instruction.Create(OpCodes.Br, finish), Instruction.Create(OpCodes.Ldc_I4_0),
        Instruction.Create(OpCodes.Starg, second), Instruction.Create(OpCodes.Ldc_I4_0),
        Instruction.Create(OpCodes.Starg_S, first), Instruction.Create(OpCodes.Ldnull),
        Instruction.Create(OpCodes.Unaligned, (byte)1), Instruction.Create(OpCodes.Ldind_I4),
        Instruction.Create(OpCodes.Pop), Instruction.Create(OpCodes.Ldnull), Instruction.Create(OpCodes.Ldc_I4_0),
        Instruction.Create(OpCodes.Readonly), Instruction.Create(OpCodes.Ldelema, module.TypeSystem.Int32),
        Instruction.Create(OpCodes.Pop), finish
    ];
    foreach (var instruction in body) method.Body.Instructions.Add(instruction);
    // Decoded instructions have byte offsets independently of their instruction indices.
    using var image = new MemoryStream();
    module.Write(image);
    image.Position = 0;
    using var decoded = ModuleDefinition.ReadModule(image);
    var result = Inspect(decoded.Types.Single(type => type.Name == owner.Name).Methods.Single());
    string[] expected =
    [
        "homes\tSystem.Void Receiver::Body(System.Int32,System.Int32)\t2",
        "prefix\tSystem.Void Receiver::Body(System.Int32,System.Int32)\tpc=8\tIL_0011\tunaligned.",
        "prefix\tSystem.Void Receiver::Body(System.Int32,System.Int32)\tpc=13\tIL_0018\treadonly."
    ];
    if (!Rows(result).SequenceEqual(expected, StringComparer.Ordinal))
        throw new InvalidOperationException("Incorrect argument or prefix position:\n" +
            string.Join('\n', Rows(result)));
}

// A live instruction the decoder refuses blocks its entry at the refusing method's instruction, with its opcode,
// pc and IL offset in the report, while the same instruction dead refuses nothing.
static void CheckRefusalReport()
{
    using var module = ModuleDefinition.CreateModule("RefusalChecks", ModuleKind.Dll);
    var owner = new TypeDefinition("", "Receiver", TypeAttributes.Public, module.TypeSystem.Object);
    module.Types.Add(owner);
    foreach (var name in new[] { "Entry", "Body" })
        owner.Methods.Add(new(name, MethodAttributes.Public | MethodAttributes.Static, module.TypeSystem.Void));
    owner.Methods[0].Body.GetILProcessor().Emit(OpCodes.Ret);
    var il = owner.Methods[1].Body.GetILProcessor();
    il.Emit(OpCodes.Ldc_I4, 5);
    foreach (var opcode in new[] { OpCodes.Pop, OpCodes.Arglist, OpCodes.Pop, OpCodes.Ret }) il.Emit(opcode);
    // Written and read back, so the refused instruction's IL offset differs from its pc.
    using var image = new MemoryStream();
    module.Write(image);
    image.Position = 0;
    using var decoded = ModuleDefinition.ReadModule(image);
    var methods = decoded.Types.Single(type => type.Name == owner.Name).Methods;
    var entry = methods.Single(method => method.Name == "Entry");
    var body = methods.Single(method => method.Name == "Body");
    var instructions = body.Body.Instructions;
    var calls = new ResolvedCallSites();
    var refusal = GenericEvidence.FirstDecodeRefusal(body, instructions.ToHashSet(), calls, null) ??
        throw new InvalidOperationException("The decoder accepted a live arglist.");
    var failure = Blockers.Rejection(entry, new GenericEvidence.UndecodedInstruction(body, refusal));
    var site = Blockers.SiteOf(failure);
    var construct = Blockers.Construct(site.Message);
    if (failure.Method != body || !failure.Chain.SequenceEqual([entry]) ||
        site != site with { Method = body.FullName, IlOffset = 6, Instruction = "IL_0006: arglist", Source = null } ||
        !site.Message.EndsWith($"at pc 2 of {body.FullName}", StringComparison.Ordinal) ||
        construct != "Unsupported instruction: the decoder has no form for arglist")
        throw new InvalidOperationException($"Incorrect decode refusal site {site} in {construct}");
    var live = instructions.Where(instruction => instruction.OpCode != OpCodes.Arglist).ToHashSet();
    if (GenericEvidence.FirstDecodeRefusal(body, live, calls, null) is { } dead)
        throw new InvalidOperationException($"The decoder refused a dead {dead.At}.");
    // The same raw call needs a target from the admitted graph.
    var call = Instruction.Create(OpCodes.Call, entry);
    body.Body.Instructions.Insert(0, call);
    var liveCall = new HashSet<Instruction> { call };
    var unbound = GenericEvidence.FirstDecodeRefusal(body, liveCall, calls, null);
    if (unbound != new GenericEvidence.DecodeRefusal(0, call, GenericEvidence.RefusalKind.UnboundCall) ||
        Blockers.Construct(new GenericEvidence.UndecodedInstruction(body, unbound).Message) !=
            "Unsupported instruction: the decoder cannot bind the call operand with its prefixes")
        throw new InvalidOperationException($"Incorrect call refusal {unbound}");
    calls.Add(call, entry);
    if (GenericEvidence.FirstDecodeRefusal(body, liveCall, calls, null) is { } bound)
        throw new InvalidOperationException($"The decoder refused the bound call: {bound}");
    var models = new ResolvedCallSites();
    models.AddModel(call);
    if (!models.BindsOperand(call, null))
        throw new InvalidOperationException("The decoder refused an ordinary runtime model call.");
    body.Body.Instructions.Insert(0, Instruction.Create(OpCodes.Tail));
    if (!calls.BindsOperand(call, null) || models.BindsOperand(call, null))
        throw new InvalidOperationException("A tail call must enter a managed target.");
}

// The blockers command, run on an assembly whose callee the extractor admits, blocks the entry at the callee's add
// when add is outside the opcodes the decoder reads, and admits it with the decoder's own opcodes. The fixture is a
// copy of the extractor's assembly, which the extractor accepts as a module, with one added type.
static void CheckUndecodedCallee(string template)
{
    var directory = Path.Combine(Path.GetTempPath(), "leancil-undecoded-" + Guid.NewGuid().ToString("N"));
    Directory.CreateDirectory(directory);
    try
    {
        using var assembly = AssemblyDefinition.ReadAssembly(template);
        var module = assembly.MainModule;
        var owner = new TypeDefinition("", "Receiver", TypeAttributes.Public | TypeAttributes.Abstract |
            TypeAttributes.Sealed, module.TypeSystem.Object);
        module.Types.Add(owner);
        MethodDefinition Define(string name)
        {
            var method = new MethodDefinition(name, MethodAttributes.Public | MethodAttributes.Static,
                module.TypeSystem.Int32);
            method.Parameters.Add(new("value", ParameterAttributes.None, module.TypeSystem.Int32));
            owner.Methods.Add(method);
            return method;
        }
        var (entry, body) = (Define("Entry"), Define("Body"));
        var il = body.Body.GetILProcessor();
        foreach (var opcode in new[] { OpCodes.Ldarg_0, OpCodes.Ldc_I4_1, OpCodes.Add, OpCodes.Ret }) il.Emit(opcode);
        il = entry.Body.GetILProcessor();
        il.Emit(OpCodes.Ldarg_0);
        il.Emit(OpCodes.Call, body);
        il.Emit(OpCodes.Ret);
        var path = Path.Combine(directory, "Undecoded.dll");
        assembly.Write(path);
        var manifest = Path.Combine(directory, "manifest.json");
        File.WriteAllText(manifest, """{ "entries": [ { "signature": "Receiver::Entry(int)", "profile": "scalar" } ] }""");
        JsonElement Report(IReadOnlySet<Code> opcodes, string name)
        {
            var output = Path.Combine(directory, name);
            GenericEvidence.ExtractedOpcodes = opcodes;
            try
            {
                if (Blockers.Run([path, "--manifest", manifest, "--output", output]) != 0)
                    throw new InvalidOperationException("The blockers command failed.");
            }
            finally { GenericEvidence.ExtractedOpcodes = GenericEvidence.DecodedOpcodes; }
            return JsonSerializer.Deserialize<JsonElement>(File.ReadAllText(output));
        }
        const string bodyName = "System.Int32 Receiver::Body(System.Int32)";
        const string entryName = "System.Int32 Receiver::Entry(System.Int32)";
        var admitted = Report(GenericEvidence.DecodedOpcodes, "admitted.json").GetProperty("entries")[0];
        if (admitted.GetProperty("status").GetString() != "admitted" ||
            admitted.GetProperty("reachableMethods").GetInt32() != 2)
            throw new InvalidOperationException($"The decodable fixture was not admitted: {admitted}");
        var refused = Report(GenericEvidence.DecodedOpcodes.Where(code => code != Code.Add).ToHashSet(),
            "refused.json");
        var outcome = refused.GetProperty("entries")[0];
        var blocker = refused.GetProperty("blockers").EnumerateArray().Single();
        var site = blocker.GetProperty("sites").EnumerateArray().Single();
        var chains = blocker.GetProperty("entries").EnumerateArray().Single().GetProperty("chains");
        if (outcome.GetProperty("status").GetString() != "blocked" ||
            blocker.GetProperty("construct").GetString() !=
                "Unsupported instruction: the decoder has no form for add" ||
            site.GetProperty("method").GetString() != bodyName || site.GetProperty("ilOffset").GetInt32() != 2 ||
            site.GetProperty("instruction").GetString() != "IL_0002: add" ||
            !site.GetProperty("message").GetString()!.EndsWith($"at pc 2 of {bodyName}", StringComparison.Ordinal) ||
            chains.GetArrayLength() != 1 || chains[0].GetArrayLength() != 1 ||
            chains[0][0].GetString() != entryName)
            throw new InvalidOperationException($"Incorrect undecoded callee report: {refused}");
    }
    finally { Directory.Delete(directory, recursive: true); }
}

sealed record MethodHoles(string Method, int[] Arguments, DeadPrefix[] Prefixes);
sealed record DeadPrefix(int Pc, int Offset, string Opcode);
